//! Present forward-declared functions the way Lua source writes them.
//!
//! A local that is declared `nil` and afterwards only ever receives closures is
//! the forward-declaration idiom:
//!
//! ```lua
//! local mountNode
//! ...
//! mountNode = function(element) ... end
//! ```
//!
//! The lifter sees the declaration's `LOADNIL` as an explicit `= nil`. Both
//! spellings compile to the same instruction, so the bare declaration, which
//! real code uses for 51 of 54 forward declarations in the pinned public and
//! game corpora, is chosen whenever every other write of the local, anywhere in
//! the function tree, is a closure.

use rustc_hash::FxHashMap;

use crate::{Block, LValue, Literal, LocalRw, RValue, RcLocal, Statement, Traverse};

#[derive(Default)]
struct Writes {
    nil_declarations: usize,
    closures: usize,
    other: usize,
}

/// Rewrite `local f = nil` to `local f` for every forward-declared function,
/// and for uncaptured branch-initialized declarations (`local x = nil; if c then x = a else x = b end`).
pub fn bare_forward_declarations(block: &mut Block) {
    // Candidates are locals that a later statement assigns a closure (rare);
    // only their writes are counted.
    let mut writes = FxHashMap::default();
    visit_statements(block, &mut |statement| {
        if let Statement::Assign(assign) = statement
            && !assign.prefix
            && assign.left.len() == assign.right.len()
        {
            for (left, right) in assign.left.iter().zip(&assign.right) {
                if let (LValue::Local(local), RValue::Closure(_)) = (left, right) {
                    writes.entry(local.clone()).or_insert_with(Writes::default);
                }
            }
        }
    });
    if !writes.is_empty() {
        visit_statements(block, &mut |statement| census_statement(statement, &mut writes));
    }
    rewrite_block(block, &writes);
}

fn is_forward_function(writes: &Writes) -> bool {
    writes.nil_declarations == 1 && writes.closures != 0 && writes.other == 0
}

/// Every statement of the function tree, including nested closures.
fn visit_statements(block: &Block, visit: &mut impl FnMut(&Statement)) {
    for statement in &block.0 {
        visit(statement);
        let mut functions = Vec::new();
        crate::inline_temps::collect_closures_in_statement(statement, &mut |closure| {
            functions.push(closure.function.clone());
        });
        for function in functions {
            visit_statements(&function.lock().body, visit);
        }
        for_each_child_block(statement, &mut |block| visit_statements(block, visit));
    }
}

fn census_statement(statement: &Statement, writes: &mut FxHashMap<RcLocal, Writes>) {
    if let Statement::Assign(assign) = statement {
        let aligned = assign.left.len() == assign.right.len();
        for (index, left) in assign.left.iter().enumerate() {
            let LValue::Local(local) = left else { continue };
            let Some(entry) = writes.get_mut(local) else { continue };
            match aligned.then(|| &assign.right[index]) {
                Some(RValue::Closure(_)) => entry.closures += 1,
                Some(RValue::Literal(Literal::Nil)) if assign.prefix && assign.left.len() == 1 => {
                    entry.nil_declarations += 1
                }
                _ => entry.other += 1,
            }
        }
    } else {
        statement.visit_local_writes(&mut |local| {
            if let Some(entry) = writes.get_mut(local) {
                entry.other += 1;
            }
            true
        });
    }
}

fn block_writes_before_read(block: &Block, local: &RcLocal) -> bool {
    for stmt in &block.0 {
        match stmt {
            Statement::Empty(_) | Statement::Comment(_) => continue,
            Statement::Assign(assign) if assign.prefix => {
                if assign.right.iter().any(|r| rvalue_reads_or_captures(r, local)) {
                    return false;
                }
                continue;
            }
            Statement::Assign(assign) if !assign.prefix && !assign.compound => {
                // Any read in RHS or index targets happens before the write.
                if assign.right.iter().any(|r| rvalue_reads_or_captures(r, local)) {
                    return false;
                }
                if assign.left.iter().any(|l| match l {
                    LValue::Index(index) => index.any_local_read(&mut |read| read == local),
                    _ => false,
                }) {
                    return false;
                }
                if assign.left.iter().any(|l| matches!(l, LValue::Local(t) if t == local)) {
                    return true;
                }
                return false;
            }
            Statement::If(branch) => {
                if rvalue_reads_or_captures(&branch.condition, local) {
                    return false;
                }
                let then_block = branch.then_block.lock();
                let else_block = branch.else_block.lock();
                return !else_block.0.is_empty()
                    && block_writes_before_read(&then_block, local)
                    && block_writes_before_read(&else_block, local);
            }
            _ => return false,
        }
    }
    false
}

fn rvalue_captures_local(value: &RValue, local: &RcLocal) -> bool {
    let mut captured = false;
    fn walk(value: &RValue, local: &RcLocal, captured: &mut bool) {
        if *captured {
            return;
        }
        if let RValue::Closure(closure) = value {
            for upvalue in &closure.upvalues {
                let (crate::Upvalue::Copy(up) | crate::Upvalue::Ref(up)) = upvalue;
                if up == local {
                    *captured = true;
                    return;
                }
            }
        }
        value.visit_rvalues(&mut |child| {
            walk(child, local, captured);
            !*captured
        });
    }
    walk(value, local, &mut captured);
    captured
}

fn rvalue_reads_local_outside_closures(value: &RValue, local: &RcLocal) -> bool {
    let mut found = false;
    fn walk(value: &RValue, local: &RcLocal, found: &mut bool) {
        if *found {
            return;
        }
        match value {
            RValue::Local(read) if read == local => {
                *found = true;
                return;
            }
            RValue::Closure(_) => return,
            _ => {}
        }
        value.visit_rvalues(&mut |child| {
            walk(child, local, found);
            !*found
        });
    }
    walk(value, local, &mut found);
    found
}

fn rvalue_reads_or_captures(value: &RValue, local: &RcLocal) -> bool {
    value.any_local_read(&mut |read| read == local) || rvalue_captures_local(value, local)
}

fn statement_touches_local(statement: &Statement, local: &RcLocal) -> bool {
    let mut touched = false;
    statement.visit_local_reads(&mut |read| {
        if read == local {
            touched = true;
        }
        !touched
    });
    if touched {
        return true;
    }
    statement.visit_local_writes(&mut |written| {
        if written == local {
            touched = true;
        }
        !touched
    });
    if touched {
        return true;
    }
    let mut captured = false;
    statement.visit_rvalues(&mut |value| {
        if rvalue_captures_local(value, local) {
            captured = true;
        }
        !captured
    });
    captured
}

fn rewrite_block(block: &mut Block, writes: &FxHashMap<RcLocal, Writes>) {
    for index in 0..block.0.len() {
        let strip_nil = if let Statement::Assign(assign) = &block.0[index]
            && assign.prefix
            && assign.left.len() == 1
            && matches!(assign.right.as_slice(), [RValue::Literal(Literal::Nil)])
            && let LValue::Local(local) = &assign.left[0]
        {
            if writes.get(local).is_some_and(is_forward_function) {
                true
            } else if writes.get(local).is_none() {
                // Pattern A: `local conn = nil; conn = sig:Connect(function() conn:Disconnect() end)`
                // Pattern B: `local x = nil; [unrelated stmts]; if cond then ... x = ... else ... x = ... end`
                let mut found = false;
                for next in &block.0[index + 1..] {
                    match next {
                        Statement::Empty(_) | Statement::Comment(_) => continue,
                        Statement::Assign(next_assign)
                            if !next_assign.prefix
                                && !next_assign.compound
                                && next_assign.left.len() == 1
                                && next_assign.right.len() == 1
                                && matches!(&next_assign.left[0], LValue::Local(t) if t == local) =>
                        {
                            let rhs = &next_assign.right[0];
                            if !rvalue_reads_local_outside_closures(rhs, local)
                                && rvalue_captures_local(rhs, local)
                            {
                                found = true;
                            }
                            break;
                        }
                        Statement::If(branch) => {
                            if !rvalue_reads_or_captures(&branch.condition, local) {
                                let then_block = branch.then_block.lock();
                                let else_block = branch.else_block.lock();
                                if !else_block.0.is_empty()
                                    && block_writes_before_read(&then_block, local)
                                    && block_writes_before_read(&else_block, local)
                                {
                                    found = true;
                                }
                            }
                            break;
                        }
                        other if !statement_touches_local(other, local) => continue,
                        _ => break,
                    }
                }
                found
            } else {
                false
            }
        } else {
            false
        };
        if strip_nil && let Statement::Assign(assign) = &mut block.0[index] {
            assign.right.clear();
        }
        let statement = &mut block.0[index];
        let mut functions = Vec::new();
        crate::inline_temps::collect_closures_in_statement(statement, &mut |closure| {
            functions.push(closure.function.clone());
        });
        for function in functions {
            rewrite_block(&mut function.lock().body, writes);
        }
        for_each_child_block(statement, &mut |block| rewrite_block(block, writes));
    }
}

fn for_each_child_block(statement: &Statement, f: &mut impl FnMut(&mut Block)) {
    match statement {
        Statement::If(r#if) => {
            f(&mut r#if.then_block.lock());
            f(&mut r#if.else_block.lock());
        }
        Statement::While(r#while) => f(&mut r#while.block.lock()),
        Statement::Repeat(repeat) => f(&mut repeat.block.lock()),
        Statement::NumericFor(numeric_for) => f(&mut numeric_for.block.lock()),
        Statement::GenericFor(generic_for) => f(&mut generic_for.block.lock()),
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::bare_forward_declarations;
    use crate::{Assign, Block, Closure, Function, LValue, Literal, Local, RValue, RcLocal};
    use by_address::ByAddress;
    use parking_lot::Mutex;
    use triomphe::Arc;

    fn local(name: &str) -> RcLocal {
        RcLocal::new(Local::new(Some(name.to_string())))
    }

    fn closure() -> RValue {
        RValue::Closure(Closure {
            node_origin: Default::default(),
            function: ByAddress(Arc::new(Mutex::new(Function::default()))),
            upvalues: vec![],
        })
    }

    fn declare_nil(local: &RcLocal) -> crate::Statement {
        let mut assign = Assign::new(vec![LValue::Local(local.clone())], vec![Literal::Nil.into()]);
        assign.prefix = true;
        assign.into()
    }

    #[test]
    fn forward_declared_function_uses_the_lua_idiom() {
        let mount = local("mount");
        let call = || crate::Call::new(crate::Global::from("prepare").into(), vec![]).into();
        let mut block = Block(vec![
            declare_nil(&mount),
            call(),
            Assign::new(vec![LValue::Local(mount.clone())], vec![closure()]).into(),
        ]);
        bare_forward_declarations(&mut block);
        let text = block.to_string();
        assert!(text.starts_with("local mount\n"), "{text}");
        assert!(!text.contains("= nil"), "{text}");
        // Right after its declaration, the assignment is `local function`.
        let mut block = Block(vec![
            declare_nil(&mount),
            Assign::new(vec![LValue::Local(mount.clone())], vec![closure()]).into(),
        ]);
        bare_forward_declarations(&mut block);
        let text = block.to_string();
        assert!(text.starts_with("local function mount()"), "{text}");
    }

    #[test]
    fn a_nil_local_with_other_writes_keeps_its_initializer() {
        let state = local("state");
        let mut block = Block(vec![
            declare_nil(&state),
            Assign::new(vec![LValue::Local(state.clone())], vec![closure()]).into(),
            Assign::new(vec![LValue::Local(state.clone())], vec![Literal::Boolean(true).into()]).into(),
        ]);
        bare_forward_declarations(&mut block);
        assert!(block.to_string().starts_with("local state = nil\n"));
    }

    #[test]
    fn self_capturing_connection_forward_decl_drops_nil() {
        let conn = local("connection");
        let callback = RValue::Closure(Closure {
            node_origin: Default::default(),
            function: ByAddress(Arc::new(Mutex::new(crate::Function::default()))),
            upvalues: vec![crate::Upvalue::Ref(conn.clone())],
        });
        let connect = crate::MethodCall::new(
            RValue::Global(crate::Global::from("sig")),
            "Connect".into(),
            vec![callback],
        )
        .into();
        let mut block = Block(vec![
            declare_nil(&conn),
            Assign::new(vec![LValue::Local(conn.clone())], vec![connect]).into(),
        ]);
        bare_forward_declarations(&mut block);
        let text = block.to_string();
        assert!(text.starts_with("local connection\n"), "{text}");
        assert!(!text.contains("= nil"), "{text}");
    }

    #[test]
    fn branch_initialized_local_with_arm_temp_drops_nil() {
        let out = local("result");
        let tmp = local("tmp");
        let mut tmp_decl = Assign::new(vec![LValue::Local(tmp.clone())], vec![Literal::Number(1.0).into()]);
        tmp_decl.prefix = true;
        let branch = crate::If::new(
            RValue::Global(crate::Global::from("cond")),
            Block(vec![
                tmp_decl.into(),
                Assign::new(vec![LValue::Local(out.clone())], vec![RValue::Local(tmp)]).into(),
            ]),
            Block(vec![
                Assign::new(vec![LValue::Local(out.clone())], vec![Literal::Number(2.0).into()]).into(),
            ]),
        );
        let mut block = Block(vec![declare_nil(&out), branch.into()]);
        bare_forward_declarations(&mut block);
        let text = block.to_string();
        assert!(text.starts_with("local result\n"), "{text}");
        assert!(!text.contains("= nil"), "{text}");
    }
}
