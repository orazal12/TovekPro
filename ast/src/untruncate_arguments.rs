//! A call's last argument keeps all of its values unless parenthesized:
//! `f(g())` passes every result of `g`, `f((g()))` only the first. Where
//! the callee drops the extra values anyway, the parentheses say nothing:
//! `emit((x:FindFirstChild("Beams")))` reads as `emit(x:FindFirstChild("Beams"))`.
//! Nor does the adjustment, so a `("...%*"):format(x)` there is adjusted
//! instead, and prints as the backtick string `` emit(`...{x}`) ``: in a
//! spreading position it keeps `:format`, as a hooked `string.format` may
//! return more than one value.
//!
//! A callee drops them when the argument sits at or after its last
//! parameter and it takes no `...`: a local function declared once. A call
//! returning nothing then leaves that parameter `nil`, which such a function
//! cannot tell from an explicit `nil`. A library function can: `tostring()`
//! raises "missing argument" where `tostring(nil)` is `"nil"`, so its
//! parentheses stay.
//!
//! A call giving exactly one value reads the same without the parentheses
//! adjusting it to one, wherever it is: `print((tostring(x)))` is
//! `print(tostring(x))`: a local function declared once each path of which
//! returns one value that is not a call's. A builtin may be replaced at run
//! time by one giving more values, which its fast call's fallback still
//! adjusts to one where the source wrote `(math.max(a, b))`, so a builtin
//! of one result it fast-called drops them only assuming the standard
//! libraries.
//!
//! An equivalent call a de-inliner inferred ends in no `nil` after another
//! argument: its copy cannot tell a `nil` passed from one left out, and the
//! source most often leaves those out (`getCutscene("House")`, not
//! `getCutscene("House", nil, nil)`). A lone `nil` is most often written
//! (`purchase(nil)`), and stays.
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{Block, Call, LValue, RValue, RcLocal, Select, Statement, Traverse};

pub fn untruncate_arguments(body: &mut Block, standard_libraries: bool) {
    let mut writes = FxHashMap::default();
    crate::expr_deinline::collect_write_counts(&body.0, &mut writes);
    let mut parameters = FxHashMap::default();
    let mut one_valued = FxHashSet::default();
    let error_trusted = standard_libraries && !local_or_global_shadows_error(&body.0);
    let mut forward_nil_decls = FxHashSet::default();
    collect_forward_nil_decls(&body.0, &mut forward_nil_decls);
    local_functions(
        &body.0,
        &writes,
        &forward_nil_decls,
        error_trusted,
        &mut parameters,
        &mut one_valued,
    );
    let arity = |callee: &RValue| match callee {
        RValue::Local(local) => parameters.get(local).copied(),
        _ => None,
    };
    let one = |call: &Call| {
        (standard_libraries && !call.group_callee && call.builtin_fastcall.is_some_and(|(builtin, _)| one_result_builtin(builtin)))
            || matches!(call.value.as_ref(), RValue::Local(local) if one_valued.contains(local))
    };
    block(&mut body.0, &arity, &one);
}

fn local_or_global_shadows_error(stmts: &[Statement]) -> bool {
    let is_error_local = |local: &RcLocal| local.0 .0.lock().0.as_deref() == Some("error");
    for statement in stmts {
        match statement {
            Statement::Assign(assign) => {
                for target in &assign.left {
                    match target {
                        LValue::Local(local) if is_error_local(local) => return true,
                        LValue::Global(global) if global.0.as_slice() == b"error" => return true,
                        _ => {}
                    }
                }
            }
            Statement::NumericFor(numeric_for) => {
                if is_error_local(&numeric_for.counter) {
                    return true;
                }
            }
            Statement::GenericFor(generic_for) => {
                if generic_for.res_locals.iter().any(&is_error_local) {
                    return true;
                }
            }
            _ => {}
        }
        let mut found = false;
        for_each_block(statement, &mut |nested| {
            found |= local_or_global_shadows_error(nested);
        });
        if found {
            return true;
        }
        crate::deinline::visit_stmt_rvalues(statement, &mut |value| {
            closures_with_fn(value, &mut |function| {
                if function.parameters.iter().any(&is_error_local)
                    || local_or_global_shadows_error(&function.body.0)
                {
                    found = true;
                }
            });
            !found
        });
        if found {
            return true;
        }
    }
    false
}

fn closures_with_fn(value: &RValue, f: &mut impl FnMut(&crate::Function)) {
    if let RValue::Closure(closure) = value {
        f(&closure.function.lock());
    }
    value.visit_rvalues(&mut |child| {
        closures_with_fn(child, f);
        true
    });
}

fn collect_forward_nil_decls(stmts: &[Statement], out: &mut FxHashSet<RcLocal>) {
    for statement in stmts {
        if let Statement::Assign(assign) = statement
            && assign.prefix
            && let [LValue::Local(local)] = assign.left.as_slice()
            && (assign.right.is_empty()
                || matches!(assign.right.as_slice(), [RValue::Literal(crate::Literal::Nil)]))
        {
            out.insert(local.clone());
        }
        for_each_block(statement, &mut |nested| collect_forward_nil_decls(nested, out));
        crate::deinline::visit_stmt_rvalues(statement, &mut |value| {
            closures(value, &mut |body| collect_forward_nil_decls(&body.0, out));
            true
        });
    }
}

/// Returns true if every non-diverging path through `stmts` ends in a
/// 1-value `return`, treating tail `error(...)` calls as diverging when
/// `error_trusted` (`--assume-standard-libraries` with unshadowed `error`).
fn returns_exactly_one_with_error(stmts: &[Statement], error_trusted: bool) -> bool {
    if crate::deinline::returns_exactly_one(stmts) {
        return true;
    }
    if !error_trusted {
        return false;
    }
    fn all_returns_one(stmts: &[Statement]) -> bool {
        for stmt in stmts {
            match stmt {
                Statement::Return(ret) => {
                    if ret.values.len() != 1
                        || matches!(
                            ret.values.first(),
                            Some(RValue::Call(_) | RValue::MethodCall(_) | RValue::VarArg(_))
                        )
                    {
                        return false;
                    }
                }
                Statement::If(r#if) => {
                    if !all_returns_one(&r#if.then_block.lock().0)
                        || !all_returns_one(&r#if.else_block.lock().0)
                    {
                        return false;
                    }
                }
                Statement::While(w) => {
                    if !all_returns_one(&w.block.lock().0) {
                        return false;
                    }
                }
                Statement::Repeat(r) => {
                    if !all_returns_one(&r.block.lock().0) {
                        return false;
                    }
                }
                Statement::NumericFor(f) => {
                    if !all_returns_one(&f.block.lock().0) {
                        return false;
                    }
                }
                Statement::GenericFor(f) => {
                    if !all_returns_one(&f.block.lock().0) {
                        return false;
                    }
                }
                _ => {}
            }
        }
        true
    }
    fn always_returns_or_errors(stmts: &[Statement]) -> bool {
        let Some(last) = stmts
            .iter()
            .rev()
            .find(|s| !matches!(s, Statement::Empty(_) | Statement::Comment(_)))
        else {
            return false;
        };
        match last {
            Statement::Return(_) => true,
            Statement::Call(call) => matches!(call.value.as_ref(), RValue::Global(g) if g.0.as_slice() == b"error"),
            Statement::If(r#if) => {
                always_returns_or_errors(&r#if.then_block.lock().0)
                    && always_returns_or_errors(&r#if.else_block.lock().0)
            }
            _ => false,
        }
    }
    all_returns_one(stmts) && always_returns_or_errors(stmts)
}

/// Luau's builtins (`LuauBuiltinFunction`) returning one value
/// (`getBuiltinInfo(id).results == 1`): every id up to `bit32.byteswap`'s
/// but none, `assert`, `math.frexp`/`modf`, `string.byte`, `table.insert`/
/// `unpack`, `select(n, ...)` and the buffer writes.
fn one_result_builtin(id: u8) -> bool {
    id <= 131 && !matches!(id, 0 | 1 | 14 | 20 | 41 | 52 | 53 | 57 | 67 | 70 | 73 | 75 | 77)
}

/// The parameter count of every non-variadic local function whose binder
/// is written only by its declaration (or bare forward declaration + closure),
/// and those of them each non-diverging path of which returns exactly one value.
fn local_functions(
    stmts: &[Statement],
    writes: &FxHashMap<RcLocal, usize>,
    forward_nil_decls: &FxHashSet<RcLocal>,
    error_trusted: bool,
    out: &mut FxHashMap<RcLocal, usize>,
    one_valued: &mut FxHashSet<RcLocal>,
) {
    for statement in stmts {
        if let Statement::Assign(assign) = statement
            && let [LValue::Local(local)] = assign.left.as_slice()
            && let [RValue::Closure(closure)] = assign.right.as_slice()
            && ((assign.prefix && writes.get(local) == Some(&1))
                || (!assign.prefix
                    && writes.get(local) == Some(&2)
                    && forward_nil_decls.contains(local)))
        {
            let function = closure.function.0.lock();
            if !function.is_variadic {
                out.insert(local.clone(), function.parameters.len());
            }
            if returns_exactly_one_with_error(&function.body.0, error_trusted) {
                one_valued.insert(local.clone());
            }
        }
        for_each_block(statement, &mut |nested| {
            local_functions(nested, writes, forward_nil_decls, error_trusted, out, one_valued)
        });
        crate::deinline::visit_stmt_rvalues(statement, &mut |value| {
            closures(value, &mut |body| {
                local_functions(&body.0, writes, forward_nil_decls, error_trusted, out, one_valued)
            });
            true
        });
    }
}

fn block(stmts: &mut [Statement], arity: &impl Fn(&RValue) -> Option<usize>, one: &impl Fn(&Call) -> bool) {
    for statement in stmts {
        match statement {
            Statement::Call(call) => {
                one_valued_last(&mut call.arguments, one);
                untruncate(call, arity);
            }
            Statement::MethodCall(call) => one_valued_last(&mut call.arguments, one),
            Statement::Return(ret) => one_valued_last(&mut ret.values, one),
            Statement::Assign(assign) if assign.left.len() > assign.right.len() => one_valued_last(&mut assign.right, one),
            _ => {}
        }
        statement.traverse_rvalues(&mut |value| match value {
            RValue::Call(call) | RValue::Select(Select::Call(call)) => {
                one_valued_last(&mut call.arguments, one);
                untruncate(call, arity);
            }
            RValue::MethodCall(call) | RValue::Select(Select::MethodCall(call)) => one_valued_last(&mut call.arguments, one),
            RValue::Table(table) => {
                if let Some((None, last)) = table.0.last_mut() {
                    one_valued_last(std::slice::from_mut(last), one);
                }
            }
            RValue::Closure(closure) => block(&mut closure.function.0.lock().body.0, arity, one),
            _ => {}
        });
        for_each_block_mut(statement, &mut |nested| block(nested, arity, one));
    }
}

/// The last of `values`, where all of a call's results spread, without the
/// parentheses adjusting it to one where it gives exactly one.
fn one_valued_last(values: &mut [RValue], one: &impl Fn(&Call) -> bool) {
    if let Some(last) = values.last_mut()
        && let RValue::Select(Select::Call(call)) = last
        && one(call)
    {
        call.one_result = true;
        *last = crate::untruncated(std::mem::replace(last, RValue::Literal(crate::Literal::Nil)));
    }
}

fn untruncate(call: &mut crate::Call, arity: &impl Fn(&RValue) -> Option<usize>) {
    // A call or `...` left last would spread into the parameters the `nil`s fill.
    while call.is_inferred()
        && arity(&call.value).is_some()
        && call.arguments.len() > 1
        && matches!(call.arguments.last(), Some(RValue::Literal(crate::Literal::Nil)))
        && !matches!(call.arguments.iter().rev().nth(1), Some(RValue::Call(_) | RValue::MethodCall(_) | RValue::VarArg(_)))
    {
        call.arguments.pop();
    }
    let Some(last) = call.arguments.len().checked_sub(1) else { return };
    let argument = &call.arguments[last];
    // Only parentheses that print are dropped; a format call that prints as
    // a backtick string is the one form adjusted.
    let interpolates = matches!(argument, RValue::MethodCall(format) if crate::formatter::prints_as_interpolation(format));
    if !(interpolates || crate::formatter::needs_truncation_parens(argument))
        || !arity(&call.value).is_some_and(|parameters| last + 1 >= parameters)
    {
        return;
    }
    let value = std::mem::replace(&mut call.arguments[last], RValue::Literal(crate::Literal::Nil));
    call.arguments[last] = match value {
        RValue::MethodCall(format) if interpolates => RValue::Select(Select::MethodCall(format)),
        value => crate::untruncated(value),
    };
}

fn for_each_block(statement: &Statement, visit: &mut impl FnMut(&Block)) {
    match statement {
        Statement::If(branch) => {
            visit(&branch.then_block.lock());
            visit(&branch.else_block.lock());
        }
        Statement::While(node) => visit(&node.block.lock()),
        Statement::Repeat(node) => visit(&node.block.lock()),
        Statement::NumericFor(node) => visit(&node.block.lock()),
        Statement::GenericFor(node) => visit(&node.block.lock()),
        _ => {}
    }
}

fn for_each_block_mut(statement: &mut Statement, visit: &mut impl FnMut(&mut [Statement])) {
    match statement {
        Statement::If(branch) => {
            visit(&mut branch.then_block.lock().0);
            visit(&mut branch.else_block.lock().0);
        }
        Statement::While(node) => visit(&mut node.block.lock().0),
        Statement::Repeat(node) => visit(&mut node.block.lock().0),
        Statement::NumericFor(node) => visit(&mut node.block.lock().0),
        Statement::GenericFor(node) => visit(&mut node.block.lock().0),
        _ => {}
    }
}

fn closures(value: &RValue, visit: &mut impl FnMut(&Block)) {
    if let RValue::Closure(closure) = value {
        visit(&closure.function.0.lock().body);
        return;
    }
    value.visit_rvalues(&mut |child| {
        closures(child, visit);
        true
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Assign, Call, Closure, Function, Global, Index, Literal, Local};
    use by_address::ByAddress;
    use parking_lot::Mutex;
    use triomphe::Arc;

    fn local(name: &str) -> RcLocal {
        RcLocal::new(Local::new(Some(name.to_string())))
    }

    fn global(name: &str) -> RValue {
        RValue::Global(Global::from(name))
    }

    fn field(library: &str, name: &str) -> RValue {
        Index::new(global(library), RValue::Literal(Literal::String(name.as_bytes().to_vec()))).into()
    }

    fn one_result() -> RValue {
        RValue::Select(Select::Call(Call::new(global("g"), Vec::new())))
    }

    fn function(name: &RcLocal, parameters: usize, is_variadic: bool) -> Statement {
        let function = Function {
            parameters: (0..parameters).map(|i| local(&format!("p{i}"))).collect(),
            is_variadic,
            ..Function::default()
        };
        let closure = Closure {
            node_origin: Default::default(),
            function: ByAddress(Arc::new(Mutex::new(function))),
            upvalues: Vec::new(),
        };
        Assign::new(vec![LValue::Local(name.clone())], vec![RValue::Closure(closure)]).into()
    }

    fn declare(statement: Statement) -> Statement {
        let Statement::Assign(mut assign) = statement else { unreachable!() };
        assign.prefix = true;
        assign.into()
    }

    fn call(callee: RValue, mut arguments: Vec<RValue>) -> Statement {
        arguments.push(one_result());
        Call::new(callee, arguments).into()
    }

    fn run(mut statements: Vec<Statement>) -> String {
        let mut block = Block(std::mem::take(&mut statements));
        untruncate_arguments(&mut block, false);
        block.to_string()
    }

    #[test]
    fn parentheses_go_where_the_callee_drops_extra_values() {
        let emit = local("emit");
        let pair = local("pair");
        let rest = local("rest");
        let output = run(vec![
            declare(function(&emit, 1, false)),
            declare(function(&pair, 2, false)),
            declare(function(&rest, 1, true)),
            call(RValue::Local(emit.clone()), Vec::new()),
            call(RValue::Local(pair.clone()), Vec::new()),
            call(RValue::Local(pair.clone()), vec![global("a")]),
            call(RValue::Local(rest.clone()), Vec::new()),
            call(global("type"), Vec::new()),
            call(field("math", "abs"), Vec::new()),
            call(global("tonumber"), Vec::new()),
            call(field("math", "random"), vec![global("a")]),
            call(field("math", "max"), vec![global("a")]),
        ]);
        let calls: Vec<&str> = output.lines().filter(|line| line.contains("g()")).collect();
        assert_eq!(
            calls,
            [
                "emit(g())",
                "pair((g()))",
                "pair(a, g())",
                "rest((g()))",
                // A library function counts its arguments: `type()` raises
                // where `type(nil)` is `"nil"`.
                "type((g()))",
                "math.abs((g()))",
                "tonumber((g()))",
                "math.random(a, (g()))",
                "math.max(a, (g()))",
            ],
            "{output}"
        );
    }

    #[test]
    fn an_inferred_call_leaves_trailing_nils_out() {
        let show = local("show");
        let nil = || RValue::Literal(Literal::Nil);
        let inferred = |arguments: Vec<RValue>| -> Statement {
            Call::new(RValue::Local(show.clone()), arguments).reconstructed(crate::call_origins::Kind::StatementDeinline).into()
        };
        let output = run(vec![
            declare(function(&show, 3, false)),
            inferred(vec![global("a"), nil(), nil()]),
            inferred(vec![nil(), global("b"), nil()]),
            inferred(vec![nil(), nil()]),
            // `g()` left last would fill the parameters the `nil` fills.
            inferred(vec![global("a"), Call::new(global("g"), Vec::new()).into(), nil()]),
            // A call the bytecode makes passes its `nil`.
            Call::new(RValue::Local(show.clone()), vec![global("a"), nil()]).into(),
        ]);
        let calls: Vec<&str> = output.lines().filter(|line| line.starts_with("show(")).collect();
        assert_eq!(
            calls,
            [
                "show(a) -- inferred equivalent call",
                "show(nil, b) -- inferred equivalent call",
                "show(nil) -- inferred equivalent call",
                "show(a, g(), nil) -- inferred equivalent call",
                "show(a, nil)"
            ],
            "{output}"
        );
    }

    #[test]
    fn parentheses_stay_where_the_callee_may_be_replaced() {
        let emit = local("emit");
        let output = run(vec![
            declare(function(&emit, 1, false)),
            // `emit` is written again: the call may reach another function.
            function(&emit, 3, false),
            call(RValue::Local(emit.clone()), Vec::new()),
            // The script assigns `type`.
            Assign::new(vec![LValue::Global(Global::from("type"))], vec![global("print")]).into(),
            call(global("type"), Vec::new()),
        ]);
        assert!(output.contains("emit((g()))"), "{output}");
        assert!(output.contains("type((g()))"), "{output}");
    }

    /// A `%*` format call passed where the callee drops the rest prints as a
    /// backtick string; elsewhere it spreads and keeps `:format`.
    #[test]
    fn a_format_call_the_callee_truncates_prints_as_a_backtick_string() {
        let emit = local("emit");
        let format = || -> RValue {
            crate::MethodCall::new(RValue::Literal(Literal::String(b"id %*".to_vec())), "format".into(), vec![global("x")]).into()
        };
        let output = run(vec![
            declare(function(&emit, 1, false)),
            Call::new(RValue::Local(emit.clone()), vec![format()]).into(),
            Call::new(global("print"), vec![format()]).into(),
        ]);
        assert!(output.contains("emit(`id {x}`)"), "{output}");
        assert!(output.contains("print((\"id %*\"):format(x))"), "{output}");
    }

    #[test]
    fn shadowed_error_parameter_blocks_diverging_error_assumption() {
        let err_param = local("error");
        let mut inner = Function::default();
        inner.parameters = vec![err_param.clone()];
        inner.body = Block(vec![Call::new(RValue::Local(err_param), vec![Literal::String(b"x".to_vec()).into()]).into()]);
        let closure = RValue::Closure(Closure {
            node_origin: Default::default(),
            function: ByAddress(Arc::new(Mutex::new(inner))),
            upvalues: vec![],
        });
        let stmts = vec![Assign::new(vec![LValue::Local(local("f"))], vec![closure]).into()];
        assert!(super::local_or_global_shadows_error(&stmts));
    }
}
