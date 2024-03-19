use std::{collections::HashMap, rc::Rc};

use im_rc::vector;
use slog::info;

use crate::{exec::{constants, find_entry_for_static_invocation, Thread}, stack::{Stack, StackFrame}, typeable::runtime_to_nonvoidtype, Declaration, Expression, Identifier, Invocation, Method, Parameter, RuntimeType};

use super::{eval::evaluate, invocation::InvocationContext, Engine, State};

fn evaluated_arguments(
    invocation: &Invocation,
    state: &mut State,
    en: &mut impl Engine,
) -> Vec<Rc<Expression>> {
    invocation
        .arguments()
        .iter()
        .map(|arg| evaluate(state, arg.clone(), en))
        .collect::<Vec<_>>()
}

pub(super) fn fork_invocation(
    state: &mut State,
    context: InvocationContext,
    resolved: &(Declaration, Rc<Method>),
    en: &mut impl Engine,
) {
    info!(state.logger, "Single method invocation");

    let (declaration, resolved_method) = resolved;
    let class_name = declaration.name();

    let params = if !resolved_method.is_static { 
        non_static_method_params(
            state, 
            context.clone(), 
            resolved_method, 
            class_name, 
            en
        )
    } else {
        let arguments: Vec<Rc<Expression>> = evaluated_arguments(context.invocation, state, en);
        resolved_method.params.iter().zip(arguments.iter().cloned())
            .map(|(p, e)| (p.name.clone(), evaluate(state, e, en)))
            .collect()
    };

    let next_entry = find_entry_for_static_invocation(
        class_name,
        context.invocation.identifier(),
        context.invocation.argument_types(),
        context.program,
        en.symbol_table(),
    ); 

    let tid = state.thread_counter.next_id();
    let thread: Thread = Thread {
        tid,
        pc: next_entry,
        stack: Stack::new(vector![StackFrame {
            return_pc: next_entry,
            returning_lhs: None,
            params,
            current_member: resolved_method.clone(),
        }])
    };
    state.threads.insert(tid, thread);
}

fn non_static_method_params(
    state: &mut State,
    context: InvocationContext,
    resolved_method: &Rc<Method>,
    class_name: &Identifier,
    en: &mut impl Engine
) -> HashMap<Identifier, Rc<Expression>> {
    let arguments: Vec<Rc<Expression>> = evaluated_arguments(context.invocation, state, en);

    let invocation_lhs = match context.invocation {
        Invocation::InvokeMethod { lhs, .. } => lhs,
        _ => panic!("expected invoke Method"),
    };

    let this: (RuntimeType, Identifier) = (
        RuntimeType::ReferenceRuntimeType {
            type_: class_name.clone(),
        },
        invocation_lhs.to_owned().into(),
    );

    let this_param = Parameter::new(
        runtime_to_nonvoidtype(this.0.clone()).expect("concrete, nonvoid type"),
        constants::this_str(),
    );

    let this_expr = Expression::Var {
        var: this.1.clone(),
        type_: this.0,
        info: resolved_method.info,
    };
    let parameters = std::iter::once(&this_param).chain(resolved_method.params.iter());
    let arguments = std::iter::once(Rc::new(this_expr)).chain(arguments.iter().cloned());

    parameters.zip(arguments)
        .map(|(p, e)| (p.name.clone(), evaluate(state, e, en)))
        .collect()
}