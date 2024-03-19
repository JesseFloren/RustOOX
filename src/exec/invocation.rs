//! This module contains functions and types related to function calls in OOX.
//!
use std::{collections::HashMap, rc::Rc};

use itertools::Itertools;
use slog::{debug, info};

use crate::{
    cfg::CFGStatement,
    stack::StackFrame,
    syntax::{Declaration, Expression, Identifier, Invocation, Lhs, Method, RuntimeType},
    typeable::{runtime_to_nonvoidtype, Typeable},
    utils, Parameter,
};

use super::{
    constants,
    eval::evaluate,
    find_entry_for_static_invocation,
    heap::HeapValue,
    remove_symbolic_null,
    state_split::{self, split_states_with_aliases},
    ActionResult, Engine, State,
};

/// A struct to pass around context types of invocation more easily.
#[derive(Clone)]
pub(super) struct InvocationContext<'a> {
    pub(super) lhs: Option<Lhs>,
    pub(super) return_point: u64,
    pub(super) invocation: &'a Invocation,
    pub(super) program: &'a HashMap<u64, CFGStatement>,
}

/// A static method, or a method that is not overriden anywhere (non-polymorphic)
/// This means that there is only one method that can be called
/// Returns the next function entry CFG
pub(super) fn single_method_invocation(
    state: &mut State,
    context: InvocationContext,
    resolved: &(Declaration, Rc<Method>),
    en: &mut impl Engine,
) -> u64 {
    info!(state.logger, "Single method invocation");
    let (declaration, resolved_method) = resolved;
    let class_name = &declaration.name();

    if resolved_method.is_static {
        // evaluate arguments
        let arguments = evaluated_arguments(context.invocation, state, en);

        exec_static_method_entry(
            state,
            context.return_point,
            resolved_method.clone(),
            context.lhs,
            &arguments,
            &resolved_method.params,
            en,
        );
        let next_entry = find_entry_for_static_invocation(
            class_name,
            context.invocation.identifier(),
            context.invocation.argument_types(),
            context.program,
            en.symbol_table(),
        );

        next_entry
    } else {
        non_static_resolved_method_invocation(
            state,
            context,
            class_name,
            resolved_method.clone(),
            en,
        )
    }
}

/// Non-static case, multiple candidate methods that could be called
///
/// For example a method from a superclass or an overriden method from a subclass could be called,
/// depending on the type of the object.
pub(super) fn multiple_method_invocation(
    state: &mut State,
    invocation_lhs: &Identifier,
    context: InvocationContext,
    // For each type, the method implementation it resolves to.
    potential_methods: &HashMap<Identifier, (Declaration, Rc<Method>)>,
    en: &mut impl Engine,
) -> ActionResult {
    info!(state.logger, "Multiple method invocation");
    let object = &state.threads[&state.active_thread].stack.lookup(invocation_lhs).unwrap();
    // object can be either a concrete reference to a heap object, or a symbolic object
    // the latter means that we have to split states here, one path for each distinct method that is resolved to,
    // if all aliases resolve to the same method, then we can also continue with that path
    match object.as_ref() {
        Expression::Ref { type_, .. } => {
            let reference_type_name = type_.as_reference_type().expect("expected reference type");

            let method = potential_methods.get(reference_type_name).unwrap();

            let (declaration, member) = method;

            let decl_name = declaration.name();

            let next_entry = non_static_resolved_method_invocation(
                state,
                context,
                decl_name,
                member.clone(),
                en,
            );
            ActionResult::FunctionCall(next_entry)
        }
        Expression::SymbolicRef { var, .. } => {
            remove_symbolic_null(&mut state.alias_map, var);
            let alias_entry = &state.alias_map[var];

            // if symbolicref contains only objects of one type
            // we can resolve which method to call

            if let Some(RuntimeType::ReferenceRuntimeType { type_ }) = alias_entry.uniform_type() {
                // All aliases have the same type, so they all resolve to the same method.
                let (declaration, member) = potential_methods.get(&type_).unwrap();

                let decl_name = declaration.name();

                let next_entry = non_static_resolved_method_invocation(
                    state,
                    context,
                    decl_name,
                    member.clone(),
                    en,
                );
                ActionResult::FunctionCall(next_entry)
            } else {
                // Not all aliases have the same type, so it can happen that different types resolve to different methods.
                // First we check to which methods they resolve:

                // A mapping from a (class_name, method_name) -> array of aliases that resolve to this method.
                let resulting_alias = utils::group_by(alias_entry.aliases.iter().map(|alias| {
                    let (decl, method) = (potential_methods.get(
                        alias
                            .type_of()
                            .as_reference_type()
                            .expect("expected reference type"),
                    ))
                    .expect("Could not find method for the type");
                    ((decl.name().clone(), method.name.clone()), alias.clone())
                }));

                if resulting_alias.len() == 1 {
                    // not a uniform type, but all aliases resolve to the same method, we can continue with this path.
                    let ((decl_name, method_name), _objects) =
                        resulting_alias.iter().next().unwrap();
                    debug!(
                        state.logger,
                        "Symbolic object contains types that resolve to the same method {:?}::{:?}",
                        decl_name,
                        method_name
                    );

                    // All methods are the same for each candidate class, so take the first.
                    let (_decl, method) = potential_methods.values().next().unwrap();

                    let next_entry = non_static_resolved_method_invocation(
                        state,
                        context,
                        decl_name,
                        method.clone(),
                        en,
                    );
                    return ActionResult::FunctionCall(next_entry);
                }
                //dbg!(resulting_alias.keys());

                // We need to split states such that each resulting path has a single type for the object in the alias map.
                let symbolic_object_ref = var.clone();
                split_states_with_aliases(en, state, symbolic_object_ref, resulting_alias);
                // Try again with updated states.
                multiple_method_invocation(state, invocation_lhs, context, potential_methods, en)
            }
        }
        Expression::Conditional {
            guard,
            true_,
            false_,
            ..
        } => {
            state_split::conditional_state_split(
                state,
                en,
                guard.clone(),
                true_.clone(),
                false_.clone(),
                invocation_lhs.clone(),
            );
            // Try again with split states.
            multiple_method_invocation(state, invocation_lhs, context, potential_methods, en)
        }
        _ => unreachable!("Expected Ref or SymbolicRef, found {:?}", object),
    }
}

/// Checks the aliases whether their type is unique, if so return that type
/// otherwise return None
fn find_unique_type(aliases: &Vec<Rc<Expression>>) -> Option<RuntimeType> {
    assert!(!aliases.is_empty());

    let all_have_same_type = aliases
        .iter()
        .map(AsRef::as_ref)
        .map(Typeable::type_of)
        .all_equal();

    if all_have_same_type {
        Some(aliases[0].type_of())
    } else {
        None
    }
}

/// Helper function for a non-static method invocation with an already resolved method.
fn non_static_resolved_method_invocation(
    state: &mut State,
    context: InvocationContext,
    class_name: &Identifier,
    resolved_method: Rc<Method>,
    en: &mut impl Engine,
) -> u64 {
    info!(state.logger, "non-static method invocation");

    // evaluate arguments
    let arguments = evaluated_arguments(context.invocation, state, en);

    let invocation_lhs = match context.invocation {
        Invocation::InvokeMethod { lhs, .. } => lhs,
        Invocation::InvokeSuperMethod { .. } => "this", // we pass "this" object to superclass methods aswell.
        _ => panic!("expected invoke method or invokeSuperMethod"),
    };

    // This is going to give problems, fix by looking up the type in stack?
    let this = (
        RuntimeType::ReferenceRuntimeType {
            type_: class_name.clone(),
        },
        invocation_lhs.to_owned().into(),
    );

    exec_method_entry(
        state,
        context.return_point,
        resolved_method,
        context.lhs,
        &arguments,
        en,
        this,
    );

    let next_entry = find_entry_for_static_invocation(
        class_name,
        context.invocation.identifier(),
        context.invocation.argument_types(),
        context.program,
        en.symbol_table(),
    );

    next_entry
}

fn exec_method_entry(
    state: &mut State,
    return_point: u64,
    method: Rc<Method>,
    lhs: Option<Lhs>,
    arguments: &[Rc<Expression>],
    en: &mut impl Engine,
    this: (RuntimeType, Identifier),
) {
    let this_param = Parameter::new(
        runtime_to_nonvoidtype(this.0.clone()).expect("concrete, nonvoid type"),
        constants::this_str(),
    );

    let this_expr = Expression::Var {
        var: this.1.clone(),
        type_: this.0,
        info: method.info,
    };
    let parameters = std::iter::once(&this_param).chain(method.params.iter());
    let arguments = std::iter::once(Rc::new(this_expr)).chain(arguments.iter().cloned());

    push_stack_frame(
        state,
        return_point,
        method.clone(),
        lhs,
        parameters.zip(arguments),
        en,
    )
}

fn exec_static_method_entry(
    state: &mut State,
    return_point: u64,
    member: Rc<Method>,
    lhs: Option<Lhs>,
    arguments: &[Rc<Expression>],
    parameters: &[Parameter],
    en: &mut impl Engine,
) {
    push_stack_frame(
        state,
        return_point,
        member,
        lhs,
        parameters.iter().zip(arguments.iter().cloned()),
        en,
    )
}

pub(super) fn exec_constructor_entry(
    state: &mut State,
    context: InvocationContext,
    method: Rc<Method>,
    class_name: &Identifier,
    en: &mut impl Engine,
    this_param: Parameter,
) {
    let parameters = std::iter::once(&this_param).chain(method.params.iter());

    let fields = en
        .symbol_table()
        .get_all_fields(class_name)
        .iter()
        .map(|(s, t)| (s.clone(), t.default().into()))
        .collect();
    let structure = HeapValue::ObjectValue {
        fields,
        type_: method.type_of(),
    };

    let object_ref = state.allocate_on_heap(structure);
    let arguments =
        std::iter::once(object_ref).chain(evaluated_arguments(context.invocation, state, en));

    push_stack_frame(
        state,
        context.return_point,
        method.clone(),
        context.lhs,
        parameters.zip(arguments),
        en,
    )
}

pub(super) fn exec_super_constructor(
    state: &mut State,
    context: InvocationContext,
    method: Rc<Method>,
    parameters: &[Parameter],
    en: &mut impl Engine,
    this_param: Parameter,
) {
    let parameters = std::iter::once(&this_param).chain(parameters.iter());

    // instead of allocating a new object, add the new fields to the existing 'this' object.
    let object_ref = state
        .threads[&state.active_thread]
        .stack
        .lookup(&constants::this_str())
        .expect("super() is called in a constructor with a 'this' object on the stack");
    let arguments =
        std::iter::once(object_ref).chain(evaluated_arguments(context.invocation, state, en));

    push_stack_frame(
        state,
        context.return_point,
        method,
        context.lhs,
        parameters.zip(arguments),
        en,
    )
}

fn push_stack_frame<'a, P>(
    state: &mut State,
    return_point: u64,
    method: Rc<Method>,
    lhs: Option<Lhs>,
    params: P,
    en: &mut impl Engine,
) where
    P: Iterator<Item = (&'a crate::Parameter, Rc<Expression>)>,
{
    let params = params
        .map(|(p, e)| (p.name.clone(), evaluate(state, e, en)))
        .collect();
    let stack_frame = StackFrame {
        return_pc: return_point,
        returning_lhs: lhs,
        params,
        current_member: method,
    };
    state.threads.get_mut(&state.active_thread).unwrap().stack.push(stack_frame);
}

/// Helper function to get and evaluate arguments from invocation.
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
