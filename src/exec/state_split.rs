//! This module contains functions that split up the state, for reasons other than due to an if/while (branching) statement in the code.
//! This includes conditional state splitting, splitting of state due to different typing of an object,
//! and array initialisation.

use std::rc::Rc;

use itertools::Either;
use slog::{debug, info};

use crate::{
    exec::{array::array_initialisation, AliasEntry},
    syntax::{Expression, Identifier, RuntimeType},
};

use super::{exec_assume, Engine, State};

/// A state split on the same pc.
///
/// This occurs when a lhs in a statement is a conditional
/// and requires the state to split into paths where the condition is true and false.
/// A lhs becomes a conditional for example when `Point p := a[i];` where `i` is a symbolic variable.
/// When later on p is referenced, e.g. `p.x` is called, it must be determined which element of a is referred to.
pub fn conditional_state_split(
    state: &mut State,
    en: &mut impl Engine,
    guard: Rc<Expression>,
    true_lhs: Rc<Expression>,
    false_lhs: Rc<Expression>,
    lhs_name: Identifier,
) {
    // split up the states into two, one where we assume guard == true and one where we assume guard == false.
    // Program counter is untouched, path length not increased.
    debug!(
        state.logger,
        "Splitting up current path into 2 paths due to conditional state split"
    );
    en.statistics().measure_branches(2);
    let mut true_state = en.clone_state_with_new_path_id(state);
    let feasible_path = exec_assume(&mut true_state, Either::Left(guard.clone()), en);
    if feasible_path {
        true_state.threads.get_mut(&true_state.active_thread).unwrap().stack.insert_variable(lhs_name.clone(), true_lhs);
        en.add_remaining_state(true_state);
    }
    // continue with false state
    let false_state = state;
    let feasible_path = exec_assume(
        false_state,
        Either::Left(crate::dsl::negate(guard).into()),
        en,
    );
    if feasible_path {
        false_state.threads.get_mut(&false_state.active_thread).unwrap().stack.insert_variable(lhs_name, false_lhs);
    }
}

/// For each of the new aliases, create a new state and replace the symbolic object with those aliases.
/// The current state is mutated instead of added to the backlog.
pub(super) fn split_states_with_aliases(
    en: &mut impl Engine,
    state: &mut State,
    symbolic_object_ref: Identifier,
    aliases: Vec<Vec<Rc<Expression>>>,
) {
    assert!(aliases.len() > 1);
    en.statistics().measure_branches(aliases.len() as u32);

    debug!(state.logger, "Splitting up current path into {:?} paths due to polymorphic method invocation", aliases.len();
        "object" => #?symbolic_object_ref,
        "resulting_split" => #?aliases
    );

    // Turn it into an iterator over the objects
    let mut aliases = aliases.into_iter();

    let objects = aliases.next().unwrap();
    state
        .alias_map
        .insert(symbolic_object_ref.clone(), AliasEntry::new(objects));

    for alias in aliases {
        let mut state = en.clone_state_with_new_path_id(state);
        state
            .alias_map
            .insert(symbolic_object_ref.clone(), AliasEntry::new(alias));
        en.add_remaining_state(state);
    }
}

/// Splits the current state into N + 1 states, each with a single concrete array with increasing concrete size, or a null.
pub(super) fn exec_array_initialisation(
    state: &mut State,
    engine: &mut impl Engine,
    array_name: Identifier,
    array_type: RuntimeType,
) {
    let max_array_size = engine.options().symbolic_array_size;
    engine
        .statistics()
        .measure_branches((max_array_size + 1) as u32); // including null, so + 1
    info!(
        state.logger,
        "Symbolic array initialisation of {} into {} paths",
        array_name,
        max_array_size + 1
    );

    let inner_type = match array_type.clone() {
        RuntimeType::ArrayRuntimeType { inner_type } => inner_type,
        _ => panic!("Expected array type, found {:?}", array_type),
    };

    // initialise new states with arrays 1..N
    for array_size in 1..=max_array_size {
        let mut new_state = engine.clone_state_with_new_path_id(state);
        array_initialisation(
            &mut new_state,
            &array_name,
            array_size,
            array_type.clone(),
            *inner_type.clone(),
            engine.symbol_table(),
        );

        // note path_length does not decrease, we stay at the same statement containing array access
        engine.add_remaining_state(new_state);
    }

    // And a state for the case where the array is NULL
    let mut null_state = engine.clone_state_with_new_path_id(state);
    null_state.alias_map.insert(
        array_name.clone(),
        AliasEntry::new(vec![Expression::NULL.into()]),
    );
    engine.add_remaining_state(null_state);

    // initialise array on the current state, with size 0
    array_initialisation(
        state,
        &array_name,
        0,
        array_type,
        *inner_type,
        engine.symbol_table(),
    );
}
