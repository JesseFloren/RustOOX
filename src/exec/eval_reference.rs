use crate::exec::state_split::split_states_with_aliases;
use crate::Expression;
use crate::Identifier;
use crate::Reference;

use super::init_symbolic_reference;
use super::remove_symbolic_null;
use super::state_split::conditional_state_split;
use super::Engine;
use super::State;

pub trait ExecRef {
    fn exec(state: &mut State, var: &Identifier, en: &mut impl Engine) {
        // Check stack for the variable
        let object = &state.threads[&state.active_thread].stack.lookup(var).unwrap();

        // The object can refer to either a reference or a symbolic reference.
        // The concrete reference can be easily handled.
        // The Symbolic reference requires a state split.
        match object.as_ref() {
            Expression::Ref { ref_, .. } => {
                Self::exec_over_ref(state, ref_);
            },
            Expression::SymbolicRef { var, type_, .. } => {
                if let None = state.alias_map.get(var) {
                    init_symbolic_reference(state, var, type_, en);
                } 

                remove_symbolic_null(&mut state.alias_map, var);
                Self::exec_over_symbolic_ref(state, var, en);
            },
            Expression::Conditional {
                guard,
                true_,
                false_,
                ..
            } => {
                conditional_state_split(
                    state,
                    en,
                    guard.clone(),
                    true_.clone(),
                    false_.clone(),
                    var.clone(),
                );
                // Try again with split states.
                Self::exec_over_symbolic_ref(state, var, en);
            }
            _ => unreachable!("Expected Ref, found {:?}", object)
        }
    }
    
    fn exec_over_symbolic_ref(state: &mut State, var: &Identifier, en: &mut impl Engine) {
        let alias_entry = &state.alias_map[var];

        let resulting_alias = vec![alias_entry.aliases().clone()];
        if resulting_alias.len() == 1 {
            let expr = (*alias_entry.aliases()[0]).clone();

            return match expr {
                Expression::Ref { ref_, .. } => {
                    Self::exec_over_ref(state, &ref_);
                }
                _ => unreachable!("Expected ref")
            }
        }

        let aliases = vec![alias_entry.aliases().clone()];
        split_states_with_aliases(en, state, var.clone(), aliases);
        Self::exec(state, var, en);
    }

    fn exec_over_ref(state: &mut State, ref_: &Reference);
}

pub(super) fn get_reference() {

}