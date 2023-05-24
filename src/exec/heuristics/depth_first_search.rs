use std::{cell::RefCell, collections::HashMap, rc::Rc};

use slog::{Logger};

use crate::{
    cfg::CFGStatement,
    statistics::Statistics,
    symbol_table::SymbolTable, exec::heuristics::execute_instruction_for_all_states,
};

use super::{
    action, ActionResult, IdCounter, State, SymResult,
};

/// The main function for the symbolic execution, any path splitting due to the control flow graph or array initialization happens here.
/// Depth first search, without using any other heuristic.
pub(crate) fn sym_exec(
    state: State,
    program: &HashMap<u64, CFGStatement>,
    flows: &HashMap<u64, Vec<u64>>,
    k: u64,
    st: &SymbolTable,
    root_logger: Logger,
    path_counter: Rc<RefCell<IdCounter<u64>>>,
    statistics: &mut Statistics,
    _entry_method: crate::cfg::MethodIdentifier,
    _visualize_heuristic: bool,
) -> SymResult {
    let mut remaining_states = vec![state];

    while let Some(state) = remaining_states.pop() {
        let pc = state.pc;
        let step = execute_instruction_for_all_states(vec![state], program, flows, k, st, root_logger.clone(), path_counter.clone(), statistics);

        match step {
            Err(source_pos) => return SymResult::Invalid(source_pos),
            Ok(mut new_states) => {
                if let Some(children) = flows.get(&pc) {
                    // Add the children in DFS order
                    for child in children {
                        if let Some(values) = new_states.remove(&child) {
                            remaining_states.extend(values);
                        }
                    }
                } 
                // Could be a method call, add children in random order
                for (_pc, values) in new_states {
                    remaining_states.extend(values);
                }
            }
        }
    }
    SymResult::Valid
}