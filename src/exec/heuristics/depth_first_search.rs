use std::{cell::RefCell, collections::{HashMap, BTreeMap}, rc::Rc};

use slog::Logger;

use crate::{
    cfg::CFGStatement, exec::heuristics::execute_instruction_for_all_states,
    statistics::Statistics, symbol_table::SymbolTable, Options,
};

use super::{IdCounter, State, SymResult};

/// The main function for the symbolic execution, any path splitting due to the control flow graph or array initialization happens here.
/// Depth first search, without using any other heuristic.
pub(crate) fn sym_exec(
    state: State,
    program: &HashMap<u64, CFGStatement>,
    flows: &HashMap<u64, Vec<u64>>,
    st: &SymbolTable,
    root_logger: Logger,
    path_counter: Rc<RefCell<IdCounter<u64>>>,
    statistics: &mut Statistics,
    _entry_method: crate::cfg::MethodIdentifier,
    options: &Options,
) -> SymResult {
    let mut remaining_states = vec![state];

    while let Some(state) = remaining_states.pop() {
        let current_pc = state.threads[&state.active_thread].pc;
        let step = execute_instruction_for_all_states(
            vec![state],
            program,
            flows,
            st,
            root_logger.clone(),
            path_counter.clone(),
            statistics,
            options,
        );

        if options.visualize_heuristic {
            let s = crate::prettyprint::cfg_pretty::pretty_print_compilation_unit(
                &|pc| {
                    Some(format!(
                        "{}, visited: [{}] {}",
                        pc,
                        statistics.coverage.get(&pc).map(|_pc| "x").unwrap_or(" "),
                        if current_pc == pc { "<<<" } else { "" }
                    ))
                },
                program,
                flows,
                st,
            );
            std::fs::write("visualize", &s).unwrap();
        }

        match step {
            Err(source_pos) => return SymResult::Invalid(source_pos),
            Ok(mut new_states) => {
                if let Some(children) = flows.get(&current_pc) {
                    // Add the children in DFS order
                    for child in children {
                        if let Some(values) = new_states.remove(child) {
                            remaining_states.extend(values);
                        }
                    }
                }
                // Could be a method call, add children in order of path id
                for (_path_id, values) in new_states.into_iter().collect::<BTreeMap<_, _>>() {
                    remaining_states.extend(values);
                }
            }
        }
    }
    SymResult::Valid
}
