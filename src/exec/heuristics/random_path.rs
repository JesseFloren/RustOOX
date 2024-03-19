use std::{cell::RefCell, collections::HashMap, ops::Deref, rc::Rc};

use itertools::Itertools;
use rand::{rngs::ThreadRng, Rng};
use slog::Logger;

use crate::{
    cfg::{CFGStatement, MethodIdentifier},
    statistics::Statistics,
    symbol_table::SymbolTable,
    Options,
};

use super::{
    execution_tree::{sym_exec_execution_tree, ExecutionTree, ExecutionTreeBasedHeuristic},
    IdCounter, ProgramCounter, State, SymResult,
};

// We also need to consider that there are a lot of branches that end quickly, like due to if (x == null) { throw exception; } guard insertions.
enum BTree {
    Node {
        statement: u64,
        false_: Option<Box<BTree>>, // A branch is optional since it is set to None when finished to cleanup memory.
        true_: Option<Box<BTree>>,
    },
    Leaf(Vec<State>), // All program counters should be equal in these states
}

impl BTree {
    fn statement(&self) -> u64 {
        match self {
            BTree::Node { statement, .. } => *statement,
            BTree::Leaf(states) => states[0].threads[&states[0].active_thread].pc,
        }
    }

    fn get_states(&mut self) -> Option<Vec<State>> {
        if let BTree::Leaf(states) = self {
            // Take the state, leaving an empty array
            let states = std::mem::take(states);
            Some(states)
        } else {
            None
        }
    }
}

enum TreeNode {
    Node(Vec<ProgramCounter>),
    Leaf(Vec<State>),
}

impl TreeNode {
    /// Assume it is a leaf and take out the states.
    fn take_states(&mut self) -> Option<Vec<State>> {
        if let TreeNode::Leaf(states) = self {
            // Take the state, leaving an empty array
            let states = std::mem::take(states);
            Some(states)
        } else {
            None
        }
    }
}

/// A program may encounter the same branch more than once, so we need to distinguish between them
/// We use this Identifier for this.
type BranchId = u64;

fn random_path(
    mut tree: Rc<RefCell<ExecutionTree>>,
    rng: &mut impl Rng,
) -> Rc<RefCell<ExecutionTree>> {
    loop {
        let node = tree.clone();
        match node.borrow().deref() {
            ExecutionTree::Node { children, .. } => {
                // dbg!(children.len());

                let idx = rng.gen_range(0..children.len());
                tree = children[idx].clone();
            }
            ExecutionTree::Leaf { .. } => {
                return tree;
            }
        };
    }
}

pub(super) struct RandomPath {
    rng: ThreadRng,
}

impl RandomPath {
    pub(super) fn new() -> RandomPath {
        RandomPath {
            rng: rand::thread_rng(),
        }
    }
}

impl ExecutionTreeBasedHeuristic for RandomPath {
    fn choice(
        &mut self,
        root: Rc<RefCell<ExecutionTree>>,
        _program: &HashMap<u64, CFGStatement>,
        _flows: &HashMap<u64, Vec<u64>>,
        _st: &SymbolTable,
        _entry_method: &MethodIdentifier,
        _coverage: &mut HashMap<ProgramCounter, usize>,
    ) -> Rc<RefCell<ExecutionTree>> {
        random_path(root, &mut self.rng)
    }
}

/// The main function for the symbolic execution, any path splitting due to the control flow graph or array initialization happens here.
pub(crate) fn sym_exec(
    state: State,
    program: &HashMap<u64, CFGStatement>,
    flows: &HashMap<u64, Vec<u64>>,
    st: &SymbolTable,
    root_logger: Logger,
    path_counter: Rc<RefCell<IdCounter<u64>>>,
    statistics: &mut Statistics,
    entry_method: crate::cfg::MethodIdentifier,
    options: &Options,
) -> SymResult {
    sym_exec_execution_tree(
        state,
        program,
        flows,
        st,
        root_logger,
        path_counter,
        statistics,
        entry_method,
        RandomPath::new(),
        options,
    )
}

fn assert_all_aliasmaps_are_equivalent(states: &[State]) -> bool {
    states.iter().map(|s| &s.alias_map).all_equal()
}
