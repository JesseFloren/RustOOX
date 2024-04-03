use std::collections::{HashMap, VecDeque};

use itertools::Itertools;

use crate::{cfg::CFGStatement, Reference, Statement};

use super::{eval_reference::ExecRef, Engine, State, ThreadState};

struct ExecLock {}

impl ExecRef for ExecLock {
    fn exec_over_ref(state: &mut State, ref_: &Reference) {
        if let Some(_) = state.lock_requests.get(ref_) {
            state.lock_requests.get_mut(ref_).unwrap().push_back(state.active_thread);
            state.threads.get_mut(&state.active_thread).unwrap().state = ThreadState::Disabled;
        } else {
            state.lock_requests.insert(*ref_, VecDeque::new());
        }
    }
}

struct ExecUnlock {}

impl ExecRef for ExecUnlock {
    fn exec_over_ref(state: &mut State, ref_: &Reference) {
        if let Some(requests) = state.lock_requests.remove(ref_) {
            for request in requests {
                state.threads.get_mut(&request).unwrap().state = ThreadState::Enabled;
            }
        }
    }
}

pub(super) fn check_deadlock(
    state: &State
) {
    if !state.threads.values().any(|t| t.state == ThreadState::Enabled) 
    && !(state.threads[&0].state == ThreadState::Finished) 
    && !state.threads.values().any(|t| t.state == ThreadState::Excepted) { 
        println!("{:?}", state.threads.values().map(|t| (t.tid, t.state.clone())).collect_vec());
        println!("{:?}", state.path);
        unreachable!("DEADLOCK");
    }
}

pub(super) fn update_next_locks(
    state: &mut State,
    statement: &CFGStatement,
    en: &mut impl Engine
) {
    if let CFGStatement::Statement(Statement::Lock { identifier, .. }) = statement {
        ExecLock::exec(state, identifier, en)
    }

    if let CFGStatement::Statement(Statement::Unlock { identifier, .. }) = statement {
        ExecUnlock::exec(state, identifier, en)
    }
}

pub(super) fn update_joins(
    state: &mut State,
    program: &HashMap<u64, CFGStatement>
) {
    for (tid, thread) in state.threads.clone().iter() {
        if let CFGStatement::Statement(Statement::Join {..}) = program[&thread.pc] {
            if state.threads.values().any(|t| t.parents.contains(tid) && t.state != ThreadState::Finished) {
                state.threads.get_mut(tid).unwrap().state = ThreadState::Disabled;
            } else {
                state.threads.get_mut(tid).unwrap().state = ThreadState::Enabled;
            }
        }
    }
}