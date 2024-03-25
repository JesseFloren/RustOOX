use std::collections::{HashMap, VecDeque};

use itertools::Itertools;

use crate::{cfg::CFGStatement, Expression, Identifier, Reference, Statement};

use super::{State, Thread, ThreadState};

pub(super) fn check_deadlock(
    state: &State
) {
    if !state.threads.values().any(|t| t.state == ThreadState::Enabled) && !(state.threads[&0].state == ThreadState::Finished) { 
        println!("{:?}", state.threads.values().map(|t| (t.tid, t.state.clone())).collect_vec());
        unreachable!("DEADLOCK");
    }
}

pub(super) fn update_next_locks(
    state: &mut State,
    statement: &CFGStatement
) {
    if let CFGStatement::Statement(Statement::Lock { identifier, .. }) = statement {
        exec_lock(state, identifier)
    }

    if let CFGStatement::Statement(Statement::Unlock { identifier, .. }) = statement {
        exec_unlock(state, identifier)
    }
}


fn exec_lock(
    state: &mut State, 
    var: &Identifier
) {
    if let Some(_) = state.alias_map.get(var) {
        return lock_for_aliases(state, var);
    };
    let object = &state.threads[&state.active_thread].stack.lookup(var).unwrap();
    match object.as_ref() {
        Expression::Ref { ref_, .. } => {
            lock_ref(state, ref_);
        }
        _ => unreachable!("Expected Ref, found {:?}", object)
    }
}

fn lock_for_aliases(
    state: &mut State, 
    var: &Identifier,
)  {
    let alias_entry = &state.alias_map[var];
    let resulting_alias = vec![alias_entry.aliases().clone()];
    if resulting_alias.len() == 1 {
        let expr = (*alias_entry.aliases()[0]).clone();

        return match expr {
            Expression::Ref { ref_, .. } => {
                lock_ref(state, &ref_);
            }
            _ => unreachable!("Expected ref")
        }
        
    }
    unreachable!("Expected ref")
}

fn lock_ref(
    state: &mut State, 
    ref_: &Reference, 
) {
    if let Some(_) = state.lock_requests.get(ref_) {
        state.lock_requests.get_mut(ref_).unwrap().push_back(state.active_thread);
        state.threads.get_mut(&state.active_thread).unwrap().state = ThreadState::Disabled;
        println!("Thread {}, aquires lock: {}", state.active_thread, ref_)
    } else {
        state.lock_requests.insert(*ref_, VecDeque::new());
        println!("Thread {}, requests lock: {}", state.active_thread, ref_)
    }
}

fn exec_unlock(
    state: &mut State, 
    var: &Identifier, 
) {
    if let Some(_) = state.alias_map.get(var) {
        return unlock_for_aliases(state, var);
    };
    let object = &state.threads[&state.active_thread].stack.lookup(var).unwrap();
    match object.as_ref() {
        Expression::Ref { ref_, .. } => {
            unlock_ref(state, ref_);
        },
        _ => unreachable!("Expected Ref, found {:?}", object)
    }
}

fn unlock_for_aliases(
    state: &mut State, 
    var: &Identifier,
) {
    let alias_entry = &state.alias_map[var];
    let resulting_alias = vec![alias_entry.aliases().clone()];
    if resulting_alias.len() == 1 {
        let expr = (*alias_entry.aliases()[0]).clone();

        return match expr {
            Expression::Ref { ref_, .. } => {
                unlock_ref(state, &ref_);
            }
            _ => unreachable!("Expected ref")
        }
        
    }

    unreachable!("Expected concrete ref");
}

fn unlock_ref(
    state: &mut State, 
    ref_: &Reference, 
) {
    if let Some(requests) = state.lock_requests.remove(ref_) {
        for request in requests {
            state.threads.get_mut(&request).unwrap().state = ThreadState::Enabled;
        }
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