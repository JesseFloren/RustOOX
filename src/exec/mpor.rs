use std::{collections::HashSet, rc::Rc};

use itertools::Itertools;

use crate::{cfg::CFGStatement, exec::ThreadState, stack::Stack, Expression, Identifier, Lhs, Reference, Rhs, Statement};

use super::{eval::evaluate, eval_assertion, Access, AliasMap, Engine, EngineContext, State};


pub(super) fn validate_quasi_monotonicity(state: &mut State, statement: CFGStatement, curr_statement: CFGStatement, en: &mut EngineContext) -> bool {
    let mut curr_accesses = get_all_accesses(state, statement.clone(), en);
    let lock_accesses = get_lock_accesses(state, curr_statement.clone(), en);

    curr_accesses.extend(lock_accesses);

    let mut out: bool = true;
    let mut temp_state = state.clone();
    for thread in state.threads.values_mut().sorted_by_key(|x| x.tid) {
        if let Some(prev_accesses) = thread.prev_accesses.clone() {
            if thread.tid != state.active_thread { en.statistics.measure_dep_invocation();}
            if thread.tid == state.active_thread || has_access_conflicts(&mut temp_state, en, prev_accesses.clone(), curr_accesses.clone()) {
                thread.prev_accesses = None;
            } else if thread.tid > state.active_thread {
                out = false;
                break;
            }
        }   
    }
    state.threads.get_mut(&state.active_thread).unwrap().prev_accesses = Some(curr_accesses);
    out
}

pub(super) fn get_all_accesses(state: &mut State, statement: CFGStatement, en: &mut impl Engine) -> Vec<Access> {
    let thread = state.threads[&state.active_thread].clone();
    let alias_map = state.alias_map.clone();
    match statement {
        CFGStatement::Statement(Statement::Assign { lhs, rhs, ..  }) => {
            let mut accesses = vec![];
            match lhs.clone()  {
                Lhs::LhsField { var, field, .. } => {
                    accesses.push(Access::FieldWrite(get_heap_ref(var, thread.stack.clone(), alias_map.clone()), field));
                },
                Lhs::LhsElem { var, index, .. } => {
                    accesses.push(Access::ElemWrite(get_heap_ref(var, thread.stack.clone(), alias_map.clone()), evaluate(state, index, en)));
                }
                _ => {}
            }
            match rhs.clone() {
                Rhs::RhsField { var, field,.. } => {
                    match (*var).clone() {
                        Expression::Var { var, .. } => {
                            accesses.push(Access::FieldRead(get_heap_ref(var, thread.stack.clone(), alias_map.clone()), field));
                        },
                        _ => {}
                    }
                },
                Rhs::RhsElem { var, index, .. } => {
                    match (*var).clone() {
                        Expression::Var { var, .. } => {
                            accesses.push(Access::ElemRead(get_heap_ref(var, thread.stack.clone(), alias_map.clone()), evaluate(state, index, en)));
                        },
                        _ => {}
                    }
                },
                _ => {}
            };
            accesses
        },

        CFGStatement::Statement(Statement::Join { .. }) => {
            vec![Access::Join(thread.tid)]
        },
        CFGStatement::FunctionExit { .. } => {
            if thread.state == ThreadState::Finished {
                return vec![Access::FinishedThread(thread.parents)];
            }
            vec![]
        },
        _ => vec![]
    }
}

pub(super) fn get_lock_accesses(state: &mut State, statement: CFGStatement, en: &mut impl Engine) -> Vec<Access> {
    let thread = state.threads[&state.active_thread].clone();
    let alias_map = state.alias_map.clone();
    match statement {
        CFGStatement::Statement(Statement::Lock { identifier, .. }) => {
            vec![Access::LockAction(get_heap_ref(identifier, thread.stack.clone(), alias_map.clone()))]
        },
        CFGStatement::Statement(Statement::Unlock { identifier, .. }) => {
            vec![Access::LockAction(get_heap_ref(identifier, thread.stack.clone(), alias_map.clone()))]
        },
        _ => vec![]
    }
}

pub(super) fn get_heap_ref(var: Identifier, stack: Stack, alias_map: AliasMap) -> HashSet<Reference> {
    let mut identifiers = vec![var.clone()];
    let mut references = vec![];

    let (idents, refs) = get_stack_vars(stack.lookup(&var.clone()));
    if let Some(var) = idents { identifiers.push(var); }
    if let Some(ref_) = refs { references.push(ref_); }

    for ident in identifiers {
        if let Some(entry) = alias_map.get(&ident) {
            for alias in entry.aliases.clone() {
                let (_, refs) = get_stack_vars(Some(alias));
                if let Some(ref_) = refs { references.push(ref_); }
            }
        }
    }
    return HashSet::from_iter(references.iter().cloned());
}

 fn get_stack_vars(expr: Option<Rc<Expression>>) -> (Option<Identifier>, Option<Reference>) {
    if let Some(x) =  expr {
        match (*x).clone() {
            Expression::Var { var, .. } => (Some(var),None),
            Expression::SymbolicVar { var, .. } =>(Some(var),None),
            Expression::Ref { ref_, .. } => (None,Some(ref_)),
            Expression::SymbolicRef { var, .. } => (Some(var),None),
            _ => (None, None)
        }
    } else {
        (None, None)
    }
   
}

fn has_access_conflicts(state: &mut State, en: &mut impl Engine, prev: Vec<Access>, curr: Vec<Access>) -> bool {
    for x in prev.iter() {
        for y in curr.iter() {
            match x {
                Access::FieldRead(x1, x2) => match y {
                    Access::FieldRead(_, _) => (),
                    Access::FieldWrite(y1, y2) => {
                        let conflicts = x1.intersection(y1).collect_vec();
                        if conflicts.len() > 0 && x2 == y2 { 
                            return true 
                        }
                    },
                    _ => {}
                },
                Access::FieldWrite(x1, x2) => match y {
                    Access::FieldRead(y1, y2) => {
                        let conflicts = x1.intersection(y1).collect_vec();
                        if conflicts.len() > 0 && x2 == y2 { 
                            return true 
                        }
                    }
                    Access::FieldWrite(y1, y2) => {
                        let conflicts: Vec<&i64> = x1.intersection(y1).collect_vec();
                        if conflicts.len() > 0 && x2 == y2  { 
                            return true 
                        }
                    },
                    _ => {}
                },
                Access::ElemRead(x1, x2) => match y {
                    Access::ElemRead(_, _) => (),
                    Access::ElemWrite(y1, y2) => {
                        let conflicts = x1.intersection(y1).collect_vec();
                        if conflicts.len() > 0 && compare_expression(state, en, x2.clone(), y2.clone()) { 
                            return true 
                        }
                    },
                    _ => {}
                },
                Access::ElemWrite(x1, x2) => match y {
                    Access::ElemRead(y1, y2) => {
                        let conflicts = x1.intersection(y1).collect_vec();
                        if conflicts.len() > 0 && compare_expression(state, en, x2.clone(), y2.clone()) { 
                            return true 
                        }
                    }
                    Access::ElemWrite(y1, y2) => {
                        let conflicts: Vec<&i64> = x1.intersection(y1).collect_vec();
                        if conflicts.len() > 0 && compare_expression(state, en, x2.clone(), y2.clone())  { 
                            return true 
                        }
                    },
                    _ => {}
                },
                Access::LockAction(x1) => match y {
                    Access::LockAction(y1) => {
                        let conflicts: Vec<&i64> = x1.intersection(y1).collect_vec();
                        if conflicts.len() > 0 { 
                            return true 
                        }
                    },
                    _ => {}
                }
                Access::FinishedThread(parents) => match y {
                    Access::Join(tid) => {
                        if parents.contains(tid) {
                            return true;
                        }
                    },
                    _ => {}
                },
                _ => {},
            }
        }
    }
    return false;
}

fn compare_expression(state: &mut State, en: &mut impl Engine, lhs: Rc<Expression>, rhs: Rc<Expression>) -> bool {
    let expr = Rc::new(Expression::BinOp { bin_op: crate::BinOp::Equal, lhs, rhs, type_: crate::RuntimeType::BoolRuntimeType, info: crate::SourcePos::UnknownPosition });
    println!("{}", expr);
    !eval_assertion(state, expr.clone(), en)
}