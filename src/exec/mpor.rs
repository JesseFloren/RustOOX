use std::{collections::HashSet, rc::Rc};

use clap::Id;
use itertools::Itertools;

use crate::{cfg::CFGStatement, stack::Stack, Expression, Identifier, Lhs, Reference, Rhs, Statement};

use super::{Access, AliasMap, State};

pub(super) fn validate_quasi_monotonicity(state: &mut State, statement: CFGStatement) -> bool {
    let pc = state.threads[&state.active_thread].pc;
    let curr_accesses = get_all_accesses(statement.clone(), state.threads[&state.active_thread].stack.clone(), state.alias_map.clone());

    let mut out: bool = true;
    for thread in state.threads.values_mut().sorted_by_key(|x| x.tid) {
        if let Some(prev_accesses) = thread.prev_accesses.clone() {
            if thread.tid == state.active_thread || has_access_conflicts(prev_accesses.clone(), curr_accesses.clone()) {
                thread.prev_accesses = None;
            } else if thread.tid > state.active_thread {
                out = false;
            }
        }   
    }
    state.threads.get_mut(&state.active_thread).unwrap().prev_accesses = Some(curr_accesses);
    out
}

fn get_all_accesses(statement: CFGStatement, stack: Stack, alias_map: AliasMap) -> Vec<Access> {
    match statement {
        CFGStatement::Statement(Statement::Assign { lhs, rhs, info  }) => {
            let mut accesses = vec![];
            match lhs.clone()  {
                Lhs::LhsField { var, field, .. } => {
                    accesses.push(Access::FieldWrite(get_heap_ref(var, stack.clone(), alias_map.clone()), field));
                }
                _ => {}
            }
            match rhs.clone() {
                Rhs::RhsField { var, field,.. } => {
                    match (*var).clone() {
                        Expression::Var { var, .. } => {
                            accesses.push(Access::FieldRead(get_heap_ref(var, stack.clone(), alias_map.clone()), field));
                        },
                        _ => {}
                    }
                },
                _ => {}
            };
            accesses
        },
        // CFGStatement::Statement(Statement::Skip { .. }) => todo!(),
        // CFGStatement::Statement(Statement::Assert { .. }) => todo!(),
        // CFGStatement::Statement(Statement::Assume { assumption, .. }) => {
        //     match assumption {
        //         itertools::Either::Left(expr) => vec![Access::FieldRead(HashSet::from([3]), Identifier::with_unknown_pos("x".to_owned()))],
        //         itertools::Either::Right(_) => vec![],
        //     }
        // },
        // CFGStatement::Statement(Statement::Continue { .. }) => todo!(),
        // CFGStatement::Statement(Statement::Break { .. }) => todo!(),
        // CFGStatement::Statement(Statement::Return { .. }) => todo!(),
        // CFGStatement::Statement(Statement::Throw { .. }) => todo!(),
        // CFGStatement::Statement(Statement::Try { .. }) => todo!(),
        // CFGStatement::Ite(expr, _, _) => {
        //     match expr {
        //         itertools::Either::Left(expr) => vec![Access::FieldRead(HashSet::from([3]), Identifier::with_unknown_pos("x".to_owned()))],
        //         itertools::Either::Right(_) => vec![],
        //     }
        // },
        // CFGStatement::While(_, _) => todo!(),
        _ => vec![]
    }
}

fn get_heap_ref(var: Identifier, stack: Stack, alias_map: AliasMap) -> HashSet<Reference> {
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

fn has_access_conflicts(xs: Vec<Access>, ys: Vec<Access>) -> bool {
    for x in xs.iter() {
        for y in ys.iter() {
            match x {
                Access::FieldRead(x1, x2) => match y {
                    Access::FieldRead(_, _) => (),
                    Access::FieldWrite(y1, y2) => {
                        let conflicts = x1.intersection(y1).collect_vec();
                        if conflicts.len() > 0 && x2 == y2 { 
                            return true 
                        }
                    }
                },
                Access::FieldWrite(x1, x2) => match y {
                    Access::FieldRead(y1, y2) => {
                        let conflicts = x1.intersection(y1).collect_vec();
                        if conflicts.len() > 0 && x2 == y2 { 
                            return true 
                        }
                    }
                    Access::FieldWrite(y1, y2) => {
                        let conflicts = x1.intersection(y1).collect_vec();
                        if conflicts.len() > 0 && x2 == y2  { 
                            return true 
                        }
                    }
                },
            }
        }
    }
    return false;
}