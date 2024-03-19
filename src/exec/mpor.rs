use crate::cfg::CFGStatement;

use super::State;

pub(super) fn validate_quasi_monotonicity(state: State, statement: CFGStatement) -> bool {
    println!("{:?}", statement);
    return true;
}

fn get_accesses(statement: CFGStatement) {
    // match statement {
    //     CFGStatement::Statement(_) => todo!(),
    //     CFGStatement::Ite(_, _, _) => todo!(),
    //     CFGStatement::While(_, _) => todo!(),
    // }
}