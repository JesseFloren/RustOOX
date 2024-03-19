// simplify the expression

use std::{ops::Deref, rc::Rc};

use itertools::{Either, Itertools};

use crate::{
    dsl::{ands, negate, negative, ors, to_int_expr},
    exec::{heap, init_symbolic_reference, single_alias_elimination, Engine, State},
    positioned::SourcePos,
    syntax::{BinOp, Expression, Identifier, Lit, RuntimeType, UnOp},
};

pub type EvaluationResult<T> = Either<Rc<Expression>, T>;

pub fn evaluate_as_int(
    state: &mut State,
    expression: Rc<Expression>,
    en: &mut impl Engine,
) -> EvaluationResult<i64> {
    let expression = evaluate(state, expression, en);
    if let Expression::Lit {
        lit: Lit::IntLit { int_value },
        ..
    } = expression.deref()
    {
        Either::Right(*int_value)
    } else {
        Either::Left(expression)
    }
}

pub fn evaluate(
    state: &mut State,
    expression: Rc<Expression>,
    en: &mut impl Engine,
) -> Rc<Expression> {
    // dbg!(expression)

    // dbg!(&expression);
    eval_locally(state, expression, en)
}

fn eval_locally(
    state: &mut State,
    expression: Rc<Expression>,
    en: &mut impl Engine,
) -> Rc<Expression> {
    match expression.as_ref() {
        Expression::BinOp {
            bin_op, lhs, rhs, ..
        } => {
            let lhs = eval_locally(state, lhs.clone(), en);
            let rhs = eval_locally(state, rhs.clone(), en);
            evaluate_binop(*bin_op, lhs, rhs)
        }
        Expression::UnOp { un_op, value, .. } => {
            let value = eval_locally(state, value.clone(), en);
            evaluate_unop(un_op.clone(), value)
        }
        Expression::Var { var, .. } => {
            let o = state
                .threads[&state.active_thread]
                .stack
                .lookup(var)
                .unwrap_or_else(|| panic!("infeasible, object does not exist: {:?}", var));

            eval_locally(state, o, en)
        }
        Expression::SymbolicVar { .. } => expression,
        Expression::Lit { .. } => expression,
        Expression::SizeOf { var, .. } => {
            let expr = single_alias_elimination(state.threads[&state.active_thread].stack.lookup(var).unwrap(), &state.alias_map);

            match expr.as_ref() {
                Expression::Lit {
                    lit: Lit::NullLit, ..
                } => {
                    // infeasible path
                    return Expression::int(-1);
                }
                Expression::Ref { ref_, .. } => {
                    if let heap::HeapValue::ArrayValue { elements, .. } = &state.heap[ref_] {
                        return Expression::int(elements.len() as i64);
                    }
                }
                _ => todo!("Symbolic arrays are not implemented"),
            }
            panic!("invalid state, expected initialised array with arrayvalue in heap");
        }
        Expression::Ref { .. } => expression,
        Expression::SymbolicRef { var, type_, info } => {
            init_symbolic_reference(state, var, type_, en);

            Rc::new(Expression::SymbolicRef {
                var: var.clone(),
                type_: type_.clone(),
                info: *info,
            })
        }
        Expression::Conditional {
            guard,
            true_,
            false_,
            type_,
            info,
        } => {
            let guard = eval_locally(state, guard.clone(), en);
            let true_ = eval_locally(state, true_.clone(), en);
            let false_ = eval_locally(state, false_.clone(), en);

            match *guard {
                Expression::Lit {
                    lit: Lit::BoolLit { bool_value: true },
                    ..
                } => true_,

                Expression::Lit {
                    lit: Lit::BoolLit { bool_value: false },
                    ..
                } => false_,
                _ => Rc::new(Expression::Conditional {
                    guard,
                    true_,
                    false_,
                    type_: type_.clone(),
                    info: *info,
                }),
            }
        }
        Expression::Forall {
            elem,
            range,
            domain,
            formula,
            ..
        } => evaluate_quantifier(ands, elem, range, domain, formula.clone(), state, en),
        Expression::Exists {
            elem,
            range,
            domain,
            formula,
            ..
        } => evaluate_quantifier(ors, elem, range, domain, formula.clone(), state, en),
    }
}

fn evaluate_binop(bin_op: BinOp, lhs: Rc<Expression>, rhs: Rc<Expression>) -> Rc<Expression> {
    use crate::syntax::BinOp::*;
    use crate::syntax::Lit::*;
    use Expression::*;

    // dbg!(&bin_op, lhs, rhs);

    match (bin_op, lhs.as_ref(), rhs.as_ref()) {
        // Boolean evaluation
        (
            bin_op,
            Lit {
                lit: BoolLit { bool_value: a },
                ..
            },
            Lit {
                lit: BoolLit { bool_value: b },
                ..
            },
        ) => match bin_op {
            Implies => Expression::bool(!a || *b),
            And => Expression::bool(*a && *b),
            Or => Expression::bool(*a || *b),
            Equal => Expression::bool(*a == *b),
            NotEqual => Expression::bool(*a != *b),
            _ => panic!("unsupported boolean operator"),
        },
        (
            bin_op,
            Lit {
                lit: BoolLit { bool_value: a },
                ..
            },
            _rhs,
        ) => match bin_op {
            Implies => {
                if *a {
                    rhs
                } else {
                    Rc::new(Expression::TRUE)
                }
            }
            And => {
                if *a {
                    rhs
                } else {
                    Rc::new(Expression::FALSE)
                }
            }
            Or => {
                if *a {
                    Rc::new(Expression::TRUE)
                } else {
                    rhs
                }
            }
            _ => Rc::new(Expression::BinOp {
                bin_op,
                lhs,
                rhs,
                type_: RuntimeType::BoolRuntimeType,
                info: SourcePos::UnknownPosition,
            }),
        },
        (
            bin_op,
            _lhs,
            Lit {
                lit: BoolLit { bool_value: b },
                ..
            },
        ) => match bin_op {
            Implies => {
                if *b {
                    Rc::new(Expression::TRUE)
                } else {
                    negate(lhs).into()
                }
            }
            And => {
                if *b {
                    lhs
                } else {
                    Rc::new(Expression::FALSE)
                }
            }
            Or => {
                if *b {
                    Rc::new(Expression::TRUE)
                } else {
                    lhs
                }
            }
            _ => Rc::new(Expression::BinOp {
                bin_op,
                lhs,
                rhs,
                type_: RuntimeType::BoolRuntimeType,
                info: SourcePos::UnknownPosition,
            }),
        },
        // Integer evaluation
        (
            Divide | Modulo,
            _,
            Lit {
                lit: IntLit { int_value: 0 },
                ..
            },
        ) => panic!("infeasible, division/modulo by zero"),
        (
            bin_op,
            Lit {
                lit: IntLit { int_value: a },
                ..
            },
            Lit {
                lit: IntLit { int_value: b },
                ..
            },
        ) => match bin_op {
            Equal => Expression::bool(*a == *b),
            NotEqual => Expression::bool(*a != *b),
            LessThan => Expression::bool(*a < *b),
            LessThanEqual => Expression::bool(*a <= *b),
            GreaterThan => Expression::bool(*a > *b),
            GreaterThanEqual => Expression::bool(*a >= *b),
            Plus => Expression::int(*a + *b),
            Minus => Expression::int(*a - *b),
            Multiply => Expression::int(*a * *b),
            Divide => Expression::int(*a / *b),
            Modulo => Expression::int(*a % *b),
            _ => panic!("unsupported integer operator"),
        },
        (bin_op, Ref { ref_: a, .. }, Ref { ref_: b, .. }) => match bin_op {
            Equal => Expression::bool(*a == *b),
            NotEqual => Expression::bool(*a != *b),
            _ => panic!("unsupported ref operator"),
        },
        (bin_op, Ref { .. }, Lit { lit: NullLit, .. }) => match bin_op {
            Equal => Rc::new(Expression::FALSE),
            NotEqual => Rc::new(Expression::TRUE),
            _ => panic!("unsupported ref operator"),
        },
        (bin_op, Lit { lit: NullLit, .. }, Ref { .. }) => match bin_op {
            Equal => Rc::new(Expression::FALSE),
            NotEqual => Rc::new(Expression::TRUE),
            _ => panic!("unsupported ref operator"),
        },
        (bin_op, Lit { lit: NullLit, .. }, Lit { lit: NullLit, .. }) => match bin_op {
            Equal => Rc::new(Expression::TRUE),
            NotEqual => Rc::new(Expression::FALSE),
            _ => panic!("unsupported ref operator"),
        },
        (bin_op, SymbolicRef { var: a, .. }, SymbolicRef { var: b, .. }) => {
            if *a == *b {
                match bin_op {
                    Equal => Rc::new(Expression::TRUE),
                    NotEqual => Rc::new(Expression::FALSE),
                    _ => panic!("unsupported ref operator"),
                }
            } else {
                Rc::new(Expression::BinOp {
                    bin_op,
                    lhs,
                    rhs,
                    type_: RuntimeType::BoolRuntimeType,
                    info: SourcePos::UnknownPosition,
                })
            }
        }
        (bin_op, _, _) => Rc::new(Expression::BinOp {
            bin_op,
            lhs,
            rhs,
            type_: RuntimeType::BoolRuntimeType,
            info: SourcePos::UnknownPosition,
        }),
    }
}

fn evaluate_unop(unop: UnOp, expression: Rc<Expression>) -> Rc<Expression> {
    match (unop, expression.as_ref()) {
        (
            UnOp::Negative,
            Expression::Lit {
                lit: Lit::IntLit { int_value },
                ..
            },
        ) => Rc::new(Expression::Lit {
            lit: Lit::IntLit {
                int_value: -int_value,
            },
            type_: RuntimeType::IntRuntimeType,
            info: SourcePos::UnknownPosition,
        }),
        (
            UnOp::Negative,
            Expression::BinOp {
                bin_op: BinOp::Equal,
                lhs,
                rhs,
                ..
            },
        ) => evaluate_binop(BinOp::NotEqual, lhs.clone(), rhs.clone()).into(),
        (UnOp::Negative, _) => Rc::new(negative(expression)),
        (
            UnOp::Negate,
            Expression::Lit {
                lit: Lit::BoolLit { bool_value },
                ..
            },
        ) => Rc::new(Expression::Lit {
            lit: Lit::BoolLit {
                bool_value: !bool_value,
            },
            type_: RuntimeType::BoolRuntimeType,
            info: SourcePos::UnknownPosition,
        }),
        (UnOp::Negate, _) => Rc::new(negate(expression)),
    }
}

/// Turns a `forall` or an `exists` into an expression with chained binary operators
/// forall <elem>, <range> : <domain> : <formula>
/// For example the expression:
/// ```
/// "forall elem, index : a : elem > 0";
/// ```
/// becomes, when a = { 0, 1, 2 }
/// ```
/// "0 > 0 && 1 > 0 && 2 > 0";
/// ```
///
/// F is a function that chains each subexpression together with a binary operator into one expression.
fn evaluate_quantifier<'a, F>(
    quantifier: F,
    elem: &'a Identifier,
    range: &'a Identifier,
    domain: &'a Identifier,
    formula: Rc<Expression>,
    state: &'a mut State,
    en: &mut impl Engine,
) -> Rc<Expression>
where
    F: Fn(Vec<Rc<Expression>>) -> Rc<Expression>,
{
    let array = state.threads[&state.active_thread].stack.lookup(domain).unwrap();
    let array = evaluate(state, array, en);

    let array = single_alias_elimination(array, &state.alias_map);

    match array.as_ref() {
        Expression::Lit {
            lit: Lit::NullLit, ..
        } => Expression::FALSE.into(), // return false?
        Expression::Ref { ref_, .. } => {
            let len = if let heap::HeapValue::ArrayValue { elements, .. } =
                state.heap.get(ref_).unwrap()
            {
                elements.len()
            } else {
                panic!("expected Array object")
            };

            //
            let formulas = (0..len)
                .map(|i| {
                    let element = heap::get_element(i, *ref_, &state.heap);
                    let index = to_int_expr(i as i64);

                    state.threads.get_mut(&state.active_thread).unwrap().stack.insert_variable(elem.clone(), element);
                    state.threads.get_mut(&state.active_thread).unwrap().stack.insert_variable(range.clone(), index);
                    let value = evaluate(state, formula.clone(), en);
                    state.threads.get_mut(&state.active_thread).unwrap().stack.remove_variable(elem);
                    state.threads.get_mut(&state.active_thread).unwrap().stack.remove_variable(range);

                    value
                })
                .collect_vec();

            quantifier(formulas)
        }
        _ => unreachable!("Expected array to be a reference, found {:?}", array),
    }
}


