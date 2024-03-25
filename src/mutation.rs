//! Takes a syntax tree and outputs a list of syntax trees, each with one mutation.
//! A mutation is a small change in the source code, for example a change in comparison direction, `2 > 1` becomes `2 < 1`
//! A mutation should result in a type correct program
//!
//! Mutations can be used to verify software testing tools

use std::{collections::HashMap, ops::Deref};

use std::rc::Rc;

use itertools::{Either, Itertools};

use crate::{syntax::*, SourcePos};

type Environment = HashMap<Identifier, NonVoidType>;

/// A function that takes an A, returning T
/// T is usually a collection representing all mutated A.
type Mutator<A, T> = &'static dyn Fn(A) -> T;
type MutatorWithEnv<A, T> = &'static dyn Fn(A, &Environment) -> T;

#[derive(Copy, Clone)]
enum MutationOperator {
    StatementMutation(Mutator<Statement, Vec<Statement>>),
    VarMutation(MutatorWithEnv<Identifier, Vec<Identifier>>),
    LitMutation(Mutator<Lit, Vec<Lit>>),
    BinOpMutation(Mutator<BinOp, Vec<BinOp>>),
    UnOpMutation(Mutator<UnOp, Option<Vec<UnOp>>>),
}

#[rustfmt::skip]
fn operators() -> Vec<(&'static str, MutationOperator)> {
    use MutationOperator::*;
    use Statement::*;
    vec![
        (
            "del",
            StatementMutation(&|stat| {
                if deletable_stat(&stat) {
                    vec![Statement::Skip]
                } else {
                    vec![]
                }
            }),
        ),
        (
            "flow",
            StatementMutation(&|stat| match stat {
                Continue { .. } => vec![Break { info: crate::SourcePos::UnknownPosition  }],
                Break { .. } => vec![Continue { info: Default::default() }],
                _ => vec![],
            }),
        ),
        (
            "var",
            VarMutation(&|original_var, env| {
                let var_type = env[&original_var].clone();
                env.iter()
                    .filter(|(var, type_)| same_type(type_, &var_type) && **var != original_var)
                    .map(|(var, _)| var.clone()).collect()
            })
        ),
        (
            "lit",
            LitMutation(&|lit| match lit {
                Lit::IntLit { int_value }   => vec![ Lit::IntLit { int_value: int_value + 1 },
                                                     Lit::IntLit { int_value: int_value - 1 }],
                Lit::BoolLit { bool_value } => vec![Lit::BoolLit { bool_value: !bool_value }],
                _ => vec![]
            })
        ),
        (
            "eq",
            BinOpMutation(&|bin_op| match bin_op {
                BinOp::Equal    =>  vec![BinOp::NotEqual],
                BinOp::NotEqual =>  vec![BinOp::Equal],
                _ => vec![]
            })
        ),
        (
            "cmp",
            BinOpMutation(&|bin_op| match bin_op {
                BinOp::LessThan         =>  vec![BinOp::LessThanEqual, BinOp::GreaterThan, BinOp::GreaterThanEqual],
                BinOp::LessThanEqual    =>  vec![BinOp::LessThan, BinOp::GreaterThan, BinOp::GreaterThanEqual],
                BinOp::GreaterThan      =>  vec![BinOp::LessThan, BinOp::LessThanEqual, BinOp::GreaterThanEqual],
                BinOp::GreaterThanEqual =>  vec![BinOp::LessThan, BinOp::LessThanEqual, BinOp::GreaterThan],
                BinOp::NotEqual         =>  vec![BinOp::Equal],
                _ => vec![]
            })
        ),
        (
            "arith",
            BinOpMutation(&|bin_op| match bin_op {
                BinOp::Plus     => vec![BinOp::Minus, BinOp::Multiply, BinOp::Divide],
                BinOp::Minus    => vec![BinOp::Plus, BinOp::Multiply, BinOp::Divide, BinOp::Modulo],
                BinOp::Multiply => vec![BinOp::Plus, BinOp::Minus, BinOp::Divide, BinOp::Modulo],
                BinOp::Divide   => vec![BinOp::Plus, BinOp::Minus, BinOp::Multiply, BinOp::Modulo],
                BinOp::Modulo   => vec![BinOp::Plus, BinOp::Minus, BinOp::Multiply, BinOp::Divide],
                _ => vec![]
            })
        ),
        (   
            "bool",
            BinOpMutation(&|bin_op| match bin_op {
                BinOp::And      => vec![BinOp::Or, BinOp::Implies],
                BinOp::Or       => vec![BinOp::And, BinOp::Implies],
                BinOp::Implies  => vec![BinOp::And, BinOp::Or],
                _ => vec![]
            })
        ),
        (
            "un",
            UnOpMutation(&|un_op| match un_op {
                UnOp::Negative => None,
                UnOp::Negate => None,
            })
        )
    ]
}

pub fn mutate_program(compilation_unit: &CompilationUnit, exclude_methods: &[(Identifier, Identifier)]) -> Vec<(String, CompilationUnit)> {
    operators()
        .into_iter()
        .map(|(name, mutation)| {
            (0..)
                .zip(mutate_compilation_unit(mutation, compilation_unit, exclude_methods))
                .map(move |(i, compilation_unit)| (format!("{}{}", name, i), compilation_unit))
        })
        .flatten()
        .collect()
}

fn mutate_compilation_unit(
    mutation: MutationOperator,
    compilation_unit: &CompilationUnit,
    exclude_methods: &[(Identifier, Identifier)]
) -> Vec<CompilationUnit> {
    let mutated_members = mutate_declarations(mutation, &compilation_unit.members, exclude_methods);

    mutated_members
        .into_iter()
        .map(|members| CompilationUnit { members })
        .collect()
}

fn mutate_declarations(
    mutation: MutationOperator,
    declarations: &Vec<Declaration>,
    exclude_methods: &[(Identifier, Identifier)]
) -> Vec<Vec<Declaration>> {
    (0..)
        .zip(declarations)
        .map(|(i, decl)| {
            mutate_declaration(mutation, &decl, exclude_methods)
                .into_iter()
                .map(|declaration| {
                    let mut declarations = declarations.clone();
                    declarations[i] = declaration;
                    declarations
                })
                .collect_vec()
        })
        .flatten()
        .filter(|v| !v.is_empty())
        .collect()
}

fn mutate_declaration(mutation: MutationOperator, declaration: &Declaration, exclude_methods: &[(Identifier, Identifier)]) -> Vec<Declaration> {
    match declaration {
        Declaration::Class(class) => (0..)
            .zip(&class.members)
            .map(|(i, member)| {
                mutate_declaration_member(mutation, member, class.name.clone(), exclude_methods)
                    .into_iter()
                    .map(move |member| {
                        let mut members = class.members.clone();
                        members[i] = member;

                        // dbg!(&class.name);
                        // dbg!(&class.extends);
                        Declaration::Class(
                            Class {
                                members,
                                name: class.name.clone(),
                                extends: class.extends.clone(),
                                implements: class.implements.clone(),
                                info: Default::default(),
                            }
                            .into(),
                        )
                    })
            })
            .flatten()
            .collect(),
        Declaration::Interface(interface) => (0..)
            .zip(&interface.members)
            .map(|(i, member)| {
                mutate_interface_member(mutation, member, interface.name.clone(), exclude_methods)
                    .into_iter()
                    .map(move |member| {
                        let mut members = interface.members.clone();
                        members[i] = member;

                        Declaration::Interface(
                            Interface {
                                members,
                                name: interface.name.clone(),
                                extends: interface.extends.clone(),
                            }
                            .into(),
                        )
                    })
            })
            .flatten()
            .collect(),
    }
}

fn mutate_declaration_member(
    mutation: MutationOperator,
    member: &DeclarationMember,
    decl_name: Identifier,
    exclude_methods: &[(Identifier, Identifier)]
) -> Vec<DeclarationMember> {
    match member {
        DeclarationMember::Constructor(method) => mutate_method(mutation, method, decl_name, exclude_methods)
            .into_iter()
            .map(|method| DeclarationMember::Constructor(method))
            .collect(),
        DeclarationMember::Method(method) => mutate_method(mutation, method, decl_name, exclude_methods)
            .into_iter()
            .map(|method| DeclarationMember::Method(method))
            .collect(),
        DeclarationMember::Field { .. } => vec![],
    }
}

fn mutate_interface_member(
    mutation: MutationOperator,
    member: &InterfaceMember,
    decl_name: Identifier,
    exclude_methods: &[(Identifier, Identifier)]
) -> Vec<InterfaceMember> {
    match member {
        InterfaceMember::DefaultMethod(method) => mutate_method(mutation, method, decl_name, exclude_methods)
            .into_iter()
            .map(|method| InterfaceMember::DefaultMethod(method))
            .collect(),
        InterfaceMember::AbstractMethod(method) => {
            vec![InterfaceMember::AbstractMethod(method.clone())]
        }
    }
}

fn mutate_method(
    mutation: MutationOperator,
    method: &Method,
    decl_name: Identifier,
    exclude_methods: &[(Identifier, Identifier)]
) -> Vec<Rc<Method>> {
    if exclude_methods.contains(&(decl_name.clone(), method.name.clone())) {
        return vec![];
    }
    let mut env = Environment::new();
    env.insert(
        "this".into(),
        NonVoidType::ReferenceType {
            identifier: decl_name,
            info: Default::default(),
        },
    );
    env.extend(
        method
            .params
            .iter()
            .map(|param| (param.name.clone(), param.type_.clone())),
    );
    mutate_body(mutation, &method.body.borrow(), &mut env)
        .into_iter()
        .map(|body| {
            Method {
                body: body.into(),
                ..method.clone()
            }
            .into()
        })
        .collect()
}

fn mutate_expression(
    mutation: MutationOperator,
    expression: &Expression,
    env: &mut Environment,
) -> Vec<Expression> {
    let info = Default::default();
    match expression {
        Expression::BinOp {
            bin_op,
            lhs,
            rhs,
            type_,
            ..
        } => {
            let bin_ops =
                apply_binop(mutation, *bin_op)
                    .into_iter()
                    .map(|bin_op| Expression::BinOp {
                        bin_op,
                        lhs: lhs.clone(),
                        rhs: rhs.clone(),
                        type_: type_.clone(),
                        info,
                    });
            let lhss = mutate_expression(mutation, lhs, env)
                .into_iter()
                .map(|lhs| Expression::BinOp {
                    bin_op: *bin_op,
                    lhs: lhs.into(),
                    rhs: rhs.clone(),
                    type_: type_.clone(),
                    info,
                });
            let rhss = mutate_expression(mutation, rhs, env)
                .into_iter()
                .map(|rhs| Expression::BinOp {
                    bin_op: *bin_op,
                    lhs: lhs.clone(),
                    rhs: rhs.into(),
                    type_: type_.clone(),
                    info,
                });

            bin_ops.chain(lhss).chain(rhss).collect()
        }
        Expression::UnOp {
            un_op,
            value,
            type_,
            ..
        } => {
            let un_ops = apply_unop(mutation, *un_op)
                .into_iter()
                .flatten()
                .map(|un_op| Expression::UnOp {
                    un_op,
                    value: value.clone(),
                    type_: type_.clone(),
                    info,
                });
            let values = mutate_expression(mutation, value, env)
                .into_iter()
                .map(|value| Expression::UnOp {
                    un_op: *un_op,
                    value: value.into(),
                    type_: type_.clone(),
                    info,
                });
            un_ops.chain(values).collect()
        }
        Expression::Var { var, type_, .. } => apply_var(mutation, var.clone(), env)
            .into_iter()
            .map(|var| Expression::Var {
                var,
                type_: type_.clone(),
                info,
            })
            .collect(),
        Expression::Lit { lit, type_, .. } => {
            let lits = apply_lit(mutation, lit.clone())
                .into_iter()
                .map(|lit| Expression::Lit {
                    lit,
                    type_: type_.clone(),
                    info,
                });
            lits.collect()
        }
        Expression::SizeOf { var, type_, .. } => {
            let vars = apply_var(mutation, var.clone(), env)
                .into_iter()
                .map(|var| Expression::SizeOf {
                    var,
                    type_: type_.clone(),
                    info: info.clone(),
                });
            vars.collect()
        }
        Expression::Forall { .. } | Expression::Exists { .. } => vec![],
        Expression::Ref { .. }
        | Expression::SymbolicRef { .. }
        | Expression::SymbolicVar { .. }
        | Expression::Conditional { .. } => unreachable!("Cannot be reached during typing phase"),
    }
}

fn mutate_expressions(
    mutation: MutationOperator,
    expressions: &Vec<Rc<Expression>>,
    env: &mut Environment,
) -> Vec<Vec<Rc<Expression>>> {
    expressions
        .into_iter()
        .map(|expression| {
            mutate_expression(mutation, expression.deref(), env)
                .into_iter()
                .map(Rc::new)
                .collect()
        })
        .filter(|v: &Vec<_>| !v.is_empty())
        .collect()
}

fn mutate_maybe_expression(
    mutation: MutationOperator,
    expression: Option<&Expression>,
    env: &mut Environment,
) -> Vec<Expression> {
    if let Some(expression) = expression {
        mutate_expression(mutation, expression, env)
    } else {
        vec![]
    }
}

fn mutate_lhs(mutation: MutationOperator, lhs: &Lhs, env: &mut Environment) -> Vec<Lhs> {
    match lhs {
        Lhs::LhsVar { var, type_, info } => {
            let vars = apply_var(mutation, var.clone(), env)
                .into_iter()
                .map(|var| Lhs::LhsVar {
                    var,
                    type_: type_.clone(),
                    info: info.clone(),
                });
            vars.collect()
        }
        Lhs::LhsField {
            var,
            var_type,
            field,
            type_,
            info,
        } => {
            let fields = apply_var(mutation, var.clone(), env)
                .into_iter()
                .map(|var| Lhs::LhsField {
                    var,
                    field: field.clone(),
                    var_type: var_type.clone(),
                    type_: type_.clone(),
                    info: info.clone(),
                });
            fields.collect()
        }
        Lhs::LhsElem {
            var,
            index,
            type_,
            info,
        } => {
            let vars = apply_var(mutation, var.clone(), env)
                .into_iter()
                .map(|var| Lhs::LhsElem {
                    var,
                    type_: type_.clone(),
                    index: index.clone(),
                    info: info.clone(),
                });

            let indexes = mutate_expression(mutation, index, env)
                .into_iter()
                .map(|index| Lhs::LhsElem {
                    var: var.clone(),
                    type_: type_.clone(),
                    index: index.into(),
                    info: info.clone(),
                });
            vars.chain(indexes).collect()
        }
    }
}

fn mutate_rhs(mutation: MutationOperator, rhs: &Rhs, env: &mut Environment) -> Vec<Rhs> {
    let info: SourcePos = Default::default();
    match rhs {
        Rhs::RhsExpression { value, type_, .. } => mutate_expression(mutation, value, env)
            .into_iter()
            .map(|expr| Rhs::RhsExpression {
                value: expr.into(),
                type_: type_.clone(),
                info,
            })
            .collect(),
        Rhs::RhsField {
            var, field, type_, ..
        } => {
            let vars = mutate_expression(mutation, var, env)
                .into_iter()
                .map(|var| Rhs::RhsField {
                    var: var.into(),
                    field: field.clone(),
                    type_: type_.clone(),
                    info,
                });
            vars.collect()
        }
        Rhs::RhsElem {
            var, index, type_, ..
        } => {
            let vars = mutate_expression(mutation, var, env)
                .into_iter()
                .map(|var| Rhs::RhsElem {
                    var: var.into(),
                    type_: type_.clone(),
                    index: index.clone(),
                    info: info.clone(),
                });

            let indexes = mutate_expression(mutation, index, env)
                .into_iter()
                .map(|index| Rhs::RhsElem {
                    var: var.clone(),
                    type_: type_.clone(),
                    index: index.into(),
                    info: info.clone(),
                });
            vars.chain(indexes).collect()
        }
        Rhs::RhsCall {
            invocation, type_, ..
        } => {
            let invocations = mutate_invocation(mutation, invocation, env)
                .into_iter()
                .map(|invocation| Rhs::RhsCall {
                    invocation,
                    type_: type_.clone(),
                    info,
                });
            invocations.collect()
        }
        Rhs::RhsArray {
            array_type,
            sizes,
            type_,
            ..
        } => {
            let sizes = mutate_expressions(mutation, sizes, env)
                .into_iter()
                .map(|sizes| Rhs::RhsArray {
                    array_type: array_type.clone(),
                    sizes,
                    type_: type_.clone(),
                    info,
                });
            sizes.collect()
        }
        Rhs::RhsCast { cast_type, var, .. } => {
            let vars = apply_var(mutation, var.clone(), env)
                .into_iter()
                .map(|var| Rhs::RhsCast {
                    var: var.into(),
                    cast_type: cast_type.clone(),
                    info: info.clone(),
                });

            vars.collect()
        },
    }
}

fn mutate_invocation(
    mutation: MutationOperator,
    invocation: &Invocation,
    env: &mut Environment,
) -> Vec<Invocation> {
    let info = Default::default();
    match invocation {
        Invocation::InvokeMethod {
            lhs,
            rhs,
            arguments,
            resolved,
            ..
        } => {
            let arguments = mutate_expressions(mutation, arguments, env)
                .into_iter()
                .map(|arguments| Invocation::InvokeMethod {
                    lhs: lhs.clone(),
                    rhs: rhs.clone(),
                    arguments,
                    resolved: resolved.clone(),
                    info,
                });

            arguments.collect()
        }
        Invocation::InvokeConstructor {
            class_name,
            arguments,
            resolved,
            ..
        } => {
            let arguments = mutate_expressions(mutation, arguments, env)
                .into_iter()
                .map(|arguments| Invocation::InvokeConstructor {
                    class_name: class_name.clone(),
                    arguments,
                    resolved: resolved.clone(),
                    info,
                });

            arguments.collect()
        }
        Invocation::InvokeSuperMethod { .. } => vec![],
        Invocation::InvokeSuperConstructor { .. } => vec![],
    }
}

fn mutate_body(
    mutation: MutationOperator,
    statement: &Statement,
    env: &mut Environment,
) -> Vec<Statement> {
    let info = Default::default();

    match statement {
        Statement::While { guard, body, .. } => {
            // mutate guard.
            let guard_mutated = mutate_expression(mutation, guard, env)
                .into_iter()
                .map(|guard| Statement::While {
                    guard: guard.into(),
                    body: body.clone(),
                    info,
                });

            let bodies = mutate_body(mutation, body, env).into_iter().map(|body| {
                Statement::While {
                    guard: guard.clone(),
                    body: Box::new(body),
                    info,
                }
                .into()
            });

            guard_mutated.chain(bodies).collect()
        }
        Statement::Ite {
            guard,
            true_body,
            false_body,
            ..
        } => {
            // mutate guard.
            let guard_mutated = if let Either::Left(guard) = guard {
                mutate_expression(mutation, guard, env)
                    .into_iter()
                    .map(|guard| Statement::Ite {
                        guard: Either::Left(guard.into()),
                        true_body: true_body.clone(),
                        false_body: false_body.clone(),
                        info,
                    })
                    .collect()
            } else {
                vec![]
            };

            let true_bodies = mutate_body(mutation, true_body, &mut env.clone())
                .into_iter()
                .map(|body| {
                    Statement::Ite {
                        guard: guard.clone(),
                        true_body: Box::new(body),
                        false_body: false_body.clone(),
                        info: Default::default(),
                    }
                    .into()
                });
            let false_bodies = mutate_body(mutation, false_body, &mut env.clone())
                .into_iter()
                .map(|body| {
                    Statement::Ite {
                        guard: guard.clone(),
                        true_body: true_body.clone(),
                        false_body: Box::new(body),
                        info: Default::default(),
                    }
                    .into()
                });

            guard_mutated
                .into_iter()
                .chain(true_bodies)
                .chain(false_bodies)
                .collect()
        }
        Statement::Try {
            try_body,
            catch_body,
            ..
        } => {
            let try_bodies = mutate_body(mutation, try_body, &mut env.clone())
                .into_iter()
                .map(|body| {
                    Statement::Try {
                        try_body: Box::new(body),
                        catch_body: catch_body.clone(),
                        info: Default::default(),
                    }
                    .into()
                });
            let catch_bodies = mutate_body(mutation, catch_body, &mut env.clone())
                .into_iter()
                .map(|body| {
                    Statement::Try {
                        try_body: try_body.clone(),
                        catch_body: Box::new(body),
                        info: Default::default(),
                    }
                    .into()
                });

            try_bodies.chain(catch_bodies).collect()
        }
        Statement::Block { body } => mutate_body(mutation, body, &mut env.clone())
            .into_iter()
            .map(|body| Statement::Block {
                body: Box::new(body),
            })
            .collect(),
        Statement::Seq { stat1, stat2 } => {
            let stat1s =
                mutate_body(mutation, stat1, env)
                    .into_iter()
                    .map(|stat1| Statement::Seq {
                        stat1: Box::new(stat1),
                        stat2: stat2.clone(),
                    });
            let stat2s =
                mutate_body(mutation, stat2, env)
                    .into_iter()
                    .map(|stat2| Statement::Seq {
                        stat1: stat1.clone(),
                        stat2: Box::new(stat2),
                    });

            stat1s.chain(stat2s).collect_vec()
        }
        Statement::Declare { type_, var, .. } => {
            env.insert(var.clone(), type_.clone());
            apply_stat(mutation, statement.clone())
        }
        Statement::Assign { lhs, rhs, .. } => {
            let mutated_lhss =
                mutate_lhs(mutation, lhs, env)
                    .into_iter()
                    .map(|lhs| Statement::Assign {
                        lhs,
                        rhs: rhs.clone(),
                        info,
                    });
            let mutated_rhss =
                mutate_rhs(mutation, rhs, env)
                    .into_iter()
                    .map(|rhs| Statement::Assign {
                        lhs: lhs.clone(),
                        rhs,
                        info,
                    });

            let stats = apply_stat(mutation, statement.clone());

            mutated_lhss.chain(mutated_rhss).chain(stats).collect()
        }
        Statement::Call { invocation, .. } => {
            let mutated_invocations = mutate_invocation(mutation, invocation, env)
                .into_iter()
                .map(|invocation| Statement::Call { invocation, info });
            let stats = apply_stat(mutation, statement.clone());
            mutated_invocations.chain(stats).collect()
        },
        Statement::Fork { invocation, .. } => {
            let mutated_invocations = mutate_invocation(mutation, invocation, env)
                .into_iter()
                .map(|invocation| Statement::Fork { invocation, info });
            let stats = apply_stat(mutation, statement.clone());
            mutated_invocations.chain(stats).collect()
        },
        Statement::Lock { .. } => apply_stat(mutation, statement.clone()),
        Statement::Unlock { .. } => apply_stat(mutation, statement.clone()),
        Statement::Join {..} => apply_stat(mutation, statement.clone()),
        Statement::Skip => apply_stat(mutation, statement.clone()),
        Statement::Assert {
            assertion: _assertion,
            ..
        } => apply_stat(mutation, statement.clone()),
        Statement::Assume {
            assumption: _assumption,
            ..
        } => apply_stat(mutation, statement.clone()),
        Statement::Continue { .. } => apply_stat(mutation, statement.clone()),
        Statement::Break { .. } => apply_stat(mutation, statement.clone()),
        Statement::Return { expression, .. } => {
            let expressions = mutate_maybe_expression(mutation, expression.as_deref(), env)
                .into_iter()
                .map(|expression| Statement::Return {
                    expression: Some(expression.into()),
                    info,
                });

            let stats = apply_stat(mutation, statement.clone());
            expressions.chain(stats).collect()
        }
        Statement::Throw { .. } => apply_stat(mutation, statement.clone()),
    }
}

fn apply_stat(mutation: MutationOperator, statement: Statement) -> Vec<Statement> {
    if let MutationOperator::StatementMutation(mutator) = mutation {
        mutator(statement)
    } else {
        vec![]
    }
}

fn apply_var(
    mutation: MutationOperator,
    var: Identifier,
    env: &mut Environment,
) -> Vec<Identifier> {
    if let MutationOperator::VarMutation(mutator) = mutation {
        // dbg!(&env, &var);
        mutator(var, env)
    } else {
        vec![]
    }
}

fn apply_binop(mutation: MutationOperator, binop: BinOp) -> Vec<BinOp> {
    if let MutationOperator::BinOpMutation(mutator) = mutation {
        mutator(binop)
    } else {
        vec![]
    }
}

fn apply_unop(mutation: MutationOperator, unop: UnOp) -> Option<Vec<UnOp>> {
    if let MutationOperator::UnOpMutation(mutator) = mutation {
        mutator(unop)
    } else {
        None
    }
}

fn apply_lit(mutation: MutationOperator, lit: Lit) -> Vec<Lit> {
    if let MutationOperator::LitMutation(mutator) = mutation {
        mutator(lit)
    } else {
        vec![]
    }
}

// Helpers

fn deletable_stat(statement: &Statement) -> bool {
    match statement {
        Statement::Declare { .. } => false,
        Statement::Assign { .. } => true,
        Statement::Call { .. } => true,
        Statement::Fork { .. } => false,
        Statement::Lock { .. } => false,
        Statement::Unlock { .. } => false,
        Statement::Join { .. } => false,
        Statement::Skip { .. } => false,
        Statement::Assert { .. } => false,
        Statement::Assume { .. } => false,
        Statement::While { .. } => false,
        Statement::Ite { .. } => false,
        Statement::Continue { .. } => true,
        Statement::Break { .. } => true,
        Statement::Return { .. } => false,
        Statement::Throw { .. } => true,
        Statement::Try { .. } => false,
        Statement::Block { .. } => false,
        Statement::Seq { .. } => false,
    }
}

// the actual type mutation is checked during type checking, but we do a quick check here too.
fn same_type(t1: &NonVoidType, t2: &NonVoidType) -> bool {
    match (t1, t2) {
        (NonVoidType::UIntType { .. }, NonVoidType::UIntType { .. }) => true,
        (NonVoidType::IntType { .. }, NonVoidType::IntType { .. }) => true,
        (NonVoidType::FloatType { .. }, NonVoidType::FloatType { .. }) => true,
        (NonVoidType::BoolType { .. }, NonVoidType::BoolType { .. }) => true,
        (NonVoidType::StringType { .. }, NonVoidType::StringType { .. }) => true,
        (NonVoidType::CharType { .. }, NonVoidType::CharType { .. }) => true,
        (NonVoidType::ReferenceType { .. }, NonVoidType::ReferenceType { .. }) => true,
        (NonVoidType::ArrayType { .. }, NonVoidType::ArrayType { .. }) => true,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use crate::{parse_program, parser, tokens};

    use super::*;

    #[test]
    fn simple() {
        let program = "
        static void test() {
            int abc;
            v := 0;
            v := 0;
            int c;
            i := 1;
            x.fool(x);
        }
        ";
        let tokens = tokens(program, 0).unwrap();
        let method = parser::method(true).parse(&tokens).unwrap();
        let method = if let DeclarationMember::Method(method) = method {
            method
        } else {
            panic!()
        };

        let mutator = MutationOperator::StatementMutation(&|stat| {
            if deletable_stat(&stat) {
                vec![Statement::Skip]
            } else {
                vec![]
            }
        });

        let stats = mutate_method(mutator, &method, "SimpleClass".into(), &[]);
        println!("{}\n\n", method.body.borrow());
        for stat in stats {
            println!("{}\n\n", stat.body.borrow());
        }
    }

    #[test]
    fn compilation_unit() {
        let program = std::fs::read_to_string("./examples/simpleclass.oox").unwrap();
        let compilation_unit = parse_program(&program, 0, false).unwrap();

        let mutator = MutationOperator::StatementMutation(&|stat| {
            if deletable_stat(&stat) {
                vec![Statement::Skip]
            } else {
                vec![]
            }
        });

        let mutated_units = mutate_compilation_unit(mutator, &compilation_unit, &[]);
        // println!("{}\n\n", compilation_unit);
        for mutated_unit in mutated_units {
            println!("{}\n\n", mutated_unit);
        }
    }
}
