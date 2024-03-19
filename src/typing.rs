use std::rc::Rc;
/// Type analysis of an OOX abstract syntax tree
///
/// The input is an abstract syntax tree (CompilationUnit) with (most) of its types set to UnknownType.
/// If the program is type correct, each type in the syntax tree (without a type) is mapped to itself with a type.
/// If type incorrect, a TypeError is returned instead.
///
/// Also any method invocations in the bodies of the methods are resolved, by assigning a reference to the invoked method(s).
use std::collections::HashMap;

use itertools::Either;
use queues::IsQueue;
use queues::{queue, Queue};

use crate::{
    error::{self, unification_error},
    exec::constants::{retval, this_str},
    positioned::WithPosition,
    resolver,
    symbol_table::SymbolTable,
    syntax::*,
    typeable::Typeable,
};

type TypeError = String;

/// Checks whether typeable A is of type B, returning an error when this is not the case.
/// And an empty Ok result otherwise.
fn matches_type<A, B>(type1: A, type2: B, st: &SymbolTable) -> Result<(), TypeError>
where
    A: Typeable + WithPosition,
    B: Typeable,
{
    if !type1.is_of_type(type2.type_of(), st) {
        return Err(error::unification_error(
            type2.type_of(),
            type1.type_of(),
            type1.get_position(),
        ));
    }
    Ok(())
}

#[derive(Clone)]
struct TypeEnvironment {
    env: HashMap<Identifier, RuntimeType>,
}
impl TypeEnvironment {
    fn declare_var(&mut self, var: Identifier, type_: RuntimeType) -> Result<(), TypeError> {
        if let Some((previously_defined, _)) = self.env.get_key_value(&var) {
            return Err(error::shadowing(
                &var,
                previously_defined,
                var.get_position(),
            ));
        }
        self.env.insert(var, type_);
        Ok(())
    }

    fn declare_param(&mut self, param: &Parameter) -> Result<(), TypeError> {
        self.declare_var(param.name.clone(), param.type_.type_of())
    }

    fn get_var_type(&self, var: &Identifier) -> Result<RuntimeType, TypeError> {
        self.env
            .get(var)
            .cloned()
            .ok_or(error::undeclared_var(var, var.get_position()))
    }
}
pub fn type_compilation_unit(
    compilation_unit: CompilationUnit,
    st: &SymbolTable,
) -> Result<CompilationUnit, TypeError> {
    let members = compilation_unit
        .members
        .into_iter()
        .map(|member| type_declaration(member, st))
        .collect::<Result<_, _>>()?;

    Ok(CompilationUnit { members })
}

fn type_declaration(declaration: Declaration, st: &SymbolTable) -> Result<Declaration, TypeError> {
    match declaration {
        Declaration::Class(class) => {
            let mut env = TypeEnvironment {
                env: HashMap::new(),
            };

            for member in &class.members {
                type_member_class(class.clone(), member, &mut env, st)?;
            }

            Ok(Declaration::Class(class))
        }
        Declaration::Interface(interface) => {
            let mut env = TypeEnvironment {
                env: HashMap::new(),
            };
            for member in &interface.members {
                type_member_interface(interface.clone(), member, &mut env, st)?;
            }

            Ok(Declaration::Interface(interface))
        }
    }
}

/// Will modify the bodies of declaration members with types,
/// and resolves the method invocations
fn type_member_class(
    declaration: Rc<Class>,
    declaration_member: &DeclarationMember,
    env: &mut TypeEnvironment,
    st: &SymbolTable,
) -> Result<(), TypeError> {
    use DeclarationMember as DM;
    match declaration_member.clone() {
        DM::Field { .. } => Ok(()),
        DM::Constructor(method) | DM::Method(method) if !method.is_static => {
            let mut env = env.clone();
            env.declare_var(
                this_str(),
                RuntimeType::ReferenceRuntimeType {
                    type_: declaration.name.clone(),
                },
            )?;
            for param in &method.params {
                env.declare_param(param)?;
            }
            type_specification(
                declaration_member,
                method.specification.clone(),
                &mut env,
                st,
            )?;
            let is_constructor = declaration_member.is_constructor();
            let new_body = type_statement(
                method.body.borrow().clone(),
                is_constructor,
                method.clone(),
                &mut env,
                st,
                &Declaration::Class(declaration),
            )?;
            *method.body.borrow_mut() = new_body;

            Ok(())
        }
        DM::Method(method) => {
            // static method
            let mut env = env.clone();

            for param in &method.params {
                env.declare_param(param)?;
            }
            let is_constructor = false;
            let new_body = type_statement(
                method.body.borrow().clone(),
                is_constructor,
                method.clone(),
                &mut env,
                st,
                &Declaration::Class(declaration),
            )?;
            *method.body.borrow_mut() = new_body;

            Ok(())
        }
        DM::Constructor(_) => todo!(),
    }
}

fn type_member_interface(
    interface: Rc<Interface>,
    member: &InterfaceMember,
    env: &mut TypeEnvironment,
    st: &SymbolTable,
) -> Result<(), TypeError> {
    use InterfaceMember as IM;
    match member {
        IM::DefaultMethod(method) => {
            let mut env = env.clone();

            for param in &method.params {
                env.declare_param(param)?;
            }
            let is_constructor = false;
            let new_body = type_statement(
                method.body.borrow().clone(),
                is_constructor,
                method.clone(),
                &mut env,
                st,
                &Declaration::Interface(interface),
            )?;
            *method.body.borrow_mut() = new_body;
            Ok(())
        }
        IM::AbstractMethod(_) => Ok(()),
    }
}

fn type_specification(
    declaration_member: &DeclarationMember,
    mut specification: Specification,
    env: &mut TypeEnvironment,
    st: &SymbolTable,
) -> Result<Specification, TypeError> {
    if let Some((requires, type_guard)) = specification.requires.clone() {
        let requires = type_expression(requires, env, st)?;
        matches_type(requires.as_ref(), RuntimeType::BoolRuntimeType, st)?;
        if let Some(type_guard) = type_guard.as_ref() {
            matches_type(type_guard, RuntimeType::BoolRuntimeType, st)?;
        }
        specification.requires = Some((requires, type_guard));
    }

    if let Some((ensures, type_guard)) = specification.ensures.clone() {
        let method_type = declaration_member.type_of();
        if !method_type.is_of_type(RuntimeType::VoidRuntimeType, st) {
            let mut env = env.clone();

            env.declare_var(retval(), method_type)?;
            let ensures = type_expression(ensures, &mut env, st)?;
            matches_type(ensures.as_ref(), RuntimeType::BoolRuntimeType, st)?;
            if let Some(type_guard) = type_guard.as_ref() {
                matches_type(type_guard, RuntimeType::BoolRuntimeType, st)?;
            }
            specification.ensures = Some((ensures, type_guard));
        }
    }

    if let Some((exceptional, type_guard)) = specification.exceptional.clone() {
        let exceptional = type_expression(exceptional, env, st)?;
        matches_type(exceptional.as_ref(), RuntimeType::BoolRuntimeType, st)?;

        if let Some(type_guard) = type_guard.as_ref() {
            matches_type(type_guard, RuntimeType::BoolRuntimeType, st)?;
        }
        specification.exceptional = Some((exceptional, type_guard));
    }

    Ok(specification)
}

fn optional_type_expression(
    expression: Option<Rc<Expression>>,
    env: &mut TypeEnvironment,
    st: &SymbolTable,
) -> Result<Option<Rc<Expression>>, TypeError> {
    if let Some(expr) = expression {
        type_expression(expr, env, st).map(Some)
    } else {
        Ok(None)
    }
}
/// Takes a statement and gives it a type or returns an error if type incorrect.
/// This function has been implemented with a loop, the original implementation has deep recursion which results in stackoverflows.
fn type_statement(
    statement: Statement,
    is_constructor: bool,
    current_method: Rc<Method>,
    env: &mut TypeEnvironment,
    st: &SymbolTable,
    declaration: &Declaration,
) -> Result<Statement, TypeError> {
    let mut statements = Vec::new();
    let mut queue = queue![statement];

    while let Ok(next_statement) = queue.remove() {
        match next_statement {
            Statement::Seq { stat1, stat2 } => {
                queue.add(*stat1).unwrap(); // always successful according to docs
                queue.add(*stat2).unwrap();
            }
            Statement::Declare { type_, var, info } => {
                env.declare_var(var.clone(), type_.type_of())?;
                statements.push(Statement::Declare { type_, var, info });
            }
            Statement::Assign { lhs, rhs, info } => {
                let lhs = type_lhs(lhs, env, st)?;
                let rhs = type_rhs(rhs, env, st, declaration)?;
                matches_type(&rhs, &lhs, st)?;
                statements.push(Statement::Assign { lhs, rhs, info });
            }
            Statement::Call { invocation, info } => {
                let invocation = type_invocation(invocation, env, st, declaration)?;
                statements.push(Statement::Call { invocation, info });
            },
            Statement::Fork { invocation, info } => {
                let invocation = type_invocation(invocation, env, st, declaration)?;
                statements.push(Statement::Fork { invocation, info });
            },
            Statement::Skip => statements.push(Statement::Skip),
            Statement::Assert { assertion, info } => {
                let assertion = type_expression(assertion.into(), env, st)?;
                matches_type(assertion.as_ref(), RuntimeType::BoolRuntimeType, st)?;
                statements.push(Statement::Assert { assertion, info });
            }
            Statement::Assume { assumption, info } => {
                if let Either::Left(assumption) = &assumption {
                    let assumption = type_expression(assumption.clone(), env, st)?;
                    matches_type(assumption.as_ref(), RuntimeType::BoolRuntimeType, st)?;
                }
                statements.push(Statement::Assume { assumption, info });
            }
            Statement::While { guard, body, info } => {
                let guard = type_expression(guard.into(), env, st)?;
                matches_type(guard.as_ref(), RuntimeType::BoolRuntimeType, st)?;
                let mut env = env.clone();
                let body = type_statement(
                    *body,
                    is_constructor,
                    current_method.clone(),
                    &mut env,
                    st,
                    declaration,
                )?;
                statements.push(Statement::While {
                    guard,
                    body: Box::new(body),
                    info,
                });
            }
            Statement::Ite {
                guard,
                true_body,
                false_body,
                info,
            } => {
                let guard = match guard {
                    Either::Left(guard) => {
                        let guard = type_expression(guard.clone(), env, st)?;
                        matches_type(guard.as_ref(), RuntimeType::BoolRuntimeType, st)?;
                        Either::Left(guard)
                    }
                    type_guard => type_guard,
                };
                let mut true_env = env.clone();
                let mut false_env = env.clone();
                let true_body = type_statement(
                    *true_body,
                    is_constructor,
                    current_method.clone(),
                    &mut true_env,
                    st,
                    declaration,
                )?;
                let false_body = type_statement(
                    *false_body,
                    is_constructor,
                    current_method.clone(),
                    &mut false_env,
                    st,
                    declaration,
                )?;

                statements.push(Statement::Ite {
                    guard,
                    true_body: true_body.into(),
                    false_body: false_body.into(),
                    info,
                });
            }
            Statement::Continue { info } => statements.push(Statement::Continue { info }),
            Statement::Break { info } => statements.push(Statement::Break { info }),
            Statement::Return { expression, info } => match (is_constructor, expression) {
                (true, Some(return_value)) => {
                    return Err(error::unexpected_return_value(&return_value, info))
                }
                (true, None) => {
                    let this_type = current_method.type_of();
                    let this = this_str();
                    let this_var = Expression::Var {
                        var: this,
                        type_: this_type,
                        info: current_method.get_position(),
                    };
                    statements.push(Statement::Return {
                        expression: Some(Rc::new(this_var)),
                        info,
                    })
                }
                (false, Some(return_value)) => {
                    let return_value = type_expression(return_value.into(), env, st)?;
                    matches_type(return_value.as_ref(), current_method.type_of(), st)?;
                    statements.push(Statement::Return {
                        expression: Some(return_value),
                        info,
                    })
                }
                (false, None) => {
                    if !current_method.is_of_type(RuntimeType::VoidRuntimeType, st) {
                        return Err(error::expected_return_value_error(
                            current_method.type_of(),
                            info,
                        ));
                    } else {
                        statements.push(Statement::Return {
                            expression: None,
                            info,
                        })
                    }
                }
            },
            Statement::Throw { message, info } => {
                statements.push(Statement::Throw { message, info })
            }
            Statement::Try {
                try_body,
                catch_body,
                info,
            } => {
                let mut try_env = env.clone();
                let try_body = type_statement(
                    *try_body,
                    is_constructor,
                    current_method.clone(),
                    &mut try_env,
                    st,
                    declaration,
                )?;
                let mut catch_env = env.clone();
                let catch_body = type_statement(
                    *catch_body,
                    is_constructor,
                    current_method.clone(),
                    &mut catch_env,
                    st,
                    declaration,
                )?;
                statements.push(Statement::Try {
                    try_body: Box::new(try_body),
                    catch_body: Box::new(catch_body),
                    info,
                })
            }
            Statement::Block { body } => {
                let body = type_statement(
                    *body,
                    is_constructor,
                    current_method.clone(),
                    env,
                    st,
                    declaration,
                )?;
                statements.push(Statement::Block {
                    body: Box::new(body),
                })
            }
        };
    }
    // Turn the array of Statements back into the Linked 'Seq' statement.
    statements
        .into_iter()
        .rev()
        .reduce(|acc, s| Statement::Seq {
            stat1: Box::new(s),
            stat2: Box::new(acc),
        })
        .ok_or("Expected at least one statement in the body".to_owned())
}

fn type_lhs(lhs: Lhs, env: &mut TypeEnvironment, st: &SymbolTable) -> Result<Lhs, TypeError> {
    match lhs {
        Lhs::LhsVar { var, info, .. } => {
            let type_ = env.get_var_type(&var)?;
            Ok(Lhs::LhsVar { var, type_, info })
        }
        Lhs::LhsField {
            var, field, info, ..
        } => {
            let var_type = env.get_var_type(&var)?;
            let class_name = var_type.get_reference_type().ok_or_else(|| {
                error::unification_error(RuntimeType::REFRuntimeType, var_type.clone(), info)
            })?;

            // something's going to need to be changed here due to inheritance of fields
            if let Some((_, field_type)) = st.lookup_field(&class_name, &field)? {
                Ok(Lhs::LhsField {
                    var,
                    var_type,
                    field,
                    type_: field_type.type_of(),
                    info,
                })
            } else {
                Err(error::unresolved_field_error(&class_name, &field, info))
            }
        }
        Lhs::LhsElem {
            var, index, info, ..
        } => {
            let type_ = env.get_var_type(&var)?;
            let inner_type = type_.get_inner_array_type().ok_or_else(|| {
                error::unification_error(RuntimeType::ARRAYRuntimeType, type_.clone(), info)
            })?;
            let index = type_expression(index, env, st)?;
            matches_type(index.as_ref(), RuntimeType::IntRuntimeType, st)?;
            Ok(Lhs::LhsElem {
                var,
                index: index.into(),
                type_: inner_type,
                info,
            })
        }
    }
}

fn type_rhs(
    rhs: Rhs,
    env: &mut TypeEnvironment,
    st: &SymbolTable,
    declaration: &Declaration,
) -> Result<Rhs, TypeError> {
    match rhs {
        Rhs::RhsExpression { value, info, .. } => {
            let expr = type_expression(value.into(), env, st)?;
            let type_ = expr.type_of();
            Ok(Rhs::RhsExpression {
                value: expr,
                type_,
                info,
            })
        }
        Rhs::RhsField {
            var, field, info, ..
        } => {
            let var = type_expression(var.into(), env, st)?;
            let var_type = var.type_of();
            let class_name = var_type.as_reference_type().ok_or_else(|| {
                error::unification_error(RuntimeType::REFRuntimeType, var_type.clone(), info)
            })?;
            if let Some((_, field_type)) = st.lookup_field(class_name, &field)? {
                Ok(Rhs::RhsField {
                    var,
                    field,
                    type_: field_type.type_of(),
                    info,
                })
            } else {
                Err(error::unresolved_field_error(class_name, &field, info))
            }
        }
        Rhs::RhsElem {
            var, index, info, ..
        } => {
            let var = type_expression(var.into(), env, st)?;
            let var_type = var.type_of();
            let inner_type = var_type.get_inner_array_type().ok_or_else(|| {
                error::unification_error(RuntimeType::ARRAYRuntimeType, var_type.clone(), info)
            })?;
            let index = type_expression(index.into(), env, st)?;
            matches_type(index.as_ref(), RuntimeType::IntRuntimeType, st)?;
            Ok(Rhs::RhsElem {
                var,
                index,
                type_: inner_type,
                info,
            })
        }
        Rhs::RhsCall {
            invocation, info, ..
        } => {
            let invocation = type_invocation(invocation, env, st, declaration)?;
            let type_ = invocation.type_of();
            Ok(Rhs::RhsCall {
                invocation,
                type_,
                info,
            })
        }
        Rhs::RhsArray {
            array_type,
            sizes,
            info,
            ..
        } => {
            let sizes = sizes
                .into_iter()
                .map(|size_expr| type_expression(size_expr, env, st))
                .collect::<Result<Vec<_>, _>>()?;

            for size in sizes.iter() {
                matches_type(size.as_ref(), RuntimeType::IntRuntimeType, st)?;
            }
            let type_ =
                sizes
                    .iter()
                    .fold(array_type.type_of(), |a, _| RuntimeType::ArrayRuntimeType {
                        inner_type: Box::new(a),
                    });

            Ok(Rhs::RhsArray {
                array_type,
                sizes,
                type_,
                info,
            })
        }
        Rhs::RhsCast {
            cast_type,
            var,
            info,
        } => {
            let var_type = env.get_var_type(&var)?;
            matches_type(cast_type.clone(), var_type, st)?;
            Ok(Rhs::RhsCast {
                cast_type,
                var,
                info,
            })
        }
    }
}

fn type_invocation(
    invocation: Invocation,
    env: &mut TypeEnvironment,
    st: &SymbolTable,
    declaration: &Declaration,
) -> Result<Invocation, TypeError> {
    match invocation {
        Invocation::InvokeMethod {
            lhs,
            rhs,
            arguments,
            info,
            ..
        } => {
            let arguments = arguments
                .into_iter()
                .map(|arg| type_expression(arg, env, st))
                .collect::<Result<Vec<_>, _>>()?;
            // if lhs is not found as a variable, assume this is a static invocation.
            let lhs_type = env.get_var_type(&lhs).ok();
            // if lhs is non-static, add the class type to the argument list, due to the implicit 'this' argument.
            let _argument_types = {
                let mut arg_types = lhs_type
                    .as_ref()
                    .map_or(Vec::new(), |lhs_type| vec![lhs_type.clone()]);
                arg_types.extend(arguments.iter().map(AsRef::as_ref).map(Typeable::type_of));
                arg_types
            }; // argument types can be used when we support multiple methods with the same name, currently argument types are not checked.

            let class_name = lhs_type
                .as_ref()
                .and_then(|t| t.as_reference_type())
                .unwrap_or(&lhs);

            let resolved = resolver::resolve_method(class_name, &rhs, st)?;

            if resolved.is_empty() {
                return Err(error::could_not_resolve_method(class_name, &rhs, info));
            }

            Ok(Invocation::InvokeMethod {
                lhs,
                rhs,
                arguments,
                resolved: Some(resolved),
                info,
            })
        }
        Invocation::InvokeSuperMethod {
            rhs,
            arguments,
            info,
            ..
        } => {
            let class_name = declaration.name();
            let resolved = resolver::resolve_super_method(class_name, &rhs, st)?;

            Ok(Invocation::InvokeSuperMethod {
                rhs,
                arguments,
                resolved: Some(resolved),
                info,
            })
        }
        Invocation::InvokeConstructor {
            class_name,
            arguments,
            info,
            ..
        } => {
            let arguments = arguments
                .into_iter()
                .map(|arg| type_expression(arg, env, st))
                .collect::<Result<Vec<_>, _>>()?;
            let resolved = resolver::resolve_constructor(&class_name, &arguments, st)?;
            Ok(Invocation::InvokeConstructor {
                class_name,
                arguments,
                resolved: Some(resolved),
                info,
            })
        }
        Invocation::InvokeSuperConstructor {
            arguments, info, ..
        } => {
            let arguments = arguments
                .into_iter()
                .map(|arg| type_expression(arg, env, st))
                .collect::<Result<Vec<_>, _>>()?;
            let class_name = declaration.name();
            let resolved = resolver::resolve_super_constructor(class_name, arguments.as_ref(), st)?;
            Ok(Invocation::InvokeSuperConstructor {
                arguments,
                resolved: Some(resolved),
                info,
            })
        }
    }
}

/// Verifies the types in given expression, returning an expression with the types set correctly
/// or an error if the expression is type incorrect.
fn type_expression(
    expression: Rc<Expression>,
    env: &mut TypeEnvironment,
    st: &SymbolTable,
) -> Result<Rc<Expression>, TypeError> {
    let expr = match expression.as_ref().clone() {
        Expression::Forall {
            elem,
            range,
            domain,
            formula,
            info,
            ..
        } => {
            let array = env.get_var_type(&domain)?;
            let inner_type = array.get_inner_array_type().ok_or(unification_error(
                RuntimeType::ARRAYRuntimeType,
                array,
                info,
            ))?;
            let mut env = env.clone();

            env.declare_var(elem.clone(), inner_type)?;
            env.declare_var(range.clone(), RuntimeType::IntRuntimeType)?;
            let formula = type_expression(formula.into(), &mut env, st)?;
            matches_type(formula.as_ref(), RuntimeType::BoolRuntimeType, st)?;

            Expression::Forall {
                type_: RuntimeType::BoolRuntimeType,
                elem,
                range,
                domain,
                formula,
                info,
            }
        }
        Expression::Exists {
            elem,
            range,
            domain,
            formula,
            info,
            ..
        } => {
            let array = env.get_var_type(&domain)?;
            let inner_type = array.get_inner_array_type().ok_or(unification_error(
                RuntimeType::ARRAYRuntimeType,
                array,
                info,
            ))?;
            let mut env = env.clone();

            env.declare_var(elem.clone(), inner_type)?;
            env.declare_var(range.clone(), RuntimeType::IntRuntimeType)?;
            let formula = type_expression(formula.into(), &mut env, st)?;
            matches_type(formula.as_ref(), RuntimeType::BoolRuntimeType, st)?;

            Expression::Exists {
                type_: RuntimeType::BoolRuntimeType,
                elem,
                range,
                domain,
                formula,
                info,
            }
        }
        Expression::BinOp {
            bin_op,
            lhs,
            rhs,
            info,
            ..
        } => {
            let lhs = type_expression(lhs, env, st)?;
            let rhs = type_expression(rhs, env, st)?;
            let type_ = type_binop(bin_op, &lhs, &rhs, st)?;
            Expression::BinOp {
                bin_op,
                lhs: lhs.into(),
                rhs: rhs.into(),
                type_,
                info,
            }
        }
        Expression::UnOp {
            un_op, value, info, ..
        } => {
            let value = type_expression(value, env, st)?;
            let type_ = match un_op {
                UnOp::Negative => {
                    matches_type(value.as_ref(), RuntimeType::NUMRuntimeType, st)?;
                    value.type_of()
                }
                UnOp::Negate => {
                    matches_type(value.as_ref(), RuntimeType::BoolRuntimeType, st)?;
                    RuntimeType::BoolRuntimeType
                }
            };
            Expression::UnOp {
                un_op,
                value: value.into(),
                type_,
                info,
            }
        }
        Expression::Var { var, info, .. } => {
            let type_ = env.get_var_type(&var)?;
            Expression::Var { var, type_, info }
        }
        Expression::SymbolicVar { .. } => unreachable!("Symbolic variable in analysis phase"),
        Expression::Lit { lit, info, .. } => {
            let type_ = lit.type_of();
            Expression::Lit { lit, type_, info }
        }
        Expression::SizeOf { var, info, .. } => {
            let type_ = env.get_var_type(&var)?;
            let var_expr = Expression::Var { var: var.clone(), type_, info: info };
            matches_type(var_expr, RuntimeType::ARRAYRuntimeType, st)?;
            Expression::SizeOf {
                var,
                type_: RuntimeType::IntRuntimeType,
                info,
            }
        },
        Expression::Ref { ref_, info, .. } => Expression::Ref {
            ref_,
            type_: RuntimeType::REFRuntimeType,
            info,
        },
        Expression::SymbolicRef { .. } => unreachable!("Symbolic object in analysis phase"),
        Expression::Conditional { .. } => unreachable!("Ite in analysis phase"),
        // instance_of@Expression::InstanceOf { .. } => instance_of,
    };
    Ok(expr.into())
}

/// Assumes exp1 and exp2 already have been typechecked.
fn type_binop(
    binop: BinOp,
    exp1: &Expression,
    exp2: &Expression,
    st: &SymbolTable,
) -> Result<RuntimeType, TypeError> {
    use BinOp::*;
    if [Implies, And, Or].contains(&binop) {
        matches_type(exp1, RuntimeType::BoolRuntimeType, st)?;
        matches_type(exp2, RuntimeType::BoolRuntimeType, st)?;
        Ok(RuntimeType::BoolRuntimeType)
    } else if [Equal, NotEqual].contains(&binop) {
        matches_type(exp1, exp2, st)?;
        Ok(RuntimeType::BoolRuntimeType)
    } else if [LessThan, LessThanEqual, GreaterThan, GreaterThanEqual].contains(&binop) {
        matches_type(exp1, RuntimeType::NUMRuntimeType, st)?;
        matches_type(exp2, RuntimeType::NUMRuntimeType, st)?;
        Ok(RuntimeType::BoolRuntimeType)
    } else if [Plus, Minus, Multiply, Divide, Modulo].contains(&binop) {
        let type_of = exp1.type_of();
        matches_type(exp1, RuntimeType::NUMRuntimeType, st)?;
        matches_type(exp2, RuntimeType::NUMRuntimeType, st)?;
        Ok(type_of)
    } else {
        unreachable!("missing case in type_binop")
    }
}
