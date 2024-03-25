use std::{cell::RefCell, collections::{HashMap, HashSet, VecDeque}, ops::AddAssign, rc::Rc, vec};

use clap::ValueEnum;
use im_rc::{vector, HashMap as ImHashMap, HashSet as ImHashSet};
use itertools::{Either, Itertools};
use num::One;
use slog::{debug, error, info, o, Logger};
use sloggers::{file::FileLoggerBuilder, types::Severity, Build};
use z3::SatResult;

use std::fmt::Debug;

pub(crate) mod alias_map;
mod array;
pub(crate) mod constants;
pub(crate) mod heap;
mod heuristics;
mod invocation;
mod fork;
mod mpor;
mod locks;
mod state_split;

use crate::{
    cfg::{labelled_statements, CFGStatement, MethodIdentifier},
    concretization::{concretizations, find_symbolic_refs},
    dsl::{and, equal, ite, negate, to_int_expr},
    exception_handler::{ExceptionHandlerEntry, ExceptionHandlerStack},
    exec::{
        eval::{evaluate, evaluate_as_int}, fork::fork_invocation, invocation::InvocationContext
    },
    insert_exceptional_clauses, language, parse_program,
    positioned::{SourcePos, WithPosition},
    prettyprint::cfg_pretty::pretty_print_compilation_unit,
    reachability::reachability,
    stack::{Stack, StackFrame},
    statistics::Statistics,
    symbol_table::SymbolTable,
    syntax::{
        BinOp, Declaration, Expression, Identifier, Invocation, Lhs, Lit, Method, NonVoidType,
        Parameter, Reference, Rhs, RuntimeType, Statement,
    },
    typeable::Typeable,
    typing::type_compilation_unit,
    utils, z3_checker, CompilationUnit, TypeExpr, FILE_NAMES,
};

use alias_map::*;
use array::*;
use heap::*;
mod eval;

use crate::exec::state_split::exec_array_initialisation;

type PathConstraints = ImHashSet<Rc<Expression>>;

enum Output {
    Valid,
    Invalid,
    Unknown,
}

/// A type to provide fresh id values (numerical).
/// Useful for generating new ids (addresses) for heap values
/// or generating new path ids when paths split.
#[derive(Debug, Clone)]
pub struct IdCounter<T> {
    last_value: T,
}

impl<T> IdCounter<T>
where
    T: AddAssign + One + Clone,
{
    fn new(initial: T) -> IdCounter<T> {
        IdCounter {
            last_value: initial,
        }
    }

    fn next_id(&mut self) -> T {
        self.last_value += T::one();
        self.last_value.clone()
    }

    fn current_value(&self) -> T {
        self.last_value.clone()
    }
}

#[derive(Debug, Clone)]
pub enum Access {
    FieldWrite(HashSet<Reference>, Identifier),
    FieldRead(HashSet<Reference>, Identifier), 
    ElemWrite(HashSet<Reference>, Rc<Expression>),
    ElemRead(HashSet<Reference>, Rc<Expression>),
    LockAction(HashSet<Reference>),
    FinishedThread(Vec<u64>),
    Join(u64)
}

#[derive(Debug, Clone, PartialEq)]
pub enum ThreadState {
    Enabled,
    Disabled,
    Finished
}

#[derive(Clone, Debug)]
pub struct Thread {
    tid: u64,
    pc: u64,
    pub state: ThreadState,
    pub parents: Vec<u64>,
    pub prev_accesses: Option<Vec<Access>>,
    pub stack: Stack,
}

/// The state of a path.
#[derive(Clone)]
pub struct State {
    /// The current 'program counter' this state is at in the control flow graph
    pub active_thread: u64,
    pub threads: HashMap<u64, Thread>,
    pub thread_counter: IdCounter<u64>,
    pub lock_requests: HashMap<Reference, VecDeque<u64>>,

    pub heap: Heap,

    constraints: PathConstraints,
    pub alias_map: AliasMap,
    pub ref_counter: IdCounter<i64>,
    exception_handler: ExceptionHandlerStack,

    // logger and other (non-functional) metrics
    pub logger: Logger,
    path: Vec<(u64, u64)>,
    path_length: u64,
    path_id: u64,
}

impl Debug for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("State")
            .field("pc", &self.threads[&self.active_thread].pc)
            .field("active_thread", &self.active_thread)
            .field("threads", &self.threads)
            // .field("heap", &self.heap)
            // .field("precondition", &self.precondition)
            // .field("constraints", &self.constraints)
            // .field("alias_map", &self.alias_map)
            // .field("ref_counter", &self.ref_counter)
            // .field("exception_handler", &self.exception_handler)
            .field("logger", &self.logger)
            .field("path_length", &self.path_length)
            .field("path_id", &self.path_id)
            .finish()
    }
}

impl State {
    fn next_reference_id(&mut self) -> Reference {
        self.ref_counter.next_id()
    }

    /// Create a copy from this state, 'state splitting'
    /// path_id is for the new state to reflect that this is a new path.
    fn new_state(&self, path_counter: &mut IdCounter<u64>) -> State {
        let mut new_state = self.clone();
        new_state.path_id = path_counter.next_id();
        new_state
    }

    /// allocates structure on heap, returning a reference to the value.
    fn allocate_on_heap(&mut self, structure: HeapValue) -> Rc<Expression> {
        let ref_fresh = self.next_reference_id();
        let type_ = structure.type_of();

        self.heap.insert(ref_fresh, structure);
        Rc::new(Expression::Ref {
            ref_: ref_fresh,
            type_,
            info: SourcePos::UnknownPosition,
        })
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum SymResult {
    Valid,
    Invalid(SourcePos),
}

/// A trait providing a way to add new states resulting from state splitting to a backlog.
///
/// Also serves as a context, providing easy access to other used types.
pub trait Engine {
    fn add_remaining_state(&mut self, state: State);

    fn add_remaining_states(&mut self, state: impl Iterator<Item = State>);

    /// Provides a unique path id, can be used when the state is split into a new path
    fn next_path_id(&mut self) -> u64;

    fn statistics(&mut self) -> &mut Statistics;

    fn symbol_table(&self) -> &SymbolTable;

    /// The root logger, without path id appended to each log.
    fn root_logger(&self) -> &Logger;

    /// Creates a new logger for the given path id.
    /// This path id will be appended to each log on that state.
    fn new_logger(&self, path_id: u64) -> Logger {
        self.root_logger().new(o!("path_id" => path_id))
    }

    /// Clones the state, with a new unique path_id
    fn clone_state_with_new_path_id(&mut self, state: &State) -> State {
        let mut new_state = state.clone();
        new_state.path_id = self.next_path_id();
        new_state.logger = self.new_logger(new_state.path_id);
        new_state
    }

    fn options(&self) -> &Options;
}

pub struct EngineContext<'a> {
    /// Any other states that must be executed in this step.
    /// In heuristics which steps over multiple states at once this will contain multiple states.
    /// Any states resulting from state-splitting on the same program point are also added to this list, see [`state_split`]
    ///
    /// When it is empty, the step is completed.
    remaining_states: &'a mut Vec<State>,

    path_counter: Rc<RefCell<IdCounter<u64>>>,
    statistics: &'a mut Statistics,
    st: &'a SymbolTable,
    root_logger: &'a Logger,
    options: &'a Options<'a>,
}

impl Engine for EngineContext<'_> {
    /// Add more states to this step, must be at the same program point
    fn add_remaining_state(&mut self, state: State) {
        self.remaining_states.push(state);
    }

    fn add_remaining_states(&mut self, states: impl Iterator<Item = State>) {
        self.remaining_states.extend(states);
    }

    fn next_path_id(&mut self) -> u64 {
        self.path_counter.borrow_mut().next_id()
    }

    fn statistics(&mut self) -> &mut Statistics {
        self.statistics
    }

    fn symbol_table(&self) -> &SymbolTable {
        self.st
    }

    fn root_logger(&self) -> &Logger {
        self.root_logger
    }

    fn options(&self) -> &Options {
        self.options
    }
}

enum ActionResult {
    /// Statement executed, continue
    Continue,
    Return(u64),
    FunctionCall(u64),
    InvalidFork(SourcePos),
    InvalidAssertion(SourcePos),
    InfeasiblePath,
    Finish,
}

/// Execute one statement for one state
fn action(
    state: &mut State,
    program: &HashMap<u64, CFGStatement>,
    en: &mut impl Engine,
) -> ActionResult {
    let pc = state.threads.get_mut(&state.active_thread).unwrap().pc;
    let action = &program[&pc];

    //use language::prettyprint::cfg_pretty;

    debug!(state.logger, "Action {}", action;
     "stack" => ?state.threads.get_mut(&state.active_thread).unwrap().stack.current_stackframe(),
     "heap" => ?state.heap,
     "alias_map" => ?state.alias_map
    //  "constraints" => ?state.constraints,
    );

    match action {
        CFGStatement::Statement(Statement::Declare { type_, var, .. }) => {
            state.threads.get_mut(&state.active_thread).unwrap()
                .stack
                .insert_variable(var.clone(), Rc::new(type_.default()));

            ActionResult::Continue
        }
        CFGStatement::Statement(Statement::Assign { lhs, rhs, .. }) => {
            // RhsCall 'x.foo()' has a special case,
            // others are handled in evaluateRhs
            if let Rhs::RhsCall { invocation, .. } = rhs {
                // if rhs contains an invocation.
                return exec_invocation(
                    state,
                    InvocationContext {
                        invocation,
                        program,
                        return_point: pc,
                        lhs: Some(lhs.clone()),
                    },
                    en,
                );
            }
            let value = evaluate_rhs(state, rhs, en);
            let e = evaluate(state, value, en);

            execute_assign(state, lhs, e, en);

            ActionResult::Continue
        }
        CFGStatement::Statement(Statement::Assert { assertion, .. }) => {
            let expression = prepare_assert_expression(state, assertion.clone(), en);

            let is_valid = eval_assertion(state, expression, en);
            if !is_valid {
                return ActionResult::InvalidAssertion(assertion.get_position());
            }
            ActionResult::Continue
        }
        CFGStatement::Statement(Statement::Assume { assumption, .. }) => {
            let is_feasible_path = exec_assume(state, assumption.clone(), en);
            if !is_feasible_path {
                return ActionResult::InfeasiblePath;
            }
            ActionResult::Continue
        }
        CFGStatement::Statement(Statement::Return { expression, .. }) => {
            if let Some(expression) = expression {
                let expression = evaluate(state, expression.clone(), en);
                state.threads.get_mut(&state.active_thread).unwrap().stack.insert_variable(constants::retval(), expression);
            }
            ActionResult::Continue
        }
        CFGStatement::FunctionEntry { .. } => {
            let StackFrame { current_member, .. } = state.threads.get_mut(&state.active_thread).unwrap().stack.current_stackframe().unwrap();
            if let Some((requires, type_guard)) = current_member.requires() {
                // if this is the program entry, assume that `requires(..)` is true, otherwise assert it.
                if state.path_length == 0 {
                    // First check the normal expression
                    let expression = evaluate(state, requires, en);
                    if *expression == Expression::FALSE {
                        debug!(state.logger, "Constraint is infeasible");
                        return ActionResult::InfeasiblePath;
                    } else if *expression != Expression::TRUE {
                        state.constraints.insert(expression);
                    }
                    // Also check the type guard expression if available.
                    // Note these are separated from the normal expression
                    // since there is currently only simple instanceof support.
                    if let Some(type_guard) = type_guard {
                        let feasible = assume_type_guard(state, &type_guard, en);
                        if !feasible {
                            return ActionResult::InfeasiblePath;
                        }
                    }
                } else {
                    // Assert that requires is true
                    let evaluated_requires = evaluate(state, requires.clone(), en);
                    let assertion =
                        prepare_assert_expression(state, evaluated_requires.clone(), en);
                    let is_valid = eval_assertion(state, assertion, en);
                    if !is_valid {
                        return ActionResult::InvalidAssertion(requires.get_position());
                    }
                    state.constraints.insert(evaluated_requires);

                    // Also assert the type guard expression if available.
                    if let Some(type_guard) = type_guard.as_ref() {
                        let all_of_type = assert_type_guard(state, type_guard, en);
                        if !all_of_type {
                            return ActionResult::InvalidAssertion(type_guard.get_position());
                        }
                    }
                }
            }

            ActionResult::Continue
        }
        CFGStatement::FunctionExit { .. } => {
            state.exception_handler.decrement_handler();

            let StackFrame { current_member, .. } = state.threads.get_mut(&state.active_thread).unwrap().stack.current_stackframe().unwrap();
            if let Some((post_condition, type_guard)) = current_member.post_condition() {
                let expression = prepare_assert_expression(state, post_condition.clone(), en);
                let is_valid = eval_assertion(state, expression, en);
                if !is_valid {
                    // postcondition invalid
                    return ActionResult::InvalidAssertion(post_condition.get_position());
                }
                if let Some(type_guard) = type_guard.as_ref() {
                    let all_of_type = assert_type_guard(state, type_guard, en);
                    if !all_of_type {
                        return ActionResult::InvalidAssertion(type_guard.get_position());
                    }
                }
            }
            if state.threads.get_mut(&state.active_thread).unwrap().stack.len() == 1 {
                ActionResult::Continue
            } else {
                let StackFrame {
                    returning_lhs,
                    params,
                    current_member,
                    return_pc,
                } = state.threads.get_mut(&state.active_thread).unwrap().stack.pop().unwrap();
                let return_type = current_member.type_of();
                if return_type != RuntimeType::VoidRuntimeType {
                    if let Some(lhs) = returning_lhs {
                        let rv = params
                            .get(&constants::retval())
                            .expect("Found no return value, missing a return?");
                        let return_value = evaluate(state, rv.clone(), en);

                        execute_assign(state, &lhs, return_value, en);
                    }
                }

                ActionResult::Return(return_pc)
            }
        }
        CFGStatement::Statement(Statement::Call { invocation, .. }) => exec_invocation(
            state,
            InvocationContext {
                invocation,
                lhs: None,
                return_point: pc,
                program,
            },
            en,
        ),
        CFGStatement::Statement(Statement::Fork { invocation, .. }) => exec_fork(
            state,
            InvocationContext {
                invocation,
                lhs: None,
                return_point: pc,
                program,
            },
            en,
        ),
        CFGStatement::Statement(Statement::Throw { message, .. }) => exec_throw(state, en, message),
        CFGStatement::TryCatch(_, _, catch_entry_pc, _) => {
            state
                .exception_handler
                .insert_handler(ExceptionHandlerEntry::new(*catch_entry_pc));
            ActionResult::Continue
        }
        CFGStatement::TryEntry(_) => ActionResult::Continue,
        CFGStatement::TryExit => {
            state.exception_handler.remove_last_handler();
            ActionResult::Continue
        }
        CFGStatement::CatchEntry(_) => ActionResult::Continue,
        _ => ActionResult::Continue,
    }
}

fn exec_throw(state: &mut State, en: &mut impl Engine, message: &str) -> ActionResult {
    info!(state.logger, "executing throw");

    if let Some(ExceptionHandlerEntry {
        catch_pc,
        mut current_depth,
    }) = state.exception_handler.pop_last()
    {
        // A catch was found, starting from now untill the catch we check any exceptional(..) clauses.
        while current_depth > 0 {
            if let Some((exceptional, type_guard)) = state.threads.get_mut(&state.active_thread).unwrap()
                .stack
                .pop()
                .and_then(|frame| frame.current_member.exceptional())
            {
                if !assert_exceptional(state, en, exceptional.clone(), type_guard, message) {
                    return ActionResult::InvalidAssertion(exceptional.get_position());
                }
            }
            current_depth -= 1;
        }
        ActionResult::Return(catch_pc)
    } else {
        // No catch found, starting from now untill the initial method we check any exceptional(..) clauses.
        while let Some(stack_frame) = state.threads.get_mut(&state.active_thread).unwrap().stack.current_stackframe() {
            if let Some((exceptional, type_guard)) = stack_frame.current_member.exceptional() {
                if !assert_exceptional(state, en, exceptional.clone(), type_guard, message) {
                    return ActionResult::InvalidAssertion(exceptional.get_position());
                }
            }
            state.threads.get_mut(&state.active_thread).unwrap().stack.pop();
        }
        ActionResult::Finish
    }
}

/// Asserts an `exceptional(..)` OOX statement.
/// Returns false if the exception is invalid.
fn assert_exceptional(
    state: &mut State,
    en: &mut impl Engine,
    exceptional: Rc<Expression>,
    type_guard: Option<TypeExpr>,
    message: &str,
) -> bool {
    let assertion = prepare_assert_expression(state, exceptional, en);
    let is_valid = eval_assertion(state, assertion, en);
    if !is_valid {
        error!(state.logger, "Exceptional message: {:?}", message);
        return false;
    }
    if let Some(type_guard) = type_guard.as_ref() {
        let path_constraints = collect_path_constraints(state);
        dbg!(&path_constraints);
        let path_constraints_sat = !eval_assertion(state, path_constraints, en);
        dbg!(path_constraints_sat);
        // if the path constraints are satisfiable, we have to check this otherwise the path is unfeasible and we don't.
        if path_constraints_sat {
            let all_of_type = assert_type_guard(state, type_guard, en);
            if !all_of_type {
                return false;
            }
        }
    }
    true
}

// Evaluates the expression with Z3
fn eval_assertion(state: &mut State, expression: Rc<Expression>, en: &mut impl Engine) -> bool {
    info!(state.logger, "invoke Z3");
    // dbg!(&alias_map);
    en.statistics().measure_verification();
    // println!("expression: {:?}", &expression);

    if *expression == Expression::TRUE {
        false
    } else if *expression == Expression::FALSE {
        true
    } else {
        let symbolic_refs = find_symbolic_refs(&expression);
        if symbolic_refs.is_empty() {
            let result = z3_checker::concretization::verify(&expression);
            if let SatResult::Unsat = result {
            } else {
                return false;
            }
        } else {
            // dbg!(&symbolic_refs);
            debug!(
                state.logger,
                "Unique symbolic refs: {}",
                symbolic_refs.len()
            );

            let solve_with_z3_only = if let Some(local_solving_threshold) = en.options().local_solving_threshold {
                // The number of combinations of each symbolic ref, which could be concretized.
                // If this number is too large we leave all the work to Z3 which seems to be faster in practice.
                // This explodes so hard we need 128 bit integer and it still overflows.
                let n_combinations: u128 = state
                    .alias_map
                    .iter()
                    .fold(Some(1_u128), |a, (_, refs)| {
                        a.and_then(|a| a.checked_mul(refs.aliases().len() as u128))
                    })
                    .unwrap_or(u128::MAX); // limit overflow to max u128

                n_combinations > local_solving_threshold
            } else {
                true
            };


            if solve_with_z3_only {
                // Solve through only Z3
                let result = z3_checker::all_z3::verify(&expression, &state.alias_map);
                if let SatResult::Unsat = result {
                    // valid, continue
                } else {
                    return false;
                }
            } else {
                // Solve using concretizations + Z3

                // Cloning alias map is not optimal but needed due to borrow of state.
                // Optimization: This can be avoided if we can make evaluate() (or a version of evaluate) not borrow state mutably.
                let expressions =
                    concretizations(expression.clone(), &symbolic_refs, state.alias_map.clone());

                debug!(
                    state.logger,
                    "Number of concretization expressions: {}",
                    expressions.len()
                );
                // This introduces branching in computation for each concretization proposed:
                en.statistics().measure_branches(expressions.len() as u32);
                // dbg!(&expressions);

                for expression in expressions {
                    let expression = evaluate(state, expression, en);
                    if *expression == Expression::TRUE {
                        // Invalid
                        en.statistics().measure_local_solve();
                        return false;
                    } else if *expression == Expression::FALSE {
                        // valid, continue
                        en.statistics().measure_local_solve();
                    } else {
                        en.statistics().measure_invoke_z3();
                        let result = z3_checker::concretization::verify(&expression);
                        if let SatResult::Unsat = result {
                            // valid, continue
                        } else {
                            return false;
                        }
                    }
                }
            }
        }
        return true;
    }
}

/// Handles an invocation statement in OOX.
///
/// This may result in state splitting due to dynamic binding, states are appended to the engine.
fn exec_invocation(
    state: &mut State,
    context: InvocationContext,
    en: &mut impl Engine,
) -> ActionResult {
    // dbg!(invocation);

    debug!(state.logger, "Invocation"; "invocation" => %context.invocation);

    state.exception_handler.increment_handler();

    match context.invocation {
        Invocation::InvokeMethod {
            resolved,
            lhs: invocation_lhs,
            ..
        } => {
            let potential_methods = resolved.as_ref().unwrap();

            if potential_methods.len() == 1 {
                debug!(state.logger, "only one potential method, resolved");
                // potentially a static method.
                let (_, potential_method) = &potential_methods.iter().next().unwrap();
                // A static method, or a method that is not overriden anywhere (non-polymorphic)
                let next_entry =
                    invocation::single_method_invocation(state, context, potential_method, en);
                ActionResult::FunctionCall(next_entry)
            } else {
                // dbg!(invocation_lhs);

                invocation::multiple_method_invocation(
                    state,
                    invocation_lhs,
                    context,
                    potential_methods,
                    en,
                )
            }
        }
        Invocation::InvokeConstructor {
            resolved,
            class_name,
            ..
        } => {
            let (declaration, method): &(Declaration, Rc<Method>) = resolved
                .as_ref()
                .map(AsRef::as_ref)
                .unwrap_or_else(|| panic!("Unresolved constructor for class {}", class_name));
            let class_name = declaration.name();

            let this_param = Parameter::new(
                NonVoidType::ReferenceType {
                    identifier: class_name.clone(),
                    info: SourcePos::UnknownPosition,
                },
                constants::this_str(),
            );
            invocation::exec_constructor_entry(
                state,
                context.clone(),
                method.clone(),
                class_name,
                en,
                this_param,
            );

            let next_entry = find_entry_for_static_invocation(
                class_name,
                &method.name,
                context.invocation.argument_types(),
                context.program,
                en.symbol_table(),
            );
            ActionResult::FunctionCall(next_entry)
        }
        Invocation::InvokeSuperConstructor { resolved, .. } => {
            let (declaration, method) = resolved
                .as_ref()
                .map(AsRef::as_ref)
                .expect("super constructor call not resolved");
            let class_name = declaration.name();

            // evaluate arguments
            let this_param = Parameter::new(
                NonVoidType::ReferenceType {
                    identifier: class_name.clone(),
                    info: SourcePos::UnknownPosition,
                },
                constants::this_str(),
            );
            invocation::exec_super_constructor(
                state,
                context.clone(),
                method.clone(),
                &method.params,
                en,
                this_param,
            );
            let next_entry = find_entry_for_static_invocation(
                class_name,
                &method.name,
                context.invocation.argument_types(),
                context.program,
                en.symbol_table(),
            );
            ActionResult::FunctionCall(next_entry)
        }
        Invocation::InvokeSuperMethod { resolved, .. } => {
            let potential_method = resolved.as_ref().unwrap();

            let next_entry =
                invocation::single_method_invocation(state, context, potential_method, en);
            ActionResult::FunctionCall(next_entry)
        }
    }
}

/// Handles an fork statement in OOX.
///
/// This may result in state splitting due to dynamic binding, states are appended to the engine.
fn exec_fork(
    state: &mut State,
    context: InvocationContext,
    en: &mut impl Engine,
) -> ActionResult {
    // dbg!(invocation);

    debug!(state.logger, "Invocation"; "invocation" => %context.invocation);

    state.exception_handler.increment_handler();

    match context.invocation {
        Invocation::InvokeMethod {
            resolved,
            info,
            ..
        } => {
            let potential_methods = resolved.as_ref().unwrap();

            if potential_methods.len() == 1 {
                debug!(state.logger, "only one potential method, resolved");
                let (_, potential_method) = &potential_methods.iter().next().unwrap();
                fork_invocation(state, context, potential_method, en);
                ActionResult::Continue
            } else {
                error!(state.logger, "Foxrk can only have a Single possible method invocation");
                ActionResult::InvalidFork(*info)
            }
            
        },
        Invocation::InvokeSuperMethod {  info, .. } => {
            error!(state.logger, "Fork can only have a Method invocation, found SuperMethod");
            ActionResult::InvalidFork(*info)
        },
        Invocation::InvokeConstructor { info, ..} => {
            error!(state.logger, "Fork can only have a Method invocation, found Constructor");
            ActionResult::InvalidFork(*info)
        },
        Invocation::InvokeSuperConstructor { info, .. } => {
            error!(state.logger, "Fork can only have a Method invocation, found SuperConstructor");
            ActionResult::InvalidFork(*info)
        },
        
    }
}

/// Given a class name and method name, lookup the entry node in the Control Flow Graph
/// Also checks if the argument types match.
/// Panics if the method is not found
pub fn find_entry_for_static_invocation(
    class_name: &str,
    method_name: &str,
    argument_types: impl ExactSizeIterator<Item = RuntimeType> + Clone,
    program: &HashMap<u64, CFGStatement>,
    st: &SymbolTable,
) -> u64 {
    // dbg!(invocation);
    let (entry, _) = program
        .iter()
        .find(|(_k, v)| {
            if let CFGStatement::FunctionEntry {
                decl_name: other_decl_name,
                method_name: other_method_name,
                argument_types: other_argument_types,
            } = *v
            {
                let mut argument_types_match = argument_types
                    .clone()
                    .zip(other_argument_types)
                    .map(|(a, b)| a.is_of_type(b, st));
                *other_decl_name == class_name
                    && *other_method_name == method_name
                    && argument_types.len() == other_argument_types.len()
                    && argument_types_match.all_equal()
            } else {
                false
            }
        })
        .unwrap_or_else(|| {
            panic!(
                "Could not find the method {}.{}({:?})",
                class_name,
                method_name,
                argument_types.clone().collect_vec()
            )
        });

    *entry
}

fn prepare_assert_expression(
    state: &mut State,
    assertion: Rc<Expression>,
    en: &mut impl Engine,
) -> Rc<Expression> {
    let expression = if !state.constraints.is_empty() {
        let assumptions = collect_path_constraints(state);

        negate(Rc::new(Expression::BinOp {
            bin_op: BinOp::Implies,
            lhs: assumptions,
            rhs: assertion,
            type_: RuntimeType::BoolRuntimeType,
            info: SourcePos::UnknownPosition,
        }))
    } else {
        negate(assertion)
    };
    // let expression = constraints.iter().fold(
    //     Expression::UnOp {
    //         un_op: UnOp::Negative,
    //         value: Box::new(assertion.clone()),
    //         type_: RuntimeType::BoolRuntimeType,
    //     },
    //     |x, b| Expression::BinOp {
    //         bin_op: BinOp::And,
    //         lhs: Box::new(x),
    //         rhs: Box::new(b.clone()),
    //         type_: RuntimeType::BoolRuntimeType,
    //     },
    // );
    debug!(state.logger, "Expression to evaluate: {}", expression);
    let z = evaluate(state, Rc::new(expression), en);
    debug!(state.logger, "Evaluated expression: {}", z);
    z
}

/// Collects the path constraints into an expression
fn collect_path_constraints(state: &State) -> Rc<Expression> {
    state
        .constraints
        .iter()
        .cloned()
        .reduce(|x, y| {
            Expression::BinOp {
                bin_op: BinOp::And,
                lhs: x,
                rhs: y,
                type_: RuntimeType::BoolRuntimeType,
                info: SourcePos::UnknownPosition,
            }
            .into()
        })
        .unwrap()
}

fn read_field_concrete_ref(heap: &mut Heap, ref_: i64, field: &Identifier) -> Rc<Expression> {
    match heap.get_mut(&ref_).unwrap() {
        HeapValue::ObjectValue { fields, .. } => fields[field].clone(),
        x => panic!("Expected object, found {:?}", x),
    }
}

fn read_field_symbolic_ref(
    heap: &mut Heap,
    concrete_refs: &[Rc<Expression>],
    sym_ref: Rc<Expression>,
    field: &Identifier,
) -> Rc<Expression> {
    // dbg!(sym_ref.as_ref());
    match concrete_refs {
        [] => {
            panic!("A symbolic object must have at least one concrete reference when initialised")
        }
        [r] => {
            // null is not possible here, will be caught with exceptional state
            let ref_ = r.expect_reference().unwrap();
            read_field_concrete_ref(heap, ref_, field)
        }
        // A symbolic object only contains references (and null literals that are filtered out by exceptional guard paths)
        [r, rs @ ..] => {
            let ref_ = r.expect_reference().unwrap();
            Rc::new(Expression::Conditional {
                guard: Rc::new(Expression::BinOp {
                    bin_op: BinOp::Equal,
                    lhs: sym_ref.clone(),
                    rhs: r.clone(),
                    type_: RuntimeType::BoolRuntimeType,
                    info: SourcePos::UnknownPosition,
                }),
                true_: (read_field_concrete_ref(heap, ref_, field)),
                false_: (read_field_symbolic_ref(heap, rs, sym_ref, field)),
                type_: RuntimeType::BoolRuntimeType,
                info: SourcePos::UnknownPosition,
            })
        }
    }
}

fn write_field_concrete_ref(heap: &mut Heap, ref_: i64, field: &Identifier, value: Rc<Expression>) {
    if let HeapValue::ObjectValue { fields, .. } = heap.get_mut(&ref_).unwrap() {
        fields.insert(field.clone(), value);
    } else {
        panic!("expected object")
    }
}

fn write_field_symbolic_ref(
    heap: &mut Heap,
    concrete_refs: &[Rc<Expression>],
    field: &Identifier,
    sym_ref: Rc<Expression>,
    value: Rc<Expression>,
) {
    match concrete_refs {
        [] => {
            panic!("Symbolic objects must have at least one concrete reference when initialised.")
        }
        [r] => {
            let ref_ = r.expect_reference().unwrap();
            write_field_concrete_ref(heap, ref_, field, value)
        }
        rs => {
            for r in rs {
                // Should only contain refs
                let ref_ = r.expect_reference().unwrap();
                let ite = ite(
                    equal(sym_ref.clone(), r.clone()),
                    value.clone(),
                    read_field_concrete_ref(heap, ref_, field),
                );
                write_field_concrete_ref(heap, ref_, field, Rc::new(ite))
            }
        }
    }
}

/// Initialise a symbolic object reference.
pub fn init_symbolic_reference(
    state: &mut State,
    sym_ref: &Identifier,
    type_ref: &RuntimeType,
    en: &mut impl Engine,
) {
    if !state.alias_map.contains_key(sym_ref) {
        debug!(state.logger, "Lazy initialisation of symbolic reference"; "ref" => #?sym_ref, "type" => #?type_ref);
        match type_ref {
            RuntimeType::ReferenceRuntimeType { type_ } => {
                init_symbolic_object(type_, state, sym_ref, en)
            }
            RuntimeType::ArrayRuntimeType { .. } => {
                exec_array_initialisation(state, en, sym_ref.clone(), type_ref.clone())
            }
            _ => panic!(
                "Cannot initialize type {:?}, not a reference or arraytype",
                type_ref
            ),
        };

        debug!(state.logger, "Updated aliasentry"; "alias_map" => #?state.alias_map);
    }
}

fn init_symbolic_object(
    decl_name: &Identifier,
    state: &mut State,
    sym_ref: &Identifier,
    en: &mut impl Engine,
) {
    let st = en.symbol_table();
    // initialise new objects, one for each possible type (sub)class of class_name
    let new_object_references = st
        .get_all_instance_types(decl_name)
        .iter()
        .map(|class_name| {
            let fields = st
                .get_all_fields(class_name)
                .iter()
                .map(|(field_name, type_)| {
                    (
                        field_name.clone(),
                        Rc::new(initialize_symbolic_var(
                            field_name,
                            &type_.type_of(),
                            state.next_reference_id(),
                            st,
                        )),
                    )
                })
                .collect();

            state.allocate_on_heap(HeapValue::ObjectValue {
                fields,
                type_: RuntimeType::ReferenceRuntimeType {
                    type_: class_name.clone(),
                },
            })
        })
        .collect_vec();

    // Find all other possible concrete references of the same type as sym_ref
    let instance_types = st.get_all_instance_types(decl_name);

    let has_unique_type = instance_types.len() == 1;

    let existing_aliases = state
        .alias_map
        .values()
        .filter_map(|x| {
            if let Some(type_) = x.uniform_type() {
                let ref_type = match type_ {
                    RuntimeType::ReferenceRuntimeType { type_ } => type_,
                    RuntimeType::ArrayRuntimeType { .. } => return None, // arrays cannot have the same type as objects, skip
                    _ => panic!("Expected reference or array type"),
                };

                if instance_types.contains(&ref_type) {
                    Some(Either::Left(x.aliases.iter()))
                } else {
                    None
                }
            } else {
                Some(Either::Right(x.aliases.iter().filter(|x| {
                    if let Some(ref_type) = x.type_of().as_reference_type() {
                        instance_types.contains(ref_type)
                    } else {
                        // null
                        false
                    }
                })))
            }
        })
        .flat_map(|x| x.into_iter())
        .unique();

    let aliases = existing_aliases
        .cloned()
        .chain(std::iter::once(Expression::NULL.into()))
        .chain(new_object_references.into_iter())
        .collect();

    state.alias_map.insert(
        sym_ref.clone(),
        AliasEntry::new_with_uniform_type(aliases, has_unique_type),
    );
}

fn execute_assign(state: &mut State, lhs: &Lhs, e: Rc<Expression>, en: &mut impl Engine) {
    // let st = en.symbol_table();

    match lhs {
        Lhs::LhsVar { var, .. } => {
            state.threads.get_mut(&state.active_thread).unwrap().stack.insert_variable(var.clone(), e);
        }
        Lhs::LhsField { var, field, .. } => {
            let o = state.threads.get_mut(&state.active_thread).unwrap()
                .stack
                .lookup(var)
                .unwrap_or_else(|| panic!("object {:?} was not found on the stack", var));

            match o.as_ref() {
                Expression::Ref { ref_, .. } => {
                    write_field_concrete_ref(&mut state.heap, *ref_, field, e);
                }
                Expression::SymbolicRef { var, type_, .. } => {
                    init_symbolic_reference(state, var, type_, en);
                    // should also remove null here? --Assignemnt::45
                    // Yes, we have if (x = null) { throw; } guards that ensure it cannot be null
                    remove_symbolic_null(&mut state.alias_map, var);
                    let concrete_refs = &state.alias_map[var];
                    // dbg!(&var, &concrete_refs);
                    write_field_symbolic_ref(
                        &mut state.heap,
                        &concrete_refs.aliases,
                        field,
                        o,
                        e,
                    );
                }
                Expression::Conditional {
                    guard,
                    true_,
                    false_,
                    ..
                } => {
                    state_split::conditional_state_split(
                        state,
                        en,
                        guard.clone(),
                        true_.clone(),
                        false_.clone(),
                        var.clone(),
                    );
                    execute_assign(state, lhs, e, en)
                }

                _ => todo!("{:?}", o.as_ref()),
            }
        }
        Lhs::LhsElem { var, index, .. } => {
            let ref_ = state.threads.get_mut(&state.active_thread).unwrap()
                .stack
                .lookup(var)
                .unwrap_or_else(|| panic!("array {:?} was not found on the stack", var));

            let ref_ = single_alias_elimination(ref_.clone(), &state.alias_map)
                .expect_reference()
                .unwrap_or_else(|| panic!("expected array ref, found expr {:?}", &ref_));

            let index = evaluate_as_int(state, index.clone(), en);
            match index {
                Either::Left(index) => write_elem_symbolic_index(state, ref_, index, e),
                Either::Right(i) => write_elem_concrete_index(state, ref_, i, e),
            }
        }
    }
}

fn evaluate_rhs(state: &mut State, rhs: &Rhs, en: &mut impl Engine) -> Rc<Expression> {
    let thread = state.threads.get_mut(&state.active_thread).unwrap();

    match rhs {
        Rhs::RhsExpression { value, .. } => {
            match value.as_ref() {
                Expression::Var { var, .. } => thread.stack.lookup(var).unwrap_or_else(|| {
                    panic!(
                        "Could not find {:?} on the stack {:?}",
                        var,
                        &thread.stack.current_variables()
                    )
                }),
                _ => value.clone(), // might have to expand on this when dealing with complex quantifying expressions and array
            }
        }
        Rhs::RhsField { var, field, .. } => {
            if let Expression::Var { var, .. } = var.as_ref() {
                let object = thread.stack.lookup(var).unwrap();
                exec_rhs_field(state, object, field, en)
            } else {
                panic!(
                    "Currently only right hand sides of the form <variable>.<field> are allowed."
                )
            }
        }
        // We expect that this symbolic reference has been initialised into multiple states,
        // where in each state the aliasmap is left with one concrete array.
        Rhs::RhsElem { var, index, .. } => {
            if let Expression::Var { var, .. } = var.as_ref() {
                let array = thread.stack.lookup(var).unwrap();
                exec_rhs_elem(state, array, index.to_owned().into(), en)
            } else {
                panic!("Unexpected uninitialized array");
            }
        }
        Rhs::RhsCall { .. } => {
            unreachable!("unreachable, invocations are handled in function exec_invocation()")
        }

        Rhs::RhsArray {
            array_type,
            sizes,
            type_,
            ..
        } => exec_array_construction(state, array_type, sizes, type_, en),
        Rhs::RhsCast { cast_type, var, .. } => {
            let object = thread.stack.lookup(var).unwrap_or_else(|| {
                panic!(
                    "Could not find {:?} on the stack {:?}",
                    var,
                    &thread.stack.current_variables()
                )
            });

            match object.as_ref() {
                Expression::Ref {
                    ref_,
                    type_: _old_type,
                    info,
                } => Expression::Ref {
                    ref_: *ref_,
                    type_: cast_type.type_of(),
                    info: *info,
                }
                .into(),
                Expression::SymbolicRef {
                    var,
                    type_: _old_type,
                    info,
                } => Expression::SymbolicRef {
                    var: var.clone(),
                    type_: cast_type.type_of(),
                    info: *info,
                }
                .into(),
                _ => panic!(
                    "Expected class cast operator to cast on ref or symbolic ref, found {:?}",
                    object
                ),
            }
        }
    }
}

fn exec_rhs_field(
    state: &mut State,
    object: Rc<Expression>,
    field: &Identifier,
    en: &mut impl Engine,
) -> Rc<Expression> {
    match object.as_ref() {
        Expression::Conditional {
            guard,
            true_,
            false_,
            type_,
            info,
        } => {
            let true_ = exec_rhs_field(state, true_.clone(), field, en);
            let false_ = exec_rhs_field(state, false_.clone(), field, en);

            Rc::new(Expression::Conditional {
                guard: guard.clone(),
                true_,
                false_,
                type_: type_.clone(),
                info: *info,
            })
        }
        Expression::Lit {
            lit: Lit::NullLit, ..
        } => panic!("infeasible"),
        Expression::Ref { ref_, .. } => read_field_concrete_ref(&mut state.heap, *ref_, field),
        Expression::SymbolicRef { var, type_, .. } => {
            init_symbolic_reference(state, var, type_, en);
            remove_symbolic_null(&mut state.alias_map, var);
            let concrete_refs = &state.alias_map[var];
            // dbg!(&alias_map);
            // dbg!(&heap);
            read_field_symbolic_ref(
                &mut state.heap,
                &concrete_refs.aliases,
                object,
                field,
            )
        }
        _ => todo!("Expected reference here, found: {:?}", object),
    }
}

fn exec_rhs_elem(
    state: &mut State,
    array: Rc<Expression>,
    index: Rc<Expression>,
    en: &mut impl Engine,
) -> Rc<Expression> {
    // arrays are always initialised as concretes
    let array = single_alias_elimination(array, &state.alias_map);
    match array.as_ref() {
        Expression::Ref { ref_, .. } => {
            let index = evaluate_as_int(state, index, en);
            match index {
                Either::Left(index) => read_elem_symbolic_index(state, *ref_, index),
                Either::Right(index) => read_elem_concrete_index(state, *ref_, index),
            }
        }
        _ => {
            panic!("expected array ref, found expr {:?}", &array)
        }
    }
}

/// Removes Null literals from the aliasmap entry.
/// This is allowed since we assume to have exceptional checks for null added in OOX parser.
/// See [`insert_exceptional_clauses`].
fn remove_symbolic_null(alias_map: &mut AliasMap, var: &Identifier) {
    // dbg!(&alias_map, &var);
    alias_map.get_mut(var).unwrap().remove_null()
}

fn create_symbolic_var(name: Identifier, type_: impl Typeable, st: &SymbolTable) -> Expression {
    if type_.is_of_type(RuntimeType::REFRuntimeType, st) {
        Expression::SymbolicRef {
            var: name,
            type_: type_.type_of(),
            info: SourcePos::UnknownPosition,
        }
    } else {
        Expression::SymbolicVar {
            var: name,
            type_: type_.type_of(),
            info: SourcePos::UnknownPosition,
        }
    }
}

/// Create uninitialised variable (that can be initialized lazily)
fn initialize_symbolic_var(
    name: &str,
    type_: &RuntimeType,
    ref_: i64,
    st: &SymbolTable,
) -> Expression {
    let sym_name = format!("{}{}", name, ref_);
    create_symbolic_var(sym_name.into(), type_.clone(), st)
}

fn read_elem_concrete_index(state: &mut State, ref_: Reference, index: i64) -> Rc<Expression> {
    if let HeapValue::ArrayValue { elements, .. } = state.heap.get(&ref_).unwrap() {
        elements[index as usize].clone()
    } else {
        panic!("Expected Array object");
    }
}

/// Reads an expression from the array at reference ref_ in the heap,
/// with a symbolic index.
///
/// Since it is symbolic it will return a nested if-then-else expression
/// Like this:
/// index == #1 ? e1 : (index == #2 ? e2 : e3)
fn read_elem_symbolic_index(
    state: &mut State,
    ref_: Reference,
    index: Rc<Expression>,
) -> Rc<Expression> {
    if let HeapValue::ArrayValue { elements, .. } = state.heap.get(&ref_).unwrap() {
        let indices = (0..elements.len()).map(|i| to_int_expr(i as i64));

        let mut indexed_elements = elements.iter().zip(indices).rev();

        if let Some((last_element, _)) = indexed_elements.next() {
            indexed_elements.fold(last_element.clone(), |acc, (element, concrete_index)| {
                ite(equal(index.clone(), concrete_index), element.clone(), acc).into()
            })
        } else {
            // empty array
            panic!("Empty array, exceptional clauses should prevent this");
        }
    } else {
        panic!("Expected Array object");
    }
}

fn write_elem_concrete_index(
    state: &mut State,
    ref_: Reference,
    index: i64,
    expression: Rc<Expression>,
) {
    if let HeapValue::ArrayValue { elements, .. } = state.heap.get_mut(&ref_).unwrap() {
        if index >= 0 && index < elements.len() as i64 {
            elements[index as usize] = expression;
        } else {
            panic!("should be infeasible due to added checked array bounds");
        }
    } else {
        panic!("Expected Array object")
    }
}

fn write_elem_symbolic_index(
    state: &mut State,
    ref_: Reference,
    index: Rc<Expression>,
    expression: Rc<Expression>,
) {
    if let HeapValue::ArrayValue { elements, .. } = state.heap.get_mut(&ref_).unwrap() {
        let indices = (0..elements.len()).map(|i| to_int_expr(i as i64));

        let indexed_elements = elements.iter_mut().zip(indices);

        for (value, concrete_index) in indexed_elements {
            *value = ite(
                equal(index.clone(), concrete_index),
                expression.clone(),
                value.clone(),
            )
            .into()
        }
    } else {
        panic!("expected Array object")
    }
}

/// Helper function, does not invoke Z3 but tries to evaluate the assumption locally.
/// Returns whether the assumption was found to be feasible.
/// Otherwise it inserts the assumption into the constraints.
fn exec_assume(
    state: &mut State,
    assumption: Either<Rc<Expression>, TypeExpr>,
    en: &mut impl Engine,
) -> bool {
    // special case for instanceof, since we don't add them to the path constraints but their assumption is made by ensuring it in the alias map.
    let options = en.options();
    match assumption {
        Either::Left(assumption) => {
            if !options.prune_path_z3 {
                // We prune as much as we can with the frontend evaluator, but any path with containing symbolic variables will likely go through.
                // Those paths would be infeasible eventually when an assert is encountered.
                let expression = evaluate(state, assumption, en);
                if *expression == Expression::FALSE {
                    return false;
                } else if *expression != Expression::TRUE {
                    state.constraints.insert(expression);
                }
            } else {
                let constraints = collect_path_constraints(state);
                let assumption = evaluate(state, assumption, en);
                // dbg!(&assumption);
                let expression = evaluate(state, and(constraints, assumption.clone()), en);
                // dbg!(&expression);
                if *expression == Expression::FALSE {
                    return false;
                } else {
                    let result = z3_checker::all_z3::verify(&expression, &state.alias_map);
                    // eval_assertion(state, expression, en)
                    if result == SatResult::Sat {
                        if *expression != Expression::TRUE {
                            state.constraints.insert(assumption);
                        }
                    } else {
                        return false;
                    }
                }
            }

        }
        Either::Right(assumption) => {
            let type_guard_feasible = assume_type_guard(state, &assumption, en);
            if !type_guard_feasible {
                debug!(
                    state.logger,
                    "No aliases left after instanceof operator, pruning path"
                );
                return false;
            }
        }
    }
    true
}

fn get_expression_for_var(
    state: &mut State,
    var: &Identifier,
    en: &mut impl Engine,
) -> Rc<Expression> {
    let symbolic_ref = state.threads.get_mut(&state.active_thread).unwrap().stack.lookup(var).unwrap();

    evaluate(state, symbolic_ref, en)
}

fn get_alias_for_var<'a>(
    state: &'a mut State,
    var: &Identifier,
    en: &mut impl Engine,
) -> &'a mut AliasEntry {
    let symbolic_ref = state.threads.get_mut(&state.active_thread).unwrap().stack.lookup(var).unwrap();

    let symbolic_ref = evaluate(state, symbolic_ref, en)
        .expect_symbolic_ref()
        .unwrap();
    state
        .alias_map
        .get_mut(&symbolic_ref)
        .unwrap_or_else(|| panic!("expected '{:?}' to be a symbolic object with aliases", var))
}

/// helper function for `is_of_type`, that can not `!` the result.
fn is_of_type_or_not(a: impl Typeable, b: impl Typeable, not: bool, st: &SymbolTable) -> bool {
    let ref_of_type = a.is_of_type(b, st);
    if not {
        !ref_of_type
    } else {
        ref_of_type
    }
}

/// Returns whether the assertion holds for the type guard.
/// This is checked using the aliasmap, no Z3 involved.
fn assert_type_guard(state: &mut State, type_guard: &TypeExpr, en: &mut impl Engine) -> bool {
    let (var, rhs, not) = match type_guard {
        TypeExpr::InstanceOf { var, rhs, .. } => (var, rhs, false),
        TypeExpr::NotInstanceOf { var, rhs, .. } => (var, rhs, true),
    };

    match get_expression_for_var(state, var, en).as_ref() {
        Expression::Ref { type_, .. } => is_of_type_or_not(type_, rhs, not, en.symbol_table()),
        Expression::SymbolicRef { var, .. } => {
            let alias_entry = &mut state.alias_map[var];
            alias_entry
                .aliases
                .iter()
                .all(|alias| is_of_type_or_not(alias.as_ref(), rhs, not, en.symbol_table()))
        }
        _ => panic!("expected ref or symbolic ref"),
    }
}

/// Checks if the assumption holds for the type guard, returns whether the path is feasible
fn assume_type_guard(state: &mut State, type_guard: &TypeExpr, en: &mut impl Engine) -> bool {
    let (var, rhs, not) = match type_guard {
        TypeExpr::InstanceOf { var, rhs, .. } => (var, rhs, false),
        TypeExpr::NotInstanceOf { var, rhs, .. } => (var, rhs, true),
    };

    match get_expression_for_var(state, var, en).as_ref() {
        Expression::Ref { type_, .. } => is_of_type_or_not(type_, rhs, not, en.symbol_table()),
        Expression::SymbolicRef { var, .. } => {
            let alias_entry = &mut state.alias_map[var];
            alias_entry
                .aliases
                .retain(|alias| is_of_type_or_not(alias.as_ref(), rhs, not, en.symbol_table()));

            !(alias_entry.aliases.is_empty() || alias_entry.aliases.iter().all(|e| *e.as_ref() == Expression::NULL))
        }
        Expression::Conditional {
            // Must not forget that it can also be a conditional in some cases and we need to split the state.
            guard,
            true_,
            false_,
            ..
        } => {
            state_split::conditional_state_split(
                state,
                en,
                guard.clone(),
                true_.clone(),
                false_.clone(),
                var.clone(),
            );
            assume_type_guard(state, type_guard, en)
        }
        e => panic!("expected ref or symbolic ref, found {:?}", e),
    }
}

/// Checks whether there is only one alias for the given symbolic reference, if so return the alias otherwise return the expression.
/// A single alias occurs for example when an array is initialised, split into multiple paths each with a different array size.
pub(crate) fn single_alias_elimination(
    expr: Rc<Expression>,
    alias_map: &AliasMap,
) -> Rc<Expression> {
    if let Expression::SymbolicRef { var, .. } = expr.as_ref() {
        let alias = &alias_map[var];
        if alias.aliases.len() == 1 {
            return alias.aliases[0].clone();
        }
    }
    expr
}

pub type Error = String;

#[derive(Copy, Clone, PartialEq, Eq, ValueEnum, Debug)]
pub enum Heuristic {
    DepthFirstSearch,
    RandomPath,
    MinDist2Uncovered,
    RoundRobinMD2URandomPath,
}

/// For a description of each option, see Commands in main.rs
#[derive(Copy, Clone)]
pub struct Options<'a> {
    pub k: u64,
    /// The allowed maximum time of the verification in seconds.
    pub time_budget: u64,
    pub quiet: bool,
    pub with_exceptional_clauses: bool,
    pub heuristic: Heuristic,
    pub visualize_heuristic: bool,
    pub visualize_coverage: bool,
    pub symbolic_array_size: u64,
    pub log_path: &'a str,
    pub discard_logs: bool,
    pub prune_path_z3: bool,
    pub local_solving_threshold: Option<u128>,
}

impl Default for Options<'_> {
    fn default() -> Self {
        // These settings are used during testing (by default). 
        // The default settings used when running from the CLI can be found in main.rs `Commands::Verify`
        Self {
            k: 40,
            quiet: false,
            with_exceptional_clauses: true,
            heuristic: Heuristic::DepthFirstSearch,
            visualize_heuristic: false,
            visualize_coverage: false,
            symbolic_array_size: 3,
            time_budget: 900,
            log_path: "./logs/log.txt",
            discard_logs: true,
            prune_path_z3: false,
            local_solving_threshold: Some(1000),
        }
    }
}

impl Options<'_> {
    pub fn default_with_k(k: u64) -> Options<'static> {
        Options {
            k,
            ..Default::default()
        }
    }

    pub fn default_with_k_and_heuristic(k: u64, heuristic: Heuristic) -> Options<'static> {
        Options {
            heuristic,
            ..Self::default_with_k(k)
        }
    }
}

pub fn verify(
    paths: &[impl ToString + AsRef<str>],
    class_name: &str,
    method_name: &str,
    options: Options,
) -> std::result::Result<(SymResult, Statistics), Error> {
    if !options.quiet {
        println!("Starting up");
    }

    // Set global file names
    *FILE_NAMES.lock().unwrap() = paths.iter().map(ToString::to_string).collect();

    let mut c = CompilationUnit::empty();

    for (file_number, path) in (0..).zip(paths.iter()) {
        let file_content = std::fs::read_to_string(path.as_ref()).map_err(|err| err.to_string())?;
        let file_cu = parse_program(&file_content, file_number, false).map_err(|error| match error {
            language::Error::ParseError(err) => err.to_string(),
            language::Error::LexerError((line, col)) => {
                format!("Lexer error at {}:{}:{}", path.to_string(), line, col)
            }
        })?;

        c = c.merge(file_cu);
    }
    if options.with_exceptional_clauses {
        c = insert_exceptional_clauses(c);
    }

    // dbg!(&c);
    if !options.quiet {
        println!("Parsing completed");
    }

    let initial_method = c
        .find_class_declaration_member(method_name, class_name.into())
        .ok_or_else(|| {
            format!(
                "Could not find method '{}' in class '{}'",
                method_name, class_name
            )
        })?;

    let symbol_table = SymbolTable::from_ast(&c)?;
    if !options.quiet {
        println!("Symbol table completed");
    }

    let c = type_compilation_unit(c, &symbol_table)?;
    if !options.quiet {
        println!("Typing completed");
    }

    let (result, flw) = labelled_statements(c);

    let program = result.into_iter().collect();

    println!("{:?}", program);
    // dbg!(&program);

    let flows: HashMap<u64, Vec<u64>> = utils::group_by(flw.into_iter());

    // dbg!(&flows);
    let argument_types = initial_method
        .params
        .iter()
        .map(Typeable::type_of)
        .collect();

    let entry_method = MethodIdentifier {
        decl_name: class_name.to_string(),
        method_name: method_name.to_string(),
        arg_list: argument_types,
    };

    let pc = find_entry_for_static_invocation(
        &entry_method.decl_name,
        &entry_method.method_name,
        entry_method.arg_list.iter().cloned(),
        &program,
        &symbol_table,
    );
    // dbg!(&params);
    let params: HashMap<Identifier, Rc<Expression>> = initial_method
        .params
        .iter()
        .map(|p| {
            (
                p.name.clone(),
                Rc::new(create_symbolic_var(
                    p.name.clone(),
                    p.type_.type_of(),
                    &symbol_table,
                )),
            )
        })
        .collect();
    // dbg!(&params);

    // let root_logger = slog::Logger::root(
    //     Mutex::new(slog_bunyan::default(std::io::stderr()).filter_level(Level::Debug)).fuse(),
    //     o!(),
    // );

    let root_logger = if options.discard_logs {
        slog::Logger::root(slog::Discard, o!())
    } else {
        let mut builder = FileLoggerBuilder::new(options.log_path);
        // let mut builder = TerminalLoggerBuilder::new();
        // builder.destination(Destination::Stdout);
        builder.level(Severity::Trace);
        builder.format(sloggers::types::Format::Full);
        builder.source_location(sloggers::types::SourceLocation::FileAndLine);
        builder.truncate();

        builder.build().unwrap()
    };
    
    info!(
        root_logger,
        "Starting verification of {}::{}", class_name, method_name
    );

    let mut constraints = ImHashSet::new();
    constraints.insert(Rc::new(Expression::TRUE));

    let thread: Thread = Thread {
        tid: 0,
        pc,
        state: ThreadState::Enabled,
        parents: vec![],
        prev_accesses: None,
        stack: Stack::new(vector![StackFrame {
            return_pc: pc,
            returning_lhs: None,
            params: params,
            current_member: initial_method,
        }])
    };

    let state = State {
        active_thread: 0,
        threads: HashMap::from([(0, thread)]),
        thread_counter: IdCounter::new(0),
        lock_requests: HashMap::new(),
        heap: ImHashMap::new(),
        constraints,
        alias_map: ImHashMap::new(),
        ref_counter: IdCounter::new(0),
        exception_handler: Default::default(),
        path_length: 0,
        path: vec![],
        logger: root_logger.new(o!("pathId" => 0)),
        path_id: 0,
    };

    let path_counter = Rc::new(RefCell::new(IdCounter::new(0)));
    let mut statistics = Statistics::default();

    // Choose between heuristic function (with matching parameters)
    let sym_exec = match options.heuristic {
        Heuristic::DepthFirstSearch => heuristics::depth_first_search::sym_exec,
        Heuristic::RandomPath => heuristics::random_path::sym_exec,
        Heuristic::MinDist2Uncovered => heuristics::min_dist_to_uncovered::sym_exec,
        Heuristic::RoundRobinMD2URandomPath => heuristics::round_robin::sym_exec,
    };
    let sym_result = sym_exec(
        state,
        &program,
        &flows,
        &symbol_table,
        root_logger,
        path_counter.clone(),
        &mut statistics,
        entry_method.clone(),
        &options,
    );

    let reachability = reachability(entry_method, &program, &flows, &symbol_table);
    statistics.reachable_statements = reachability.len() as u32;

    statistics.number_of_paths_explored = path_counter.borrow().current_value();

    if options.visualize_coverage {
        let contents = pretty_print_compilation_unit(
            &|pc: u64| {
                Some(format!(
                    "pc: {}, covered: {}",
                    pc,
                    statistics.coverage.contains(&pc)
                ))
            },
            &program,
            &flows,
            &symbol_table,
        );
        std::fs::write("coverage_visualized.txt", contents).unwrap();
    }



    Ok((sym_result, statistics))
}

#[test]
fn sym_exec_of_absolute_simplest() {
    let paths = vec!["./examples/absolute_simplest.oox"];
    let options = Options::default_with_k(20);
    assert_eq!(
        verify(&paths, "Foo", "f", options).unwrap().0,
        SymResult::Valid
    );
}

#[test]
fn sym_exec_min() {
    let paths = vec!["./examples/psv/min.oox"];
    assert_eq!(
        verify(&paths, "Foo", "min", Options::default_with_k(20)).unwrap().0,
        SymResult::Valid
    );
}

#[test]
fn sym_exec_method() {
    let paths = vec!["./examples/psv/method.oox"];
    assert_eq!(
        verify(&paths, "Main", "min", Options::default_with_k(20)).unwrap().0,
        SymResult::Valid
    );
}

// #[test]
// fn sym_exec_fib() {
//     let file_content = std::fs::read_to_string("./examples/psv/fib.oox").unwrap();
//     assert_eq!(verify(&file_content, "Main", "main", 50), SymResult::Valid);
// }

#[test]
fn sym_exec_div_by_n() {
    let paths = vec!["./examples/psv/divByN.oox"];
    // so this one is invalid at k = 100, in OOX it's invalid at k=105, due to exceptions (more if statements are added)
    assert_eq!(
        verify(
            &paths,
            "Main",
            "divByN_invalid",
            Options::default_with_k(100)
        )
        .unwrap().0,
        SymResult::Invalid(SourcePos::new(73, 16, 0))
    );
}

#[test]
fn sym_exec_nonstatic_function() {
    let paths = vec!["./examples/nonstatic_function.oox"];
    assert_eq!(
        verify(&paths, "Main", "f", Options::default_with_k(20)).unwrap().0,
        SymResult::Valid
    );
}

#[test]
fn sym_exec_this_method() {
    let paths = vec!["./examples/this_method.oox"];
    assert_eq!(
        verify(&paths, "Main", "main", Options::default_with_k(30)).unwrap().0,
        SymResult::Valid
    );
}

#[test]
fn sym_exec_linked_list1() {
    let paths = vec!["./examples/intLinkedList.oox"];
    assert_eq!(
        verify(&paths, "Node", "test2", Options::default_with_k(90)).unwrap().0,
        SymResult::Valid
    );
}

#[test]
fn sym_exec_linked_list1_invalid() {
    let paths = vec!["./examples/intLinkedList.oox"];
    assert_eq!(
        verify(&paths, "Node", "test2_invalid", Options::default_with_k(90)).unwrap().0,
        SymResult::Invalid(SourcePos::new(109, 16, 0))
    );
}

#[test]
fn sym_exec_linked_list3_invalid() {
    let paths = vec!["./examples/intLinkedList.oox"];
    // at k=80 it fails, after ~170 sec in hs oox, rs oox does this in ~90 sec
    assert_eq!(
        verify(
            &paths,
            "Node",
            "test3_invalid1",
            Options::default_with_k(110)
        )
        .unwrap().0,
        SymResult::Invalid(SourcePos::new(141, 18, 0))
    );
}

#[test]
fn sym_exec_linked_list4() {
    let paths = vec!["./examples/intLinkedList.oox"];
    assert_eq!(
        verify(&paths, "Node", "test4", Options::default_with_k(90)).unwrap().0,
        SymResult::Valid
    );
}

#[test]
fn sym_exec_linked_list4_invalid() {
    let paths = vec!["./examples/intLinkedList.oox"];
    assert_eq!(
        verify(&paths, "Node", "test4_invalid", Options::default_with_k(90)).unwrap().0,
        SymResult::Invalid(SourcePos::new(11, 21, 0))
    );
}

#[test]
fn sym_exec_linked_list4_if_problem() {
    let paths = vec!["./examples/intLinkedList.oox"];
    assert_eq!(
        verify(
            &paths,
            "Node",
            "test4_if_problem",
            Options::default_with_k(90)
        )
        .unwrap().0,
        SymResult::Valid
    );
}

#[test]
fn sym_exec_exceptions1() {
    let paths = vec!["./examples/exceptions.oox"];

    assert_eq!(
        verify(&paths, "Main", "test1", Options::default_with_k(20)).unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(&paths, "Main", "test1_invalid", Options::default_with_k(20)).unwrap().0,
        SymResult::Invalid(SourcePos::new(15, 21, 0))
    );
    assert_eq!(
        verify(&paths, "Main", "div", Options::default_with_k(30)).unwrap().0,
        SymResult::Valid
    );
}

#[test]
fn sym_exec_exceptions_m0() {
    let paths = vec!["./examples/exceptions.oox"];

    assert_eq!(
        verify(&paths, "Main", "m0", Options::default_with_k(20)).unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(&paths, "Main", "m0_invalid", Options::default_with_k(20)).unwrap().0,
        SymResult::Invalid(SourcePos::new(49, 17, 0))
    );
}

#[test]
fn sym_exec_exceptions_m1() {
    let paths = vec!["./examples/exceptions.oox"];

    assert_eq!(
        verify(&paths, "Main", "m1", Options::default_with_k(20)).unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(&paths, "Main", "m1_invalid", Options::default_with_k(20)).unwrap().0,
        SymResult::Invalid(SourcePos::new(68, 17, 0))
    );
}

#[test]
fn sym_exec_exceptions_m2() {
    let paths = vec!["./examples/exceptions.oox"];

    assert_eq!(
        verify(&paths, "Main", "m2", Options::default_with_k(20)).unwrap().0,
        SymResult::Valid
    );
}

#[test]
fn sym_exec_exceptions_m3() {
    let paths = vec!["./examples/exceptions.oox"];

    assert_eq!(
        verify(&paths, "Main", "m3", Options::default_with_k(30)).unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(&paths, "Main", "m3_invalid1", Options::default_with_k(30)).unwrap().0,
        SymResult::Invalid(SourcePos::new(94, 17, 0))
    );
    assert_eq!(
        verify(&paths, "Main", "m3_invalid2", Options::default_with_k(30)).unwrap().0,
        SymResult::Invalid(SourcePos::new(102, 21, 0))
    );
}

#[test]
fn sym_exec_exceptions_null() {
    let paths = vec!["./examples/exceptions.oox"];

    assert_eq!(
        verify(&paths, "Main", "nullExc1", Options::default_with_k(30)).unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(&paths, "Main", "nullExc2", Options::default_with_k(30)).unwrap().0,
        SymResult::Valid
    );
    // assert_eq!(verify_file(&file_content, "m3_invalid1", 30), SymResult::Invalid);
    // assert_eq!(verify_file(&file_content, "m3_invalid2", 30), SymResult::Invalid);
}

#[test]
fn sym_exec_array1() {
    let paths = vec!["./examples/array/array1.oox"];

    assert_eq!(
        verify(&paths, "Main", "foo", Options::default_with_k(50)).unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(&paths, "Main", "foo_invalid", Options::default_with_k(50)).unwrap().0,
        SymResult::Invalid(SourcePos::new(33, 16, 0))
    );
    assert_eq!(
        verify(&paths, "Main", "sort", Options::default_with_k(300)).unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(&paths, "Main", "sort_invalid1", Options::default_with_k(50)).unwrap().0,
        SymResult::Invalid(SourcePos::new(62, 17, 0))
    );
    assert_eq!(
        verify(&paths, "Main", "max", Options::default_with_k(50)).unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(&paths, "Main", "max_invalid1", Options::default_with_k(50)).unwrap().0,
        SymResult::Invalid(SourcePos::new(104, 21, 0))
    );
    assert_eq!(
        verify(&paths, "Main", "max_invalid2", Options::default_with_k(50)).unwrap().0,
        SymResult::Invalid(SourcePos::new(120, 17, 0))
    );
    assert_eq!(
        verify(&paths, "Main", "exists_valid", Options::default_with_k(50)).unwrap().0,
        SymResult::Valid
    );
    // assert_eq!(verify_file(&file_content, "exists_invalid1", 50), SymResult::Invalid);
    assert_eq!(
        verify(
            &paths,
            "Main",
            "exists_invalid2",
            Options::default_with_k(50)
        )
        .unwrap().0,
        SymResult::Invalid(SourcePos::new(160, 17, 0))
    );
    assert_eq!(
        verify(
            &paths,
            "Main",
            "array_creation1",
            Options::default_with_k(50)
        )
        .unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(
            &paths,
            "Main",
            "array_creation2",
            Options::default_with_k(50)
        )
        .unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(
            &paths,
            "Main",
            "array_creation_invalid",
            Options::default_with_k(50)
        )
        .unwrap().0,
        SymResult::Invalid(SourcePos::new(193, 17, 0))
    );
}

#[test]
fn sym_exec_array2() {
    let paths = vec!["./examples/array/array2.oox"];

    assert_eq!(
        verify(&paths, "Main", "foo1", Options::default_with_k(50)).unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(&paths, "Main", "foo1_invalid", Options::default_with_k(50)).unwrap().0,
        SymResult::Invalid(SourcePos::new(37, 15, 0))
    );
    assert_eq!(
        verify(&paths, "Main", "foo2_invalid", Options::default_with_k(50)).unwrap().0,
        SymResult::Invalid(SourcePos::new(51, 18, 0))
    );
    assert_eq!(
        verify(&paths, "Main", "sort", Options::default_with_k(100)).unwrap().0,
        SymResult::Valid
    );
}

#[test]
fn sym_exec_inheritance() {
    let paths = vec!["./examples/inheritance/inheritance.oox"];
    let k = 150;
    let options = Options::default_with_k(k);

    assert_eq!(
        verify(&paths, "Main", "test1", options).unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(&paths, "Main", "test1_invalid", options).unwrap().0,
        SymResult::Invalid(SourcePos::new(25, 16, 0))
    );
    assert_eq!(
        verify(&paths, "Main", "test2a", options).unwrap().0,
        SymResult::Valid
    );

    assert_eq!(
        verify(&paths, "Main", "test2b", options).unwrap().0,
        SymResult::Valid
    );

    assert_eq!(
        verify(&paths, "Main", "test2b_invalid", options).unwrap().0,
        SymResult::Invalid(SourcePos::new(68, 16, 0))
    );

    assert_eq!(
        verify(&paths, "Main", "test3", options).unwrap().0,
        SymResult::Valid
    );

    assert_eq!(
        verify(&paths, "Main", "test4_valid", options).unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(&paths, "Main", "test4_invalid", options).unwrap().0,
        SymResult::Invalid(SourcePos::new(25, 16, 0))
    );
    assert_eq!(
        verify(&paths, "Main", "test5", options).unwrap().0,
        SymResult::Valid
    );

    assert_eq!(
        verify(&paths, "Main", "test6", options).unwrap().0,
        SymResult::Valid
    );
}

#[test]
fn sym_exec_specifications_inheritance() {
    let paths = vec!["./examples/inheritance/specifications.oox"];
    let k = 150;
    let options = Options::default_with_k(k);
    assert_eq!(
        verify(&paths, "Main", "test_valid", options).unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(&paths, "Main", "test_invalid", options).unwrap().0,
        SymResult::Invalid(SourcePos::new(3, 18, 0))
    );
}

#[test]
fn sym_exec_interface() {
    let paths = vec!["./examples/inheritance/interface.oox"];
    let k = 150;
    let options = Options::default_with_k(k);

    println!("hello");

    assert_eq!(
        verify(&paths, "Main", "main", options).unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(&paths, "Main", "test1_valid", options).unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(&paths, "Main", "test1_invalid", options).unwrap().0,
        SymResult::Invalid(SourcePos::new(35, 12, 0))
    );
}

#[test]
fn sym_exec_interface2() {
    let paths = vec!["./examples/inheritance/interface2.oox"];
    let k = 150;
    let options = Options::default_with_k(k);

    assert_eq!(
        verify(&paths, "Foo", "test_valid", options).unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(&paths, "Foo1", "test_invalid", options).unwrap().0,
        SymResult::Invalid(SourcePos::new(3, 16, 0))
    );
    assert_eq!(
        verify(&paths, "Foo2", "test_valid", options).unwrap().0,
        SymResult::Valid
    );
    assert_eq!(
        verify(&paths, "Foo3", "test_invalid", options).unwrap().0,
        SymResult::Invalid(SourcePos::new(37, 16, 0))
    );
    //assert_eq!(verify(&file_content, "Foo4", "test_valid", k), SymResult::Valid);
}

#[test]
fn sym_exec_polymorphic() {
    let k = 150;
    let options = Options::default_with_k(k);
    assert_eq!(
        verify(
            &["./examples/inheritance/sym_exec_polymorphic.oox"],
            "Main",
            "main",
            options
        )
        .unwrap().0,
        SymResult::Valid
    );
}

#[test]
fn benchmark_col_25() {
    let k = 15000; // the program won't be that large
    let options = Options::default_with_k(k);
    assert_eq!(
        verify(
            &["./benchmark_programs/experiment2/defects4j/collections_25.oox"],
            "Main",
            "test",
            options
        )
        .unwrap().0,
        SymResult::Invalid(SourcePos::new(359, 21, 0))
    );
}

#[test]
fn benchmark_col_25_symbolic() {
    let k = 15000;
    let options = Options::default_with_k(k);
    assert_eq!(
        verify(
            &["./benchmark_programs/experiment2/defects4j/collections_25.oox"],
            "Main",
            "test_symbolic",
            options
        )
        .unwrap().0,
        SymResult::Invalid(SourcePos::new(402, 21, 0))
    );
}

#[test]
fn benchmark_col_25_test3() {
    let k = 15000;
    let options = Options::default_with_k(k);
    assert_eq!(
        verify(
            &["./benchmark_programs/experiment2/defects4j/collections_25.oox"],
            "Main",
            "test3",
            options
        )
        .unwrap().0,
        SymResult::Valid
    );
}

#[test]
fn any_linked_list() {
    let k = 40;
    let options = Options::default_with_k(k);
    assert_eq!(
        verify(
            &["./benchmark_programs/experiment1/1Node.oox"],
            "Main",
            "test2",
            options
        )
        .unwrap().0,
        SymResult::Valid
    );
}

#[test]
fn supertest() {
    let k = 50;
    let options = Options::default_with_k(k);
    assert_eq!(
        verify(&["./examples/supertest.oox"], "Main", "test", options).unwrap().0,
        SymResult::Valid
    )
}

#[test]
fn multiple_constructors() {
    let k = 50;
    let options = Options::default_with_k(k);
    assert_eq!(
        verify(
            &["./examples/multiple_constructors.oox"],
            "Foo",
            "test",
            options
        )
        .unwrap().0,
        SymResult::Valid
    )
}

#[test]
fn arrays3() {
    let k = 50;
    let options = Options::default_with_k(k);
    assert_eq!(
        verify(&["./examples/array/array3.oox"], "Main", "test", options).unwrap().0,
        SymResult::Valid
    )
}


#[test]
fn idk() {
    let path = &["./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/ArchiveOutputStream.oox", 
                 "./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/ArchiveEntry.oox", 
                 "./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/ArchiveStreamFactory.oox", 
                 "./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/Zip/ZipArchiveOutputStream.oox", 
                 "./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/Zip/ZipArchiveEntry.oox", 
                 "./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/Tar/TarArchiveOutputStream.oox", 
                 "./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/Tar/TarArchiveEntry.oox", 
                 "./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/Jar/JarArchiveOutputStream.oox", 
                 "./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/Jar/JarArchiveEntry.oox", 
                 "./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/Cpio/CpioArchiveOutputStream.oox", 
                 "./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/Cpio/CpioArchiveEntry.oox", 
                 "./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/Ar/ArArchiveOutputStream.oox", 
                 "./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/Ar/ArArchiveEntry.oox", 
                 "./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/StringConstants.oox", 
                 "./benchmark_programs/experiment2/defects4j/Compress/Compress_3/oox/Main.oox", 
    ];

    
    verify(path, "Main", "test_symbolic", Options::default_with_k(1000)).unwrap();
}