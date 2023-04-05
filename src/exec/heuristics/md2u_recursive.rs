use std::{
    collections::{HashMap, HashSet},
    thread::current,
};

use crate::{
    cfg::CFGStatement, exec::find_entry_for_static_invocation, symbol_table::SymbolTable,
    Invocation, Rhs, RuntimeType, Statement,
};

use super::{Cost, ProgramCounter};

#[derive(Debug, Hash, Eq, PartialEq, Clone)]
struct MethodIdentifier<'a> {
    method_name: &'a str,
    decl_name: &'a str,
    arg_list: Vec<RuntimeType>,
}

/// A method always has the same cost, with a distinction made between a cost achieved by finding an uncovered statement,
/// and otherwise a cost of calling the function in terms of the number of statements visited.
type Cache<'a> = HashMap<MethodIdentifier<'a>, CumulativeCost>;

/// calling a method will explore a certain number of statements before returning
/// If an uncovered statement is encountered, it will have an exact cost
/// Otherwise it returns the minimal cost of the method call in terms of the number of statements explored.
#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Clone)]
enum CumulativeCost {
    // Cost to uncovered statement
    Strict(Cost),
    // Minimal cost for calling this method.
    AtLeast(Cost),
    // Cycles back to program point, with additional cost.
    Cycle(ProgramCounter, Cost),
    Added(Box<CumulativeCost>, Box<CumulativeCost>),
    UnexploredMethodCall(String),
}

// Either<CostToUncoveredStatement, MinimalMethodCost>

impl CumulativeCost {
    fn increased_by_one(self) -> CumulativeCost {
        self.plus(1)
    }

    fn plus(self, cost: Cost) -> CumulativeCost {
        match self {
            Self::Strict(c) => Self::Strict(c + cost),
            Self::AtLeast(c) => Self::AtLeast(c + cost),
            Self::Cycle(pc, c) => Self::Cycle(pc, c + cost),
            Self::Added(c1, c2) => Self::Added(c1, Box::new(c2.plus(cost))),
            Self::UnexploredMethodCall(_) => {
                Self::Added(Box::new(self), Box::new(Self::AtLeast(cost)))
            }
        }
    }
}

/// Computes the minimal distance to uncovered methods for all program counters in this method
/// Recursively computes the minimal distance for any method calls referenced.
fn min_distance_to_uncovered_method<'a>(
    method: MethodIdentifier<'a>,
    coverage: &HashMap<ProgramCounter, usize>,
    program: &'a HashMap<ProgramCounter, CFGStatement>,
    flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
    st: &'a SymbolTable,
    visited: &mut HashSet<ProgramCounter>,
) -> (
    CumulativeCost,
    HashMap<ProgramCounter, CumulativeCost>,
    Cache<'a>,
) {
    let pc = find_entry_for_static_invocation(
        method.decl_name,
        method.method_name,
        method.arg_list.iter().cloned(),
        program,
        st,
    );
    let mut pc_to_cost = HashMap::new();
    let mut cache = Cache::new();

    let method_body_cost = min_distance_to_statement(
        pc,
        &method,
        coverage,
        program,
        flow,
        st,
        &mut pc_to_cost,
        &mut cache,
        visited,
    );

    let (is_strict, resulting_cost) = match method_body_cost {
        CumulativeCost::Strict(c) => (true, c),
        CumulativeCost::AtLeast(c) => (false, c),
        _ => panic!(),
    };
    dbg!(&pc_to_cost);

    cleanup_pc_to_cost(
        &method.method_name,
        &mut pc_to_cost,
        resulting_cost,
        is_strict,
    );

    cache.insert(method, method_body_cost.clone());

    (method_body_cost, pc_to_cost, cache)
}

/// Computes the minimal distance to uncovered methods for all program counters in this method
/// Recursively computes the minimal distance for any method calls referenced.
fn min_distance_to_statement<'a>(
    pc: ProgramCounter,
    method: &MethodIdentifier<'a>,
    coverage: &HashMap<ProgramCounter, usize>,
    program: &'a HashMap<ProgramCounter, CFGStatement>,
    flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
    st: &'a SymbolTable,
    pc_to_cost: &mut HashMap<ProgramCounter, CumulativeCost>,
    cache: &mut Cache<'a>,
    visited: &mut HashSet<ProgramCounter>,
) -> CumulativeCost {
    let statement = &program[&pc];
    dbg!(statement);
    visited.insert(pc);

    if pc_to_cost.contains_key(&pc) {
        return pc_to_cost[&pc].clone();
    }

    if let CFGStatement::FunctionExit { .. } = statement {
        // We have reached the end of the method
        let cost = if !coverage.contains_key(&pc) {
            // Uncovered statement, has strict 1 cost
            CumulativeCost::Strict(1)
        } else {
            CumulativeCost::AtLeast(1)
        };
        pc_to_cost.insert(pc, cost.clone());
        return cost.clone();
    }

    let next_pcs = &flow[&pc];
    let remaining_cost = match &next_pcs[..] {
        [] => unreachable!(),
        multiple => {
            // next cost is the minimum cost of following methods.
            let next_cost = multiple
                .iter()
                .map(|next_pc| {
                    if let CFGStatement::While(_, _) = &program[&next_pc] {
                        if visited.contains(next_pc) {
                            return CumulativeCost::Cycle(*next_pc, 0);
                        }
                    }
                    // Cycle detected (while loop or recursive function)

                    min_distance_to_statement(
                        *next_pc, &method, coverage, program, flow, st, pc_to_cost, cache, visited,
                    )
                })
                .min()
                .expect("multiple pcs");
            next_cost
        }
    };

    // Find the cost of the current statement
    let cost_of_this_statement = statement_cost(
        pc, method, coverage, program, flow, st, pc_to_cost, cache, visited,
    );

    match cost_of_this_statement.clone() {
        CumulativeCost::Strict(_) => {
            // We can short-circuit back since an uncovered statement was encountered.
            pc_to_cost.insert(pc, cost_of_this_statement.clone());
            return cost_of_this_statement;
        }
        CumulativeCost::AtLeast(cost) => {
            // Otherwise we have to check the remainder of the current method.

            let next_pcs = &flow[&pc];
            let cost = remaining_cost.plus(cost);

            // if this is a while statement, check all cycles and fix them
            if let CFGStatement::While(_, _) = &statement {
                fix_cycles(pc, cost.clone(), pc_to_cost);
            }

            pc_to_cost.insert(pc, cost.clone());
            return cost;
        }
        CumulativeCost::Cycle(_pc, _pluscost) => unimplemented!(),
        CumulativeCost::Added(_, _) => {
            let cost =
                CumulativeCost::Added(Box::new(cost_of_this_statement), Box::new(remaining_cost));

            pc_to_cost.insert(pc, cost.clone());
            return cost;
        }
        CumulativeCost::UnexploredMethodCall(_) => {
            let cost =
                CumulativeCost::Added(Box::new(cost_of_this_statement), Box::new(remaining_cost));
            pc_to_cost.insert(pc, cost.clone());
            return cost;
        }
    }
}

fn cleanup_pc_to_cost(
    method_name: &str,
    pc_to_cost: &mut HashMap<ProgramCounter, CumulativeCost>,
    resulting_cost: Cost,
    strict: bool,
) {
    let mut temp = HashMap::new();
    std::mem::swap(pc_to_cost, &mut temp);

    *pc_to_cost = temp
        .into_iter()
        .map(|(key, value)| {
            (
                key,
                replace_method_call_in_costs(method_name, value, resulting_cost, strict),
            )
        })
        .collect();
}

fn replace_method_call_in_costs(
    method_name: &str,
    cost: CumulativeCost,
    resulting_cost: Cost,
    strict: bool,
) -> CumulativeCost {
    match cost {
        CumulativeCost::Added(c1, c2) => {
            let c1 = replace_method_call_in_costs(method_name, *c1, resulting_cost, strict);
            let c2 = replace_method_call_in_costs(method_name, *c2, resulting_cost, strict);
            match (c1, c2) {
                (CumulativeCost::Strict(c1), CumulativeCost::Strict(c2))
                | (CumulativeCost::Strict(c1), CumulativeCost::AtLeast(c2))
                | (CumulativeCost::AtLeast(c1), CumulativeCost::Strict(c2)) => {
                    (CumulativeCost::Strict(c1 + c2))
                }
                (CumulativeCost::AtLeast(c1), CumulativeCost::AtLeast(c2)) => {
                    (CumulativeCost::AtLeast(c1 + c2))
                }
                (c1, c2) => todo!("{:?} {:?}", c1, c2),
            }
        }
        CumulativeCost::UnexploredMethodCall(method) if method_name == method => {
            if strict {
                (CumulativeCost::Strict(resulting_cost))
            } else {
                (CumulativeCost::AtLeast(resulting_cost))
            }
        }
        CumulativeCost::Cycle(_, _) => todo!(),
        cost => (cost),
    }
}

fn fix_cycles(
    pc: ProgramCounter,
    resulting_cost: CumulativeCost,
    pc_to_cost: &mut HashMap<ProgramCounter, CumulativeCost>,
) {
    let mut to_repair = Vec::new();

    for (k, v) in pc_to_cost.iter() {
        if let CumulativeCost::Cycle(cycle_pc, cost) = v {
            if pc == *cycle_pc {
                to_repair.push((*k, *cost));
            }
        }
    }

    for (k, cost) in to_repair {
        pc_to_cost.insert(k, resulting_cost.clone().plus(cost));
    }
}

/// Returns the cost of exploring the statement
/// Can be either strictly in case of a found uncovered statement, or at least cost otherwise.
fn statement_cost<'a>(
    pc: ProgramCounter,
    current_method: &MethodIdentifier<'a>,
    coverage: &HashMap<ProgramCounter, usize>,
    program: &'a HashMap<ProgramCounter, CFGStatement>,
    flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
    st: &'a SymbolTable,
    pc_to_cost: &mut HashMap<ProgramCounter, CumulativeCost>,
    cache: &mut Cache<'a>,
    visited: &mut HashSet<ProgramCounter>,
) -> CumulativeCost {
    let statement = &program[&pc];

    if !coverage.contains_key(&pc) {
        // Uncovered statement, has strict 1 cost
        CumulativeCost::Strict(1)
    } else if let Some(invocation) = is_method_invocation(statement) {
        // Case for a statement with an invocation.
        // An invocation has more cost than a regular statement, the resulting cost is returned.
        // If an unseen before method invocation is encountered, it will explore that first, and will add the results to the cache.
        let methods_called = methods_called(invocation);

        // Of all possible resolved methods, find the minimal cost to uncovered, or minimal cost to traverse.
        let min_method_cost = methods_called
            .into_iter()
            .map(|method| {
                // Check cache or compute cost for method
                // if method == current_method {
                //     // Recursiveness detected, have to quit.
                // }

                let cost = if let Some(cost) = cache.get(&method) {
                    cost.clone()
                } else {
                    // if method is already covered, but not in cache it means we are processing it currently.
                    let next_pc = find_entry_for_static_invocation(
                        method.decl_name,
                        method.method_name,
                        method.arg_list.iter().cloned(),
                        program,
                        st,
                    );

                    if visited.contains(&next_pc) {
                        dbg!("oh oh recursion", next_pc);
                        CumulativeCost::UnexploredMethodCall(method.method_name.to_string())
                    } else {
                        let (cost, method_pc_to_cost, method_cache) =
                            min_distance_to_uncovered_method(
                                method, coverage, program, flow, st, visited,
                            );

                        pc_to_cost.extend(method_pc_to_cost);
                        cache.extend(method_cache);
                        cost
                    }
                };
                cost.increased_by_one()
            })
            .min()
            .expect("at least one resolved method");

        min_method_cost
    } else {
        // A normal statement has at least cost 1, to be added to remainder
        CumulativeCost::AtLeast(1)
    }
}

fn is_method_invocation(statement: &CFGStatement) -> Option<&Invocation> {
    match statement {
        CFGStatement::Statement(Statement::Call { invocation, .. })
        | CFGStatement::Statement(Statement::Assign {
            rhs: Rhs::RhsCall { invocation, .. },
            ..
        }) => Some(invocation),
        _ => None,
    }
}

/// Returns a list of methods that could be called at runtime depending on the runtimetype, by this invocation.
fn methods_called(invocation: &Invocation) -> Vec<MethodIdentifier> {
    match invocation {
        Invocation::InvokeMethod { resolved, .. } => {
            // A regular method can resolve to multiple different methods due to dynamic dispatch, depending on the runtime type of the object.
            // We make here the assumption that any object can be represented and thus consider each resolved method.

            // We also need to lookup the program counter for each method. (CANT WE DO THIS BEFOREHAND?)

            let methods = resolved.as_ref().unwrap();

            methods
                .values()
                .map(|(decl, method)| MethodIdentifier {
                    method_name: &method.name,
                    decl_name: decl.name(),
                    arg_list: method.param_types().collect(),
                })
                .collect()
        }
        Invocation::InvokeSuperMethod { resolved, .. }
        | Invocation::InvokeConstructor { resolved, .. }
        | Invocation::InvokeSuperConstructor { resolved, .. } => {
            // The case where we have a single method that we resolve to.
            let (decl, method) = resolved.as_ref().unwrap().as_ref();

            vec![MethodIdentifier {
                method_name: &method.name,
                decl_name: decl.name(),
                arg_list: method.param_types().collect(),
            }]
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{cfg::labelled_statements, parse_program, typing::type_compilation_unit, utils};

    use super::*;

    fn setup(
        path: &str,
    ) -> (
        HashMap<ProgramCounter, usize>,
        HashMap<ProgramCounter, CFGStatement>,
        HashMap<ProgramCounter, Vec<u64>>,
        SymbolTable,
        HashSet<u64>,
    ) {
        let file_content = std::fs::read_to_string(path).unwrap();

        let mut coverage = HashMap::new();
        let c = parse_program(&file_content, true).unwrap();

        let symbol_table = SymbolTable::from_ast(&c).unwrap();
        let c = type_compilation_unit(c, &symbol_table).unwrap();

        let (result, flw) = labelled_statements(c);

        let program: HashMap<u64, CFGStatement> = result.into_iter().collect();

        // Simulate that the method has been explored.
        coverage.extend(program.keys().map(|k| (*k, 1usize)));
        // Except for 12 (i := i + 1)
        // coverage.remove(&12);

        // dbg!(&program);

        let flows: HashMap<u64, Vec<u64>> = utils::group_by(flw.into_iter());

        let visited = HashSet::new();
        (coverage, program, flows, symbol_table, visited)
    }

    #[test]
    fn md2u_single_while() {
        let path = "./examples/reachability/while.oox";
        let (coverage, program, flows, symbol_table, mut visited) = setup(path);

        let (cost, pc_to_cost, cache) = min_distance_to_uncovered_method(
            MethodIdentifier {
                method_name: "main",
                decl_name: "Main",
                arg_list: vec![RuntimeType::IntRuntimeType; 1],
            },
            &coverage,
            &program,
            &flows,
            &symbol_table,
            &mut visited,
        );

        let expected_result = HashMap::from([
            (2, CumulativeCost::AtLeast(6)),
            (10, CumulativeCost::AtLeast(6)),
            (12, CumulativeCost::AtLeast(5)),
            (0, CumulativeCost::AtLeast(7)),
            (8, CumulativeCost::AtLeast(4)),
            (18, CumulativeCost::AtLeast(1)),
            (5, CumulativeCost::AtLeast(5)),
            (17, CumulativeCost::AtLeast(2)),
            (15, CumulativeCost::AtLeast(3)),
        ]);

        assert_eq!(pc_to_cost, expected_result);

        dbg!(cost, pc_to_cost, cache);
    }

    #[test]
    fn md2u_recursive() {
        let path = "./examples/reachability/recursive.oox";
        let (coverage, program, flows, symbol_table, mut visited) = setup(path);

        let (cost, pc_to_cost, cache) = min_distance_to_uncovered_method(
            MethodIdentifier {
                method_name: "main",
                decl_name: "Main",
                arg_list: vec![RuntimeType::IntRuntimeType; 1],
            },
            &coverage,
            &program,
            &flows,
            &symbol_table,
            &mut visited,
        );

        let expected_result = HashMap::from([
            (25, CumulativeCost::AtLeast(3)),
            (2, CumulativeCost::AtLeast(10)),
            (11, CumulativeCost::AtLeast(1)),
            (12, CumulativeCost::AtLeast(5)),
            (10, CumulativeCost::AtLeast(2)),
            (27, CumulativeCost::AtLeast(2)),
            (8, CumulativeCost::AtLeast(8)),
            (28, CumulativeCost::AtLeast(1)),
            (21, CumulativeCost::AtLeast(8)),
            (23, CumulativeCost::AtLeast(2)),
            (5, CumulativeCost::AtLeast(9)),
            (15, CumulativeCost::AtLeast(10)),
            (13, CumulativeCost::AtLeast(4)),
            (0, CumulativeCost::AtLeast(11)),
            (18, CumulativeCost::AtLeast(9)),
        ]);

        assert_eq!(pc_to_cost, expected_result);

        dbg!(cost, pc_to_cost, cache);
    }

    #[test]
    fn md2u_nested_while() {
        let path = "./examples/reachability/nested_while.oox";
        let (coverage, program, flows, symbol_table, mut visited) = setup(path);

        let (cost, pc_to_cost, cache) = min_distance_to_uncovered_method(
            MethodIdentifier {
                method_name: "main",
                decl_name: "Main",
                arg_list: vec![RuntimeType::IntRuntimeType; 1],
            },
            &coverage,
            &program,
            &flows,
            &symbol_table,
            &mut visited,
        );

        dbg!(cost, &pc_to_cost, cache);

        let expected_result = HashMap::from([
            (22, CumulativeCost::AtLeast(6)),
            (8, CumulativeCost::AtLeast(4)),
            (2, CumulativeCost::AtLeast(6)),
            (16, CumulativeCost::AtLeast(8)),
            (5, CumulativeCost::AtLeast(5)),
            (13, CumulativeCost::AtLeast(9)),
            (10, CumulativeCost::AtLeast(10)),
            (24, CumulativeCost::AtLeast(8)),
            (0, CumulativeCost::AtLeast(7)),
            (19, CumulativeCost::AtLeast(7)),
            (26, CumulativeCost::AtLeast(7)),
            (33, CumulativeCost::AtLeast(2)),
            (31, CumulativeCost::AtLeast(3)),
            (28, CumulativeCost::AtLeast(5)),
            (34, CumulativeCost::AtLeast(1)),
        ]);

        assert_eq!(pc_to_cost, expected_result);
    }
}