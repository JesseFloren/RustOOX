use std::{fmt::Display, rc::Rc};

use itertools::{Either, Itertools};
use pretty::{docs, BoxAllocator, DocAllocator, DocBuilder};

// use super::{BinOp, Expression};

use crate::{syntax::Identifier, typeable::Typeable};

use super::syntax::*;

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &'a CompilationUnit {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        docs![
            allocator,
            allocator.intersperse(
                self.members.iter().map(|decl| decl.pretty(allocator)),
                "\n\n"
            ),
        ]
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &'a Declaration {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        match self {
            Declaration::Class(class) => {
                docs![
                    allocator,
                    "class ",
                    class.name.to_string(),
                    " ",
                    class
                        .extends
                        .clone()
                        .map(|extends| format!("extends {}", extends)),
                    if !class.implements.is_empty() {
                        format!(
                            " implements {}",
                            class
                                .implements
                                .iter()
                                .map(Identifier::to_string)
                                .join(", ")
                        )
                    } else {
                        String::new()
                    },
                    allocator.softline_(),
                    "{",
                    docs![
                        allocator,
                        allocator.hardline(),
                        allocator.concat(
                            class.members.iter().map(|member| member
                                .pretty(allocator)
                                .append(allocator.hardline()))
                        )
                    ]
                    .nest(2),
                    allocator.hardline(),
                    "}"
                ]
            }
            Declaration::Interface(interface) => {
                docs![
                    allocator,
                    "interface ",
                    interface.name.to_string(),
                    " ",
                    if !interface.extends.is_empty() {
                        format!(
                            "extends {}",
                            interface
                                .extends
                                .iter()
                                .map(Identifier::to_string)
                                .join(", ")
                        )
                    } else {
                        String::new()
                    },
                    allocator.softline_(),
                    "{",
                    docs![
                        allocator,
                        allocator.hardline(),
                        allocator.concat(
                            interface.members.iter().map(|member| member
                                .pretty(allocator)
                                .append(allocator.hardline()))
                        )
                    ]
                    .nest(2),
                    allocator.hardline(),
                    "}"
                ]
            }
        }
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &'a InterfaceMember {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        match self {
            InterfaceMember::AbstractMethod(abstract_method) => abstract_method.pretty(allocator),
            InterfaceMember::DefaultMethod(method) => method.pretty(allocator),
        }
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &'a DeclarationMember {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        match self {
            DeclarationMember::Constructor(method) => pretty_constructor(method, allocator),
            DeclarationMember::Method(method) => method.pretty(allocator),
            DeclarationMember::Field { type_, name, .. } => {
                docs![
                    allocator,
                    type_.type_of().pretty(allocator),
                    " ",
                    name.to_string(),
                    ";"
                ]
            }
        }
    }
}

fn pretty_constructor<'a, D: DocAllocator<'a>>(
    method: &'a Method,
    allocator: &'a D,
) -> DocBuilder<'a, D, ()> {
    use pretty::Pretty;
    let body = method.body.borrow();
    docs![
        allocator,
        allocator.hardline(),
        method.name.to_string(),
        " ",
        pretty_parameters(&method.params, allocator),
        " {",
        docs![allocator, allocator.hardline(), body.pretty(allocator),].nest(2),
        allocator.hardline(),
        "}"
    ]
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &'a Method {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        let body = self.body.borrow();
        docs![
            allocator,
            allocator.hardline(),
            if self.is_static { "static " } else { "" },
            self.return_type.type_of(),
            " ",
            self.name.to_string(),
            pretty_parameters(&self.params, allocator),
            allocator.space(),
            specifications(&self.specification, allocator),
            "{",
            docs![allocator, allocator.hardline(), body.pretty(allocator),].nest(2),
            allocator.hardline(),
            "}"
        ]
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &'a AbstractMethod {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        docs![
            allocator,
            allocator.hardline(),
            if self.is_static { "static " } else { "" },
            self.return_type.type_of(),
            " ",
            self.name.to_string(),
            pretty_parameters(&self.params, allocator),
            allocator.space(),
            specifications(&self.specification, allocator),
            ";"
        ]
    }
}

fn specifications<'a, D: DocAllocator<'a>>(
    specification: &'a Specification,
    allocator: &'a D,
) -> DocBuilder<'a, D, ()> {
    use pretty::Pretty;
    if !(specification.requires.is_some()
        || specification.ensures.is_some()
        || specification.exceptional.is_some())
    {
        return allocator.nil();
    }

    docs![
        // specifications
        allocator,
        specification
            .requires
            .clone()
            .map(|(requires, type_requires)| docs![
                allocator,
                allocator.hardline(),
                "requires",
                "(",
                requires.pretty(allocator),
                type_requires.map(|type_guard| docs![
                    allocator,
                    ", ",
                    type_expr(&type_guard, allocator)
                ]),
                ")"
            ]),
        specification
            .ensures
            .clone()
            .map(|(ensures, type_ensures)| docs![
                allocator,
                allocator.hardline(),
                "ensures",
                "(",
                ensures.pretty(allocator),
                type_ensures.map(|type_guard| docs![
                    allocator,
                    ", ",
                    type_expr(&type_guard, allocator)
                ]),
                ")"
            ]),
        specification
            .exceptional
            .clone()
            .map(|(exceptional, type_exceptional)| docs![
                allocator,
                allocator.hardline(),
                "exceptional",
                "(",
                exceptional.pretty(allocator),
                type_exceptional.map(|type_guard| docs![
                    allocator,
                    ", ",
                    type_expr(&type_guard, allocator)
                ]),
                ")"
            ])
    ]
    .nest(2)
    .append(allocator.hardline())
}

fn pretty_parameters<'a, D: DocAllocator<'a>>(
    parameters: &'a [Parameter],
    allocator: &'a D,
) -> DocBuilder<'a, D, ()> {
    use pretty::Pretty;
    let mut parameters = parameters.iter();
    if let Some(parameter) = parameters.next() {
        let mut parameters_text = parameter.pretty(allocator);
        for parameter in parameters {
            parameters_text = parameters_text
                .append(", ")
                .append(parameter.pretty(allocator));
        }
        return parameters_text.parens();
    }
    allocator.nil().parens()
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &'a Parameter {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        docs![allocator, self.type_of(), " ", self.name.to_string()]
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &Expression {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        let comma = || allocator.text(",");
        let _colon = || allocator.text(":");

        match self {
            Expression::Var { var, .. } => allocator.text(var.to_string()),
            Expression::BinOp {
                bin_op, lhs, rhs, ..
            } => docs![
                allocator,
                lhs.pretty(allocator),
                allocator.space(),
                bin_op_to_str(bin_op),
                allocator.space(),
                rhs.pretty(allocator)
            ],

            Expression::UnOp { un_op, value, .. } => {
                let un_op_str = match un_op {
                    UnOp::Negative => "-",
                    UnOp::Negate => "!",
                };
                allocator
                    .text(un_op_str)
                    .append(value.pretty(allocator).parens())
            }
            Expression::SymbolicVar { var, .. } => {
                allocator.text("$").append(allocator.text(var.to_string()))
            }
            Expression::Lit { lit, .. } => match lit {
                Lit::NullLit => allocator.text("null"),
                Lit::BoolLit { bool_value } => allocator.text(bool_value.to_string()),
                Lit::UIntLit { uint_value } => allocator.text(uint_value.to_string()),
                Lit::IntLit { int_value } => allocator.text(int_value.to_string()),
                Lit::FloatLit { float_value } => allocator.text(float_value.to_string()),
                Lit::StringLit { string_value } => allocator.text(string_value.to_string()),
                Lit::CharLit { char_value } => allocator.text(char_value.to_string()),
            },
            Expression::SizeOf { var, .. } => allocator.text(format!("#{}", var)),
            Expression::Ref { ref_, .. } => allocator
                .text("ref")
                .append(allocator.text(ref_.to_string()).parens()),

            Expression::Conditional {
                guard,
                true_,
                false_,
                ..
            } => docs![
                allocator,
                "ite",
                "(",
                guard.as_ref(),
                comma(),
                true_.as_ref(),
                comma(),
                false_.as_ref(),
                ")"
            ]
            .parens(),
            Expression::Forall {
                elem,
                range,
                domain,
                formula,
                ..
            } => docs![
                allocator,
                "forall ",
                elem.to_string(),
                ", ",
                range.to_string(),
                ": ",
                domain.to_string(),
                ": ",
                formula.as_ref()
            ],

            Expression::Exists {
                elem,
                range,
                domain,
                formula,
                ..
            } => docs![
                allocator,
                "exists ",
                elem.to_string(),
                ", ",
                range.to_string(),
                ": ",
                domain.to_string(),
                ": ",
                formula.as_ref()
            ],

            Expression::SymbolicRef { var, .. } => allocator.text(var.to_string()),
        }
    }
}

fn if_guard<'a, D: DocAllocator<'a>>(
    assumption: Either<Rc<Expression>, TypeExpr>,
    allocator: &'a D,
) -> DocBuilder<'a, D, ()> {
    match assumption {
        Either::Left(assumption) => pretty::Pretty::pretty(assumption.as_ref(), allocator),
        Either::Right(assumption) => type_expr(&assumption, allocator),
    }
}

fn type_expr<'a, D: DocAllocator<'a>>(expr: &TypeExpr, allocator: &'a D) -> DocBuilder<'a, D, ()> {
    match expr {
        TypeExpr::InstanceOf { var, rhs, .. } => {
            docs![allocator, var.to_string(), " instanceof ", rhs]
        }
        TypeExpr::NotInstanceOf { var, rhs, .. } => {
            docs![allocator, "!", var.to_string(), " instanceof ", rhs]
        }
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &Statement {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        let semicolon = || allocator.text(";");
        match self {
            Statement::Declare { type_, var, .. } => docs![
                allocator,
                type_.type_of().to_string(),
                " ",
                var.to_string(),
                semicolon()
            ],

            Statement::Assign { lhs, rhs, .. } => docs![
                allocator,
                lhs.pretty(allocator),
                " ",
                ":=",
                " ",
                rhs.pretty(allocator),
                semicolon()
            ],

            Statement::Call { invocation, .. } => invocation.pretty(allocator).append(semicolon()),
            Statement::Fork { invocation, .. } => docs![
                allocator,
                "fork",
                " ",
                invocation.pretty(allocator),
                semicolon()
            ],
            Statement::Lock { identifier, .. } => docs![
                allocator,
                "lock",
                " ",
                identifier.to_string(),
                semicolon()
            ],
            Statement::Unlock { identifier, .. } => docs![
                allocator,
                "unlock",
                " ",
                identifier.to_string(),
                semicolon()
            ],
            Statement::Join {..} => allocator.text("join;"),
            Statement::Skip => allocator.text(";"),
            Statement::Assert { assertion, .. } => docs![
                allocator,
                "assert",
                " ",
                assertion.pretty(allocator),
                semicolon()
            ],

            Statement::Assume { assumption, .. } => docs![
                allocator,
                "assume",
                " ",
                if_guard(assumption.clone(), allocator),
                semicolon()
            ],
            Statement::While { guard, body, .. } => {
                docs![
                    allocator,
                    "while",
                    " ",
                    guard.pretty(allocator).parens(),
                    " ",
                    "{",
                    docs![allocator, allocator.hardline(), body.pretty(allocator),].nest(2),
                    allocator.hardline(),
                    "}"
                ]
            }

            Statement::Ite {
                guard,
                true_body,
                false_body,
                ..
            } => docs![
                allocator,
                "if",
                " ",
                if_guard(guard.clone(), allocator).parens(),
                " ",
                "{",
                docs![allocator, allocator.hardline(), true_body.pretty(allocator)].nest(2),
                allocator.hardline(),
                "} else  {",
                docs![
                    allocator,
                    allocator.hardline(),
                    false_body.pretty(allocator)
                ]
                .nest(2),
                allocator.hardline(),
                "}"
            ],
            Statement::Continue { .. } => allocator.text("continue;"),
            Statement::Break { .. } => allocator.text("break;"),
            Statement::Return { expression, .. } => {
                if let Some(expression) = expression {
                    allocator
                        .text("return")
                        .append(allocator.space())
                        .append(expression.pretty(allocator))
                        .append(semicolon())
                } else {
                    allocator.text("return;")
                }
            }
            Statement::Throw { message, .. } => allocator
                .text("throw ")
                .append(allocator.text(message.to_string()).double_quotes())
                .append(semicolon()),
            Statement::Try {
                try_body,
                catch_body,
                ..
            } => docs![
                allocator,
                "try",
                " ",
                try_body.pretty(allocator).braces(),
                " ",
                "catch",
                " ",
                catch_body.pretty(allocator).braces()
            ],

            Statement::Block { body } => body.pretty(allocator),
            Statement::Seq { stat1, stat2 } => docs![
                allocator,
                stat1.as_ref(),
                allocator.hardline(),
                stat2.as_ref()
            ],
        }
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &Lhs {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        match self {
            Lhs::LhsVar { var, .. } => allocator.text(var.to_string()),
            Lhs::LhsField { var, field, .. } => allocator.text(format!("{}.{}", var, field)),
            Lhs::LhsElem { var, index, .. } => allocator
                .text(var.to_string())
                .append(index.pretty(allocator).brackets()),
        }
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &Rhs {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        match self {
            Rhs::RhsExpression { value, .. } => value.pretty(allocator),
            Rhs::RhsField { var, field, .. } => {
                docs![allocator, var.as_ref(), ".", field.to_string()]
            }
            Rhs::RhsElem { var, index, .. } => var
                .pretty(allocator)
                .append(index.pretty(allocator).brackets()),
            Rhs::RhsCall { invocation, .. } => invocation.pretty(allocator),
            Rhs::RhsArray {
                sizes, array_type, ..
            } => {
                let mut result = allocator
                    .text("new ")
                    .append(array_type.type_of().pretty(allocator));
                for size in sizes {
                    result = result.append(size.pretty(allocator).brackets());
                }
                result
            }
            Rhs::RhsCast { cast_type, var, .. } => docs![
                allocator,
                cast_type.type_of().pretty(allocator).parens(),
                " ",
                var.to_string()
            ],
        }
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &Invocation {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        match self {
            Invocation::InvokeMethod {
                lhs,
                rhs,
                arguments,
                ..
            } => {
                let result = allocator
                    .text(lhs.to_string())
                    .append(allocator.text("."))
                    .append(allocator.text(rhs.to_string()));
                result.append(pretty_arguments(arguments, allocator))
            }
            Invocation::InvokeSuperMethod { rhs, arguments, .. } => {
                let result = allocator
                    .text("super")
                    .append(allocator.text("."))
                    .append(allocator.text(rhs.to_string()));

                result.append(pretty_arguments(arguments, allocator))
            }
            Invocation::InvokeConstructor {
                class_name,
                arguments,
                ..
            } => {
                let result = allocator.text("new ").append(allocator.text(class_name.to_string()));
                result.append(pretty_arguments(arguments, allocator))
            }
            Invocation::InvokeSuperConstructor { arguments, .. } => {
                let result = allocator.text("super");
                result.append(pretty_arguments(arguments, allocator))
            }
        }
    }
}

fn pretty_arguments<'a, D: DocAllocator<'a>>(
    arguments: &[Rc<Expression>],
    allocator: &'a D,
) -> DocBuilder<'a, D, ()> {
    use pretty::Pretty;
    let mut arguments = arguments.iter();
    if let Some(arg) = arguments.next() {
        let mut arguments_text = arg.pretty(allocator);
        for arg in arguments {
            arguments_text = arguments_text.append(", ").append(arg.pretty(allocator));
        }
        return arguments_text.parens();
    }
    allocator.nil().parens()
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for RuntimeType {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        (&self).pretty(allocator)
    }
}

impl<'a, D: DocAllocator<'a>> pretty::Pretty<'a, D> for &RuntimeType {
    fn pretty(self, allocator: &'a D) -> DocBuilder<'a, D, ()> {
        allocator.text(self.to_string())
    }
}

impl Display for RuntimeType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            RuntimeType::UnknownRuntimeType => write!(f, "unknown"),
            RuntimeType::VoidRuntimeType => write!(f, "void"),
            RuntimeType::UIntRuntimeType => write!(f, "unsigned int"),
            RuntimeType::IntRuntimeType => write!(f, "int"),
            RuntimeType::FloatRuntimeType => write!(f, "float"),
            RuntimeType::BoolRuntimeType => write!(f, "bool"),
            RuntimeType::StringRuntimeType => write!(f, "string"),
            RuntimeType::CharRuntimeType => write!(f, "char"),
            RuntimeType::ReferenceRuntimeType { type_ } => write!(f, "{}", type_),
            RuntimeType::ArrayRuntimeType { inner_type } => {
                write!(f, "{}[]", inner_type)
            }
            RuntimeType::ANYRuntimeType => write!(f, "any"),
            RuntimeType::NUMRuntimeType => write!(f, "NUM"),
            RuntimeType::REFRuntimeType => write!(f, "REF"),
            RuntimeType::ARRAYRuntimeType => write!(f, "ARRAY"),
        }
    }
}

impl Display for Invocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = pretty::Pretty::pretty(self, &BoxAllocator)
            .1
            .pretty(50)
            .to_string();
        f.write_str(&s)
    }
}

impl Display for Rhs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = pretty::Pretty::pretty(self, &BoxAllocator)
            .1
            .pretty(50)
            .to_string();
        f.write_str(&s)
    }
}

impl Display for Lhs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = pretty::Pretty::pretty(self, &BoxAllocator)
            .1
            .pretty(50)
            .to_string();
        f.write_str(&s)
    }
}

impl Display for Statement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = pretty::Pretty::pretty(self, &BoxAllocator)
            .1
            .pretty(50)
            .to_string();
        f.write_str(&s)
    }
}

impl Display for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = pretty::Pretty::pretty(self, &BoxAllocator)
            .1
            .pretty(50)
            .to_string();
        f.write_str(&s)
    }
}

impl Display for CompilationUnit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            pretty::Pretty::pretty(self, &pretty::BoxAllocator)
                .1
                .pretty(30)
        )
    }
}

impl std::fmt::Debug for Expression {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let s = pretty::Pretty::pretty(self, &BoxAllocator)
            .1
            .pretty(50)
            .to_string();

        f.write_str(&s)?;
        // If we are a (symbolic) ref or var of some sort also print the type.
        if matches!(
            self,
            Expression::Ref { .. }
                | Expression::SymbolicRef { .. }
                | Expression::SymbolicVar { .. }
                | Expression::Var { .. }
        ) {
            f.write_str("::")?;
            f.write_str(&self.type_of().to_string())?
        }

        Ok(())
    }
}

pub mod cfg_pretty {
    use std::{collections::HashMap, fmt::Display};

    use crate::{
        cfg::{CFGStatement, MethodIdentifier},
        exec::find_entry_for_static_invocation,
        symbol_table::SymbolTable,
    };
    use itertools::Itertools;
    use pretty::{docs, BoxAllocator, DocAllocator, DocBuilder};

    use super::if_guard;

    type ProgramCounter = u64;

    /// Pretty prints the compilation unit, with optionally a decorator to decorate each statement with a comment with additional information
    /// This can be used to display the program counter for each statement for instance.
    pub fn pretty_print_compilation_unit<F>(
        decorator: &F,
        program: &HashMap<ProgramCounter, CFGStatement>,
        flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
        st: &SymbolTable,
    ) -> String
    where
        F: Fn(u64) -> Option<String>,
    {
        let mut s = String::new();

        let class_methods = st.get_all_methods();

        let methods = class_methods
            .iter()
            .map(|(decl_name, method)| MethodIdentifier {
                method_name: method.name.to_string(),
                decl_name: decl_name.to_string(),
                arg_list: method.param_types().collect(),
            });

        for method in methods {
            let method = pretty_print_cfg_method(method, decorator, program, flow, st);
            s = format!("{}\n{}", s, method);
        }
        s
    }

    pub fn pretty_print_cfg_method<F>(
        function_entry: MethodIdentifier,
        decorator: &F,
        program: &HashMap<ProgramCounter, CFGStatement>,
        flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
        st: &SymbolTable,
    ) -> String
    where
        F: Fn(u64) -> Option<String>,
    {
        let entry = find_entry_for_static_invocation(
            &function_entry.decl_name,
            &function_entry.method_name,
            function_entry.arg_list.iter().cloned(),
            program,
            st,
        );

        pretty_print_cfg_method_from_entry(entry, decorator, program, flow)
    }

    /// A way to print a control flow graph method with additional statistics
    /// such as the CFG node id, coverage, reachability
    pub fn pretty_print_cfg_method_from_entry<F>(
        function_entry: ProgramCounter,
        decorator: &F,
        program: &HashMap<ProgramCounter, CFGStatement>,
        flow: &HashMap<ProgramCounter, Vec<ProgramCounter>>,
    ) -> String
    where
        F: Fn(u64) -> Option<String>,
    {
        let allocator = BoxAllocator;
        let mut result;

        if let CFGStatement::FunctionEntry {
            decl_name,
            method_name,
            argument_types,
        } = &program[&function_entry]
        {
            result = docs![
                &allocator,
                decl_name.to_string(),
                ".",
                method_name.to_string(),
                allocator
                    .intersperse(
                        argument_types
                            .iter()
                            .map(|t| pretty::Pretty::pretty(t, &allocator)),
                        ", "
                    )
                    .parens(),
                " {",
                decorator(function_entry).map(|decoration| { format!(" // {}", decoration) }),
            ];
            let next_statement = flow[&function_entry][0];
            let next = program
                .iter()
                .find(|(_k, v)| {
                    if let CFGStatement::Seq(a, _) = v {
                        next_statement == *a
                    } else {
                        false
                    }
                })
                .map(|(k, _)| *k)
                .unwrap_or(next_statement);

            result = result.append(
                docs![
                    &allocator,
                    allocator.hardline(),
                    pretty_print_cfg_statement(next, decorator, program, &allocator,)
                ]
                .nest(2),
            );
            // function exit
            result = result.append(docs![&allocator, allocator.hardline(), "}"]);
        } else {
            panic!("Expected function_entry to be a FunctionEntry");
        }

        line_out_comments(result.1.pretty(10).to_string())
    }

    /// Will recursively create a DocBuilder for sequential statements in the control flow graph starting from the given program
    fn pretty_print_cfg_statement<'a, F, D: pretty::DocAllocator<'a>>(
        entry: ProgramCounter,
        decorator: &'a F,
        program: &HashMap<ProgramCounter, CFGStatement>,
        allocator: &'a D,
    ) -> DocBuilder<'a, D, ()>
    where
        F: Fn(u64) -> Option<String>,
    {
        let current = entry;
        let mut result = allocator.nil();

        match &program[&entry] {
            CFGStatement::Statement(statement) => {
                result = result.append(pretty::Pretty::pretty(statement, allocator));
                if let Some(decoration) = decorator(current) {
                    result = result.append(format!(" // {}", decoration))
                }
            }
            CFGStatement::Ite(e, t, f) => {
                result = docs![
                    allocator,
                    "if (",
                    if_guard(e.clone(), allocator),
                    ") {",
                    decorator(current).map(|decoration| { format!(" // {}", decoration) }),
                    docs![
                        allocator,
                        allocator.hardline(),
                        pretty_print_cfg_statement(*t, decorator, program, allocator,),
                    ]
                    .nest(2),
                    allocator.hardline(),
                    "} else {",
                    docs![
                        allocator,
                        allocator.hardline(),
                        pretty_print_cfg_statement(*f, decorator, program, allocator),
                    ]
                    .nest(2),
                    allocator.hardline(),
                    "}"
                ];
            }
            CFGStatement::While(e, b) => {
                result = docs![
                    allocator,
                    "while (",
                    e.as_ref(),
                    ") {",
                    decorator(current).map(|decoration| { format!(" // {}", decoration) }),
                    docs![
                        allocator,
                        allocator.hardline(),
                        pretty_print_cfg_statement(*b, decorator, program, allocator,),
                    ]
                    .nest(2),
                    allocator.hardline(),
                    "}",
                ];
            }
            CFGStatement::Seq(a, b) => {
                result = pretty_print_cfg_statement(*a, decorator, program, allocator);
                result = result.append(allocator.hardline());
                result = result.append(pretty_print_cfg_statement(
                    *b, decorator, program, allocator,
                ));
            }
            CFGStatement::TryCatch(a, _b, c, _d) => {
                result = docs![
                    allocator,
                    "try {",
                    decorator(current).map(|decoration| { format!(" // {}", decoration) }),
                    pretty_print_cfg_statement(*a, decorator, program, allocator),
                    allocator.hardline(),
                    "} catch {",
                    docs![
                        allocator,
                        allocator.hardline(),
                        pretty_print_cfg_statement(*c, decorator, program, allocator),
                    ]
                    .nest(2),
                    allocator.hardline(),
                    "}"
                ];
            }
            CFGStatement::TryEntry(a) => {
                result = docs![
                    allocator,
                    allocator.hardline(),
                    pretty_print_cfg_statement(*a, decorator, program, allocator,),
                ]
                .nest(2)
            }
            CFGStatement::TryExit => (),
            CFGStatement::CatchEntry(a) => {
                result = docs![
                    allocator,
                    allocator.hardline(),
                    pretty_print_cfg_statement(*a, decorator, program, allocator,),
                ]
                .nest(2)
            }
            CFGStatement::CatchExit => (),
            CFGStatement::FunctionEntry { .. } => todo!(),
            CFGStatement::FunctionExit { .. } => todo!(),
        };

        result
    }

    /// Takes a program and ensures all comments line out for readability
    fn line_out_comments(content: String) -> String {
        let length = content
            .lines()
            .map(|l| {
                l.split_once("//")
                    .map(|(statement, _)| statement.len())
                    .unwrap_or(l.len())
            })
            .max()
            .unwrap();

        let result = content
            .lines()
            .map(|line| {
                if let Some((statement, comment)) = line.split_once("//") {
                    let fill = length - statement.len();
                    std::borrow::Cow::Owned(format!(
                        "{}{}//{}",
                        statement,
                        (0..fill).map(|_| ' ').collect::<String>(),
                        comment
                    ))
                } else {
                    std::borrow::Cow::Borrowed(line)
                }
            })
            .join("\n");

        result
    }

    impl Display for CFGStatement {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            let allocator = BoxAllocator;
            let w = 20;
            match self {
                CFGStatement::Statement(s) => {
                    pretty::Pretty::pretty(s, &allocator).1.render_fmt(w, f)
                }
                CFGStatement::Ite(e, _, _) => {
                    write!(f, "if (")?;
                    if_guard(e.clone(), &allocator).1.render_fmt(w, f)?;
                    write!(f, ") {{ .. }} else {{ .. }}")
                }
                CFGStatement::While(e, _) => {
                    write!(f, "while (")?;
                    pretty::Pretty::pretty(e.as_ref(), &allocator)
                        .1
                        .render_fmt(w, f)?;
                    write!(f, ") {{ .. }} else {{ .. }}")
                }
                CFGStatement::TryCatch(_, _, _, _) => write!(f, "try {{ .. }} catch {{ .. }}"),
                CFGStatement::TryEntry(_) => write!(f, "entry of try {{ .. }}"),
                CFGStatement::TryExit => write!(f, "exit of try {{ .. }}"),
                CFGStatement::CatchEntry(_) => write!(f, "entry of catch {{ .. }}"),
                CFGStatement::CatchExit => write!(f, "exit of catch {{ .. }}"),
                CFGStatement::Seq(_, _) => write!(f, "Seq(..)"),
                CFGStatement::FunctionEntry {
                    decl_name,
                    method_name,
                    argument_types,
                } => write!(
                    f,
                    "entry of {}.{}.{:?}",
                    decl_name, method_name, argument_types
                ),
                CFGStatement::FunctionExit {
                    decl_name,
                    method_name,
                    argument_types,
                } => write!(
                    f,
                    "exit of {}.{}.{:?}",
                    decl_name, method_name, argument_types
                ),
            }
        }
    }
}

#[test]
fn feature() {
    use crate::{language::lexer::tokens, parser::expression};
    let tokens = tokens("x && y", 0).unwrap();
    let exp = expression().parse(&tokens).unwrap();
    let allocator = pretty::BoxAllocator;
    println!("{}", pretty::Pretty::pretty(&exp, &allocator).1.pretty(10));
}

fn bin_op_to_str(bin_op: &BinOp) -> &'static str {
    match bin_op {
        BinOp::Implies => "==>",
        BinOp::And => "&&",
        BinOp::Or => "||",
        BinOp::Equal => "==",
        BinOp::NotEqual => "!=",
        BinOp::LessThan => "<",
        BinOp::LessThanEqual => "<=",
        BinOp::GreaterThan => ">",
        BinOp::GreaterThanEqual => ">=",
        BinOp::Plus => "+",
        BinOp::Minus => "-",
        BinOp::Multiply => "*",
        BinOp::Divide => "/",
        BinOp::Modulo => "%",
    }
}

use std::fmt::Debug;
impl Debug for Class {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Class")
            .field("name", &self.name)
            .field("members", &"..hidden..")
            .field("extends", &self.extends)
            .field("implements", &self.implements)
            .field("info", &self.info)
            .finish()
    }
}
