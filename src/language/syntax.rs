use derivative::Derivative;
use itertools::Either;
use ordered_float::NotNan;

mod classes;
mod identifier;
mod interfaces;

pub use identifier::*;

pub type Reference = i64;

pub type Float = NotNan<f64>;
use std::{cell::RefCell, collections::HashMap, fmt::Debug, ops::Deref, rc::Rc};

use crate::{cfg::MethodIdentifier, positioned::SourcePos, typeable::Typeable};

pub use self::{
    classes::Class, interfaces::find_interface_method, interfaces::Interface,
    interfaces::InterfaceMember,
};

#[derive(Debug, Derivative)]
#[derivative(PartialEq, Eq)]
pub struct CompilationUnit {
    pub members: Vec<Declaration>,
}

impl CompilationUnit {
    /// Find the first class member with given method name
    pub fn find_class_declaration_member(
        &self,
        identifier: &str,
        class_name: Option<&str>,
    ) -> Option<Rc<Method>> {
        for member in &self.members {
            if let Declaration::Class(class) = member {
                if Some(class.name.as_str()) != class_name {
                    continue;
                }
                for declaration_member in &class.members {
                    match declaration_member {
                        DeclarationMember::Constructor(method) if method.name == identifier => {
                            return Some(method.clone());
                        }
                        DeclarationMember::Method(method) if identifier == method.name => {
                            return Some(method.clone());
                        }
                        _ => (),
                    }
                }
            }
        }
        None
    }

    pub fn empty() -> CompilationUnit {
        CompilationUnit { members: vec![] }
    }

    /// Merge the members of this compilation unit with the other.
    /// Useful when combining compilation units from different files.
    pub fn merge(mut self, c: CompilationUnit) -> CompilationUnit {
        self.members.extend(c.members.into_iter());
        self
    }
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum Declaration {
    Class(Rc<Class>),
    Interface(Rc<Interface>),
}

impl Declaration {
    pub fn try_into_class(&self) -> Option<Rc<Class>> {
        if let Declaration::Class(class) = self {
            Some(class.clone())
        } else {
            None
        }
    }

    pub fn try_into_interface(&self) -> Option<Rc<Interface>> {
        if let Declaration::Interface(interface) = self {
            Some(interface.clone())
        } else {
            None
        }
    }

    pub fn name(&self) -> &Identifier {
        match self {
            Declaration::Class(class) => &class.name,
            Declaration::Interface(interface) => &interface.name,
        }
    }
}

/// Non-abstract, with concrete body
#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub struct Method {
    pub is_static: bool,
    pub return_type: Type,
    pub name: Identifier,
    pub params: Vec<Parameter>,
    pub specification: Specification,
    pub body: RefCell<Statement>, // This is a RefCell to allow interior mutability for inserting the exceptional clauses and types

    #[derivative(PartialEq = "ignore")]
    pub info: SourcePos,
}

impl Method {
    pub fn requires(&self) -> Option<(Rc<Expression>, Option<TypeExpr>)> {
        self.specification.requires.clone()
    }

    pub fn post_condition(&self) -> Option<(Rc<Expression>, Option<TypeExpr>)> {
        self.specification.ensures.clone()
    }

    pub fn exceptional(&self) -> Option<(Rc<Expression>, Option<TypeExpr>)> {
        self.specification.exceptional.clone()
    }

    pub fn param_types(&self) -> impl Iterator<Item = RuntimeType> + '_ {
        self.params.iter().map(|p| p.type_of())
    }
}

/// Abstract method, has no body implementation
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AbstractMethod {
    pub is_static: bool,
    pub return_type: Type,
    pub name: Identifier,
    pub params: Vec<Parameter>,
    pub specification: Specification,
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum DeclarationMember {
    /// Note: is_static is always false for constructors
    Constructor(Rc<Method>),
    Method(Rc<Method>),
    Field {
        type_: NonVoidType,
        name: Identifier,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
}

impl DeclarationMember {
    pub fn name(&self) -> &Identifier {
        match &self {
            DeclarationMember::Constructor(method) => &method.name,
            DeclarationMember::Method(method) => &method.name,
            DeclarationMember::Field { name, .. } => name,
        }
    }

    pub fn params(&self) -> Option<&Vec<Parameter>> {
        match &self {
            DeclarationMember::Constructor(method) => Some(&method.params),
            DeclarationMember::Method(method) => Some(&method.params),
            DeclarationMember::Field { .. } => None,
        }
    }

    pub fn method(&self) -> Option<Rc<Method>> {
        match self {
            DeclarationMember::Constructor(method) => Some(method.clone()),
            DeclarationMember::Method(method) => Some(method.clone()),
            DeclarationMember::Field { .. } => None,
        }
    }
    pub fn is_constructor(&self) -> bool {
        matches!(self, DeclarationMember::Constructor(_))
    }

    pub fn try_into_method(&self) -> Option<Rc<Method>> {
        match self {
            DeclarationMember::Method(m) => Some(m.clone()),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Derivative, Eq, PartialEq)]
pub struct Parameter {
    pub type_: NonVoidType,
    pub name: Identifier,

    #[derivative(PartialEq = "ignore")]
    pub info: SourcePos,
}

impl Parameter {
    pub fn new(type_: NonVoidType, name: Identifier) -> Parameter {
        Parameter {
            type_,
            name,
            info: SourcePos::UnknownPosition,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Specification {
    pub requires: Option<(Rc<Expression>, Option<TypeExpr>)>,
    pub ensures: Option<(Rc<Expression>, Option<TypeExpr>)>,
    pub exceptional: Option<(Rc<Expression>, Option<TypeExpr>)>,
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum Statement {
    Declare {
        type_: NonVoidType,
        var: Identifier,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Assign {
        lhs: Lhs,
        rhs: Rhs,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Call {
        invocation: Invocation,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Fork {
        invocation: Invocation,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Skip,
    Assert {
        assertion: Rc<Expression>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Assume {
        assumption: Either<Rc<Expression>, TypeExpr>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    While {
        guard: Rc<Expression>,
        body: Box<Statement>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Ite {
        guard: Either<Rc<Expression>, TypeExpr>,
        true_body: Box<Statement>,
        false_body: Box<Statement>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Continue {
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Break {
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Return {
        expression: Option<Rc<Expression>>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Throw {
        message: String,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Try {
        try_body: Box<Statement>,
        catch_body: Box<Statement>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    Block {
        body: Box<Statement>,
    },
    Seq {
        stat1: Box<Statement>,
        stat2: Box<Statement>,
    },
}

#[derive(Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum Invocation {
    /// in OOX: `f.method(..), this.method(..), Foo.method(..);`
    InvokeMethod {
        lhs: Identifier,
        rhs: Identifier,
        arguments: Vec<Rc<Expression>>,

        #[derivative(PartialEq = "ignore")]
        /// A mapping from runtime type to declaration, method pair. Also known as the Polymorphic Call Map.
        resolved: Option<HashMap<Identifier, (Declaration, Rc<Method>)>>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    /// in OOX: `super.method(..);`
    InvokeSuperMethod {
        rhs: Identifier,
        arguments: Vec<Rc<Expression>>,

        #[derivative(PartialEq = "ignore")]
        resolved: Option<Box<(Declaration, Rc<Method>)>>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    /// in OOX: `new Foo(..)`
    InvokeConstructor {
        class_name: Identifier,
        arguments: Vec<Rc<Expression>>,

        #[derivative(PartialEq = "ignore")]
        resolved: Option<Box<(Declaration, Rc<Method>)>>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    /// invocation of the constructor of the superclass. i.e. `super(..);`
    InvokeSuperConstructor {
        arguments: Vec<Rc<Expression>>,

        #[derivative(PartialEq = "ignore")]
        resolved: Option<Box<(Declaration, Rc<Method>)>>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
}

impl Invocation {
    // pub fn resolved(&self) -> Box<dyn Iterator<Item=&(Declaration, Rc<Method>)>> {
    //     match &self {
    //         Invocation::InvokeMethod { resolved, .. } => Box::new(resolved.as_ref().unwrap().iter()),
    //         Invocation::InvokeConstructor { resolved, .. } => {
    //             todo!()
    //             // Box::new(resolved.as_ref().map(Box::as_ref).map(std::iter::once))
    //         },
    //         Invocation::InvokeSuperConstructor { resolved, .. } => {
    //             todo!()
    //             // Box::new(resolved.as_ref().map(Box::as_ref))
    //         },
    //         _ => todo!(),
    //     }
    // }

    pub fn argument_types(&self) -> impl ExactSizeIterator<Item = RuntimeType> + '_ + Clone {
        self.arguments()
            .iter()
            .map(AsRef::as_ref)
            .map(Typeable::type_of)
    }

    pub fn arguments(&self) -> &Vec<Rc<Expression>> {
        match &self {
            Invocation::InvokeMethod { arguments, .. } => arguments,
            Invocation::InvokeSuperMethod { arguments, .. } => arguments,
            Invocation::InvokeConstructor { arguments, .. } => arguments,
            Invocation::InvokeSuperConstructor { arguments, .. } => arguments,
        }
    }

    pub fn identifier(&self) -> &Identifier {
        match &self {
            Invocation::InvokeMethod { rhs, .. } => rhs,
            Invocation::InvokeConstructor { class_name, .. } => class_name,
            Invocation::InvokeSuperMethod { rhs, .. } => rhs,
            _ => panic!("Invocation of super(); - does not have an identifier"),
        }
    }

    /// Returns a list of methods that could be called at runtime depending on the runtimetype, by this invocation.
    pub fn methods_called(&self) -> Vec<MethodIdentifier> {
        match self {
            Invocation::InvokeMethod { resolved, .. } => {
                // A regular method can resolve to multiple different methods due to dynamic dispatch, depending on the runtime type of the object.
                // We make here the assumption that any object can be represented and thus consider each resolved method.

                let methods = resolved.as_ref().unwrap();

                methods
                    .values()
                    .map(|(decl, method)| MethodIdentifier {
                        method_name: method.name.to_string(),
                        decl_name: decl.name().to_string(),
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
                    method_name: method.name.to_string(),
                    decl_name: decl.name().to_string(),
                    arg_list: method.param_types().collect(),
                }]
            }
        }
    }
}

impl Debug for Invocation {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvokeMethod {
                lhs,
                rhs,
                arguments,
                resolved,
                ..
            } => f
                .debug_struct("InvokeMethod")
                .field("lhs", lhs)
                .field("rhs", rhs)
                .field("arguments", arguments)
                .field("resolved", &resolved.is_some())
                .finish(),
            Self::InvokeSuperMethod {
                rhs,
                arguments,
                resolved,
                ..
            } => f
                .debug_struct("InvokeSuperMethod")
                .field("rhs", rhs)
                .field("arguments", arguments)
                .field("resolved", &resolved.is_some())
                .finish(),
            Self::InvokeConstructor {
                class_name,
                arguments,
                resolved,
                ..
            } => f
                .debug_struct("InvokeConstructor")
                .field("class_name", class_name)
                .field("arguments", arguments)
                .field("resolved", &resolved.is_some())
                .finish(),
            Self::InvokeSuperConstructor {
                arguments,
                resolved,
                ..
            } => f
                .debug_struct("InvokeSuperConstructor")
                .field("arguments", arguments)
                .field("resolved", &resolved.is_some())
                .finish(),
        }
    }
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum Lhs {
    LhsVar {
        var: Identifier,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    LhsField {
        var: Identifier,
        var_type: RuntimeType,
        field: Identifier,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    LhsElem {
        var: Identifier,
        index: Rc<Expression>,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum Rhs {
    RhsExpression {
        value: Rc<Expression>,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    RhsField {
        var: Rc<Expression>,
        field: Identifier,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    RhsElem {
        var: Rc<Expression>,
        index: Rc<Expression>,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    RhsCall {
        invocation: Invocation,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    RhsArray {
        array_type: NonVoidType,
        sizes: Vec<Rc<Expression>>,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    RhsCast {
        cast_type: NonVoidType,
        var: Identifier,

        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
}

#[derive(Clone, Derivative)]
#[derivative(PartialEq, Hash, Eq)]
pub enum Expression {
    Forall {
        elem: Identifier,
        range: Identifier,
        domain: Identifier,
        formula: Rc<Expression>,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    Exists {
        elem: Identifier,
        range: Identifier,
        domain: Identifier,
        formula: Rc<Expression>,
        type_: RuntimeType,
        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    BinOp {
        bin_op: BinOp,
        lhs: Rc<Expression>,
        rhs: Rc<Expression>,
        type_: RuntimeType,
        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    UnOp {
        un_op: UnOp,
        value: Rc<Expression>,
        type_: RuntimeType,
        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    Var {
        var: Identifier,
        type_: RuntimeType,
        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    SymbolicVar {
        // symbolic variables of primitives such as integers, boolean, floats
        var: Identifier,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    Lit {
        lit: Lit,
        type_: RuntimeType,

        #[derivative(Hash = "ignore", PartialEq = "ignore")]
        info: SourcePos,
    },
    SizeOf {
        var: Identifier,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    Ref {
        ref_: Reference,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    SymbolicRef {
        // symbolic references to arrays, objects
        var: Identifier,
        type_: RuntimeType, // If this is REFRuntimeType, this means that we have different types in the aliasmap and a state split may be necessary if we invoke a method

        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    Conditional {
        guard: Rc<Expression>,
        true_: Rc<Expression>,
        false_: Rc<Expression>,
        type_: RuntimeType,

        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
}

impl Expression {
    pub const TRUE: Expression = Expression::Lit {
        lit: Lit::BoolLit { bool_value: true },
        type_: RuntimeType::BoolRuntimeType,
        info: SourcePos::UnknownPosition,
    };
    pub const FALSE: Expression = Expression::Lit {
        lit: Lit::BoolLit { bool_value: false },
        type_: RuntimeType::BoolRuntimeType,
        info: SourcePos::UnknownPosition,
    };

    pub const NULL: Expression = Expression::Lit {
        lit: Lit::NullLit,
        type_: RuntimeType::REFRuntimeType,
        info: SourcePos::UnknownPosition,
    };

    pub fn bool(v: bool) -> Rc<Expression> {
        if v {
            Rc::new(Expression::TRUE)
        } else {
            Rc::new(Expression::FALSE)
        }
    }

    pub fn int(v: i64) -> Rc<Expression> {
        Self::int_with_info(v, SourcePos::UnknownPosition)
    }

    pub fn int_with_info(v: i64, info: SourcePos) -> Rc<Expression> {
        Rc::new(Expression::Lit {
            lit: Lit::IntLit { int_value: v },
            type_: RuntimeType::IntRuntimeType,
            info,
        })
    }

    pub fn expect_reference(&self) -> Option<Reference> {
        if let Expression::Ref { ref_, .. } = self {
            return Some(*ref_);
        }
        None
    }

    pub fn expect_symbolic_ref(&self) -> Option<Identifier> {
        if let Expression::SymbolicRef { var, .. } = self {
            return Some(var.clone());
        }
        None
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Implies,
    And,
    Or,
    Equal,
    NotEqual,
    LessThan,
    LessThanEqual,
    GreaterThan,
    GreaterThanEqual,
    Plus,
    Minus,
    Multiply,
    Divide,
    Modulo,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnOp {
    Negative,
    Negate,
}

#[derive(Debug, Clone, PartialEq, Hash)]
pub enum Lit {
    BoolLit { bool_value: bool },
    UIntLit { uint_value: u64 },
    IntLit { int_value: i64 },
    FloatLit { float_value: Float },
    StringLit { string_value: String },
    CharLit { char_value: char },
    NullLit,
}

impl Eq for Lit {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Type {
    pub type_: Option<NonVoidType>,
}

#[derive(Debug, Clone, Derivative)]
#[derivative(PartialEq, Eq)]
pub enum NonVoidType {
    UIntType {
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    IntType {
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    FloatType {
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    BoolType {
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    StringType {
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    CharType {
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    ReferenceType {
        identifier: Identifier,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
    ArrayType {
        inner_type: Box<NonVoidType>,
        #[derivative(PartialEq = "ignore")]
        info: SourcePos,
    },
}

/// The type of something at runtime
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum RuntimeType {
    /// This variant is set to types during parsing phase, and is replaced after typing check.
    UnknownRuntimeType,
    VoidRuntimeType,
    UIntRuntimeType,
    IntRuntimeType,
    FloatRuntimeType,
    BoolRuntimeType,
    StringRuntimeType,
    CharRuntimeType,
    ReferenceRuntimeType {
        type_: Identifier,
    },
    ArrayRuntimeType {
        inner_type: Box<RuntimeType>,
    },
    ANYRuntimeType,
    NUMRuntimeType,
    REFRuntimeType, // is this symbolic or something? why not use ReferenceRuntimeType
    ARRAYRuntimeType,
}

impl RuntimeType {
    /// Assumes this is a ReferenceRuntimeType and returns identifier of the reference class
    pub fn as_reference_type(&self) -> Option<&Identifier> {
        if let RuntimeType::ReferenceRuntimeType { type_ } = self {
            return Some(type_);
        }
        None
    }

    pub fn get_reference_type(&self) -> Option<Identifier> {
        self.as_reference_type().cloned()
    }

    pub fn get_inner_array_type(&self) -> Option<RuntimeType> {
        if let RuntimeType::ArrayRuntimeType { inner_type } = self {
            return Some(inner_type.deref().clone());
        }
        None
    }
}

#[derive(Clone, Derivative, Debug)]
#[derivative(PartialEq, Hash, Eq)]
pub enum TypeExpr {
    InstanceOf {
        var: Identifier,
        rhs: RuntimeType,

        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
    NotInstanceOf {
        var: Identifier,
        rhs: RuntimeType,

        #[derivative(PartialEq = "ignore", Hash = "ignore")]
        info: SourcePos,
    },
}

impl std::ops::Not for TypeExpr {
    type Output = TypeExpr;

    fn not(self) -> Self::Output {
        match self {
            TypeExpr::InstanceOf { var, rhs, info } => TypeExpr::NotInstanceOf { var, rhs, info },
            TypeExpr::NotInstanceOf { var, rhs, info } => TypeExpr::InstanceOf { var, rhs, info },
        }
    }
}
