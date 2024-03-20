use std::{collections::HashMap, rc::Rc};

use im_rc::Vector;

use crate::syntax::{Expression, Identifier, Lhs, Method};

#[derive(Clone, Debug)]
pub struct Stack(Vector<StackFrame>);

impl Stack {
    pub fn new(frames: Vector<StackFrame>) -> Stack {
        Stack(frames)
    }

    pub fn push(&mut self, stack_frame: StackFrame) {
        self.0.push_back(stack_frame);
    }

    pub fn current_stackframe(&self) -> Option<&StackFrame> {
        self.0.last()
    }

    pub fn current_variables(&self) -> Option<&HashMap<Identifier, Rc<Expression>>> {
        self.current_stackframe().map(|s| &s.params)
    }

    // Inserts a variable in the current (latest) stackframe.
    pub fn insert_variable(&mut self, var: Identifier, value: impl Into<Rc<Expression>>) {
        let stack_frame = self.0.back_mut().unwrap();

        stack_frame.params.insert(var, value.into());
    }
    /// Removes identifier with value expression from the top of the stack
    pub fn remove_variable(&mut self, identifier: &Identifier) {
        let stack_frame = self.0.back_mut().unwrap();
        stack_frame.params.remove(identifier);
    }

    pub fn lookup(&self, identifier: &Identifier) -> Option<Rc<Expression>> {
        self.current_variables().unwrap().get(identifier).cloned()
    }

    pub fn pop(&mut self) -> Option<StackFrame> {
        self.0.pop_back()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }
}

#[derive(Clone)]
pub struct StackFrame {
    pub return_pc: u64,
    /// The left hand side operation of the method call; `int x := o.f();`. Needed here to assign the method result to.
    pub returning_lhs: Option<Lhs>,
    pub params: HashMap<Identifier, Rc<Expression>>,
    pub current_member: Rc<Method>,
}

impl std::fmt::Debug for StackFrame {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("StackFrame")
            .field("return_pc", &self.return_pc)
            .field("returning_lhs", &self.returning_lhs.as_ref().map(|lhs| ToString::to_string(&lhs)))
            .field("params", &self.params)
            // .field("current_member", &self.current_member)       // omitted because the whole body will be logged.
            .finish()
    }
}
