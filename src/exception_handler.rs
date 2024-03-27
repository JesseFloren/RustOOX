#[derive(Default, Clone, Debug)]
pub struct ExceptionHandlerStack {
    stack: Vec<ExceptionHandlerEntry>,
}

impl ExceptionHandlerStack {
    pub fn remove_last_handler(&mut self) {
        self.stack.pop();
    }
    pub fn insert_handler(&mut self, entry: ExceptionHandlerEntry) {
        self.stack.push(entry);
    }
    pub fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }
    pub fn pop_last(&mut self) -> Option<ExceptionHandlerEntry> {
        self.stack.pop()
    }

    pub fn increment_handler(&mut self) {
        if let Some(handler_entry) = self.stack.last_mut() {
            handler_entry.increment_depth_counter();
        }
    }

    pub fn decrement_handler(&mut self) {
        if let Some(handler_entry) = self.stack.last_mut() {
            handler_entry.decrement_depth_counter();
        }
    }
}

#[derive(Clone, Debug)]
pub struct ExceptionHandlerEntry {
    /// the program counter of the catch statement to return to when an exception is thrown.
    pub catch_pc: u64,
    /// defines the current depth of the call stack relative to when the try block point was entered.
    pub current_depth: u64,
}

impl ExceptionHandlerEntry {
    pub fn new(catch_pc: u64) -> ExceptionHandlerEntry {
        ExceptionHandlerEntry {
            catch_pc,
            current_depth: 0,
        }
    }

    pub fn increment_depth_counter(&mut self) {
        self.current_depth += 1;
    }

    pub fn decrement_depth_counter(&mut self) {
        self.current_depth -= 1;
    }
}
