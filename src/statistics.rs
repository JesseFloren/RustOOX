use std::{collections::HashSet, time::Instant};

pub struct Statistics {
    pub number_of_branches: u32,
    pub number_of_prunes: u32,
    pub number_of_complete_paths: u32,
    pub number_of_verifications: u32,
    pub number_of_local_solves: u32,
    pub number_of_z3_invocations: u32,
    pub number_of_paths_explored: u64,
    pub total_runtime: u32,
    // MPOR
    pub number_of_dep_invocations: u64,
    pub number_of_mpor_prunes: u32,
    // Coverage
    pub reachable_statements: u32,
    pub covered_statements: u32,
    pub coverage: HashSet<u64>,
    pub start_time: Instant,
}

impl Default for Statistics {
    fn default() -> Self {
        Self {
            number_of_branches: 1,
            number_of_prunes: 0,
            number_of_complete_paths: 0,
            number_of_verifications: 0,
            number_of_local_solves: 0,
            number_of_z3_invocations: 0,
            number_of_dep_invocations: 0,
            number_of_mpor_prunes: 0,
            total_runtime: 0,
            reachable_statements: 0,
            covered_statements: 0,
            coverage: HashSet::new(),
            start_time: Instant::now(),
            number_of_paths_explored: 0,
        }
    }
}

impl Statistics {
    pub fn measure_branches(&mut self, n: u32) {
        self.number_of_branches += n;
    }

    pub fn measure_prune(&mut self) {
        self.number_of_prunes += 1;
    }

    pub fn measure_finish(&mut self) {
        self.number_of_complete_paths += 1;
    }

    pub fn measure_verification(&mut self) {
        self.number_of_verifications += 1;
    }

    pub fn measure_local_solve(&mut self) {
        self.number_of_local_solves += 1;
    }

    pub fn measure_invoke_z3(&mut self) {
        self.number_of_z3_invocations += 1;
    }

    pub fn measure_mpor_prune(&mut self) {
        self.number_of_mpor_prunes += 1;
    }

    pub fn measure_dep_invocation(&mut self) {
        self.number_of_dep_invocations += 1;
    }

    pub fn measure_statement_explored(&mut self, pc: u64) {
        self.coverage.insert(pc);
        self.covered_statements = self.coverage.len() as u32;
    }
}
