use std::collections::{HashMap, HashSet};
use std::fmt;
use std::ops::Not;

/// A literal, which is a (optionally negated) variable
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Literal(usize);

impl Literal {
    fn new(variable: usize, negate: bool) -> Literal {
        Literal((variable << 1) + if negate { 1 } else { 0 })
    }

    fn variable(&self) -> usize {
        self.0 >> 1
    }

    fn is_neg(&self) -> bool {
        self.0 & 0x1 == 0x1
    }
}

impl Not for Literal {
    type Output = Literal;

    fn not(self) -> Literal {
        Literal(self.0 | 0x1)
    }
}

impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Literal({}{})",
            if self.is_neg() { "~" } else { " " },
            self.variable(),
        )
    }
}

/// A disjunction of literals
pub type Clause = Vec<Literal>;

/// An instance of the boolean satisfiability problem
pub struct Sat {
    variables: Vec<String>,
    variable_table: HashMap<String, usize>,
    clauses: Vec<Clause>,
}

impl Sat {
    /// Create a new, empty problem (no variables and no clauses)
    pub fn new() -> Sat {
        Sat {
            variables: Vec::new(),
            variable_table: HashMap::new(),
            clauses: Vec::new(),
        }
    }

    /// Return a new, unnamed variable
    pub fn new_variable(&mut self) -> Literal {
        let variable = self.variables.len();
        self.variables.push(format!("unnamed_{}", variable));
        Literal::new(variable, false)
    }

    /// Return the variable with the given name, creating it if necessary
    pub fn get_variable(&mut self, name: &str) -> Literal {
        if let Some(&variable) = self.variable_table.get(name) {
            return Literal::new(variable, false);
        }
        let variable = self.variables.len();
        self.variables.push(name.into());
        self.variable_table.insert(name.into(), variable);
        Literal::new(variable, false)
    }

    /// Return the variable with the given name or None
    pub fn get_existing_variable(&self, name: &str) -> Option<Literal> {
        self.variable_table.get(name).map(|&i| Literal::new(i, false))
    }

    /// Return all the known variables
    pub fn get_variables(&self) -> Vec<(&str, Literal)> {
        self.variables.iter()
            .enumerate()
            .map(|(i, name)| (name as &str, Literal::new(i, false)))
            .collect()
    }

    /// Add a clause (vector of literals representing a disjunction)
    pub fn add_clause(&mut self, clause: Clause) {
        self.clauses.push(clause);
    }

    /// Parse a string into a clause, adding the variables that didn't exist
    pub fn parse_and_add_clause(&mut self, text: &str) -> Result<(), ()> {
        let mut clause = Vec::new();
        let mut neg = false;
        let mut start = None;
        for (pos, chr) in text.char_indices() {
            if chr == ' ' {
                if start.is_some() {
                    let variable = self.get_variable(
                        &text[start.unwrap()..pos]
                    ).variable();
                    clause.push(Literal::new(variable, neg));
                    neg = false;
                    start = None;
                } else if neg {
                    return Err(());
                }
            } else if chr == '~' {
                if neg {
                    return Err(())
                }
                neg = true;
            } else if start.is_none() {
                start = Some(pos);
            }
        }
        if let Some(start) = start {
            let variable = self.get_variable(&text[start..]).variable();
            clause.push(Literal::new(variable, neg));
        } else if neg {
            return Err(());
        }
        self.clauses.push(clause);
        Ok(())
    }

    fn update_watchlist(
        &self,
        watchlists: &mut Vec<HashSet<usize>>,
        literal_assigned_false: usize,
        assignment: &Vec<Option<bool>>,
    ) -> bool {
        // While there are clauses watching the literal that is now false
        println!("Updating watchlist for assignment to {:?}", Literal(literal_assigned_false));
        while let Some(&clause_num) = watchlists[literal_assigned_false]
            .iter().next()
        {
            println!("Updating clause {}", clause_num);
            let mut found_alternative = false;
            for alt_literal in &self.clauses[clause_num] {
                let variable = alt_literal.variable();
                let negated = alt_literal.is_neg();
                if assignment[variable] != Some(negated) {
                    found_alternative = true;
                    watchlists[literal_assigned_false].remove(&clause_num);
                    watchlists[alt_literal.0].insert(clause_num);
                    break;
                }
            }

            if !found_alternative {
                println!("Couldn't find assignment");
                return false;
            }
        }

        true
    }

    /// Solve the problem and return a list of (Variable, bool)
    pub fn solve(&self) -> Option<Vec<(Literal, bool)>> {
        // Create the assignment, with all variables set to None
        let mut assignment = Vec::with_capacity(self.variables.len());
        for _ in 0..self.variables.len() {
            assignment.push(None);
        }

        // Create the watchlist for each literal
        let mut watchlists = Vec::with_capacity(self.variables.len() * 2);
        for _ in 0..self.variables.len() * 2 {
            watchlists.push(HashSet::new());
        }
        for (clause_num, clause) in self.clauses.iter().enumerate() {
            if let Some(literal) = clause.get(0) {
                watchlists[literal.0].insert(clause_num);
            }
        }

        // Solving
        let mut var_num = 0;
        let mut tried = Vec::new();
        for _ in 0..self.variables.len() {
            tried.push(0);
        }
        loop {
            println!("Main loop, var_num={}", var_num);

            // If we assigned all the variables, we're done
            if var_num == self.variables.len() {
                break;
            }

            // Try assigning a value to var_num
            let mut assigned = false;
            for &value in &[0, 1] {
                // If it hasn't been tried so far
                if (tried[var_num] >> value) & 1 == 0 {
                    // Assign
                    println!(
                        "Trying {} = {}",
                        self.variables[var_num],
                        value == 1,
                    );
                    assigned = true;
                    tried[var_num] |= 1 << value;
                    assignment[var_num] = Some(value == 1);
                    if !self.update_watchlist(
                        &mut watchlists,
                        (var_num << 1) | value,
                        &assignment,
                    ) {
                        // This assignment doesn't work
                        assignment[var_num] = None;
                    } else {
                        // This works, keep going with next variable
                        var_num += 1;
                        break;
                    }
                }

                // If we couldn't try any more assignments
                if !assigned {
                    if var_num == 0 {
                        // Can't backtrack anymore, there are no solutions
                        println!("No solutions!");
                        return None;
                    } else {
                        // Backtrack
                        tried[var_num] = 0;
                        assignment[var_num] = None;
                        var_num -= 1;
                        println!("Backtracking to {}", self.variables[var_num]);
                    }
                }
            }
        }

        // Build result Vec: (name, value)
        Some(
            assignment.into_iter().enumerate()
                .map(|(i, b)| (Literal::new(i, false), b.unwrap()))
                .collect()
        )
    }

    /// Solve the problem and return a list of (variable_name, bool)
    pub fn solve_named(&self) -> Option<Vec<(&str, bool)>> {
        self.solve().map(|assignment|
            self.variables
                .iter()
                .map(|s| -> &str { s })
                .zip(
                    assignment.into_iter()
                        .map(|(_, b)| b)
                ).collect()
        )
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::{Literal, Sat};

    #[test]
    fn test_parse() {
        let variable = |var_num| Literal::new(var_num, false);

        let mut sat = Sat::new();
        sat.parse_and_add_clause("").unwrap();
        assert_eq!(sat.variables, Vec::new() as Vec<String>);
        assert_eq!(sat.variable_table, HashMap::new());
        assert_eq!(sat.clauses, vec![vec![]]);

        let mut sat = Sat::new();
        sat.parse_and_add_clause("A B ~C").unwrap();
        assert_eq!(
            sat.variables,
            vec!["A", "B", "C"].into_iter().map(Into::into).collect::<Vec<String>>(),
        );
        assert_eq!(
            sat.get_variables(),
            vec![("A", variable(0)), ("B", variable(1)), ("C", variable(2))],
        );
        assert_eq!(sat.clauses, vec![vec![
            Literal::new(0, false),
            Literal::new(1, false),
            Literal::new(2, true),
        ]]);

        let mut sat = Sat::new();
        sat.parse_and_add_clause(" ~A B ").unwrap();
        assert_eq!(
            sat.variables,
            vec!["A", "B"].into_iter().map(Into::into).collect::<Vec<String>>(),
        );
        assert_eq!(sat.clauses, vec![vec![
            Literal::new(0, true),
            Literal::new(1, false),
        ]]);

        let mut sat = Sat::new();
        sat.parse_and_add_clause("A B ~").unwrap_err();
    }

    #[test]
    fn test_solve() {
        let mut sat = Sat::new();
        let a = sat.get_variable("A");
        let b = sat.get_variable("B");
        let c = sat.get_variable("C");
        sat.add_clause(vec![a, b, !c]);
        sat.add_clause(vec![b, c]);
        sat.add_clause(vec![!b]);
        sat.add_clause(vec![!a, c]);

        let assignment = sat.solve().unwrap();
        assert_eq!(
            assignment,
            vec![(a, true), (b, false), (c, true)],
        );
    }

    #[test]
    fn test_parse_solve() {
        let mut sat = Sat::new();
        sat.parse_and_add_clause(" A B ~C").unwrap();
        sat.parse_and_add_clause("   B  C").unwrap();
        sat.parse_and_add_clause("  ~B   ").unwrap();
        sat.parse_and_add_clause("~A    C").unwrap();

        let assignment = sat.solve_named().unwrap();
        assert_eq!(
            assignment,
            vec![("A", true), ("B", false), ("C", true)],
        );
    }

    #[test]
    fn test_solve_unsat() {
        let mut sat = Sat::new();
        sat.parse_and_add_clause(" A B ~C").unwrap();
        sat.parse_and_add_clause("   B  C").unwrap();
        sat.parse_and_add_clause("  ~B   ").unwrap();
        sat.parse_and_add_clause("~A    C").unwrap();
        sat.parse_and_add_clause("   B   ").unwrap();

        assert!(sat.solve().is_none());
    }
}
