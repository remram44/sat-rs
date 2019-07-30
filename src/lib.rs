use std::collections::HashMap;
use std::fmt;

#[derive(Debug, PartialEq, Eq)]
struct Variable(usize);

#[derive(PartialEq, Eq)]
struct Literal(usize);

impl Literal {
    fn new(variable: Variable, negate: bool) -> Literal {
        Literal((variable.0 << 1) + if negate { 1 } else { 0 })
    }

    fn variable(&self) -> Variable {
        Variable(self.0 >> 1)
    }

    fn is_neg(&self) -> bool {
        self.0 & 0x1 == 0x1
    }
}

impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "Literal({}{})",
            if self.is_neg() { "~" } else { " " },
            self.variable().0,
        )
    }
}

type Clause = Vec<Literal>;

pub struct Sat {
    variables: Vec<String>,
    variable_table: HashMap<String, usize>,
    clauses: Vec<Clause>,
}

impl Sat {
    pub fn new() -> Sat {
        Sat {
            variables: Vec::new(),
            variable_table: HashMap::new(),
            clauses: Vec::new(),
        }
    }

    fn get_variable(&mut self, name: &str) -> Variable {
        if let Some(&variable) = self.variable_table.get(name) {
            return Variable(variable);
        }
        let variable = self.variables.len();
        self.variables.push(name.into());
        self.variable_table.insert(name.into(), variable);
        Variable(variable)
    }

    pub fn parse_and_add_clause(&mut self, text: &str) -> Result<(), ()> {
        let mut clause = Vec::new();
        let mut neg = false;
        let mut start = None;
        for (pos, chr) in text.char_indices() {
            if chr == ' ' {
                if start.is_some() {
                    let variable = self.get_variable(
                        &text[start.unwrap()..pos]
                    );
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
            let variable = self.get_variable(&text[start..]);
            clause.push(Literal::new(variable, neg));
        } else if neg {
            return Err(());
        }
        self.clauses.push(clause);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::{Literal, Variable, Sat};

    #[test]
    fn test_parse() {
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
        assert_eq!(sat.clauses, vec![vec![
            Literal::new(Variable(0), false),
            Literal::new(Variable(1), false),
            Literal::new(Variable(2), true),
        ]]);

        let mut sat = Sat::new();
        sat.parse_and_add_clause(" ~A B ").unwrap();
        assert_eq!(
            sat.variables,
            vec!["A", "B"].into_iter().map(Into::into).collect::<Vec<String>>(),
        );
        assert_eq!(sat.clauses, vec![vec![
            Literal::new(Variable(0), true),
            Literal::new(Variable(1), false),
        ]]);

        let mut sat = Sat::new();
        sat.parse_and_add_clause("A B ~").unwrap_err();
    }
}
