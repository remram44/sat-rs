use std::collections::HashMap;

#[derive(Debug, PartialEq, Eq)]
struct Literal(usize);

impl Literal {
    fn new(variable: usize, negate: bool) -> Literal {
        Literal((variable << 1) + if negate { 1 } else { 0 })
    }

    fn pos(variable: usize) -> Literal {
        Literal(variable << 1)
    }

    fn neg(variable: usize) -> Literal {
        Literal((variable << 1) + 1)
    }

    fn negate(&self) -> Literal {
        Literal(self.0 ^ 0x1)
    }

    fn variable(&self) -> usize {
        self.0 >> 1
    }

    fn is_neg(&self) -> bool {
        self.0 & 0x1 == 0x1
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

    fn get_variable(&mut self, name: &str) -> usize {
        if let Some(&variable) = self.variable_table.get(name) {
            return variable;
        }
        let variable = self.variables.len();
        self.variables.push(name.into());
        self.variable_table.insert(name.into(), variable);
        variable
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

    use super::{Literal, Sat};

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
        assert_eq!(sat.clauses, vec![vec![Literal::pos(0), Literal::pos(1), Literal::neg(2)]]);

        let mut sat = Sat::new();
        sat.parse_and_add_clause(" ~A B ").unwrap();
        assert_eq!(
            sat.variables,
            vec!["A", "B"].into_iter().map(Into::into).collect::<Vec<String>>(),
        );
        assert_eq!(sat.clauses, vec![vec![Literal::neg(0), Literal::pos(1)]]);

        let mut sat = Sat::new();
        sat.parse_and_add_clause("A B ~").unwrap_err();
    }
}
