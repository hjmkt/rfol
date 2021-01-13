use crate::language::*;
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub struct FiniteModel {
    pub domain_size: u32,
    pub var_assignment: HashMap<Term, u32>,
    pub func_assignment: HashMap<NonLogicalSymbol, HashMap<Vec<u32>, u32>>,
    pub pred_assignment: HashMap<NonLogicalSymbol, HashMap<Vec<u32>, bool>>,
}

impl FiniteModel {
    pub fn new(domain_size: u32) -> FiniteModel {
        FiniteModel {
            domain_size: domain_size,
            var_assignment: HashMap::new(),
            func_assignment: HashMap::new(),
            pred_assignment: HashMap::new(),
        }
    }

    pub fn assign_var(&mut self, assign: HashMap<Term, u32>) {
        self.var_assignment.extend(assign);
    }

    pub fn assign_func(&mut self, s: NonLogicalSymbol, assign: HashMap<Vec<u32>, u32>) {
        if !self.func_assignment.contains_key(&s) {
            self.func_assignment.insert(s.clone(), hashmap![]);
        }
        let tmp = self.func_assignment.get_mut(&s).unwrap();
        tmp.extend(assign);
    }

    pub fn assign_pred(&mut self, s: NonLogicalSymbol, assign: HashMap<Vec<u32>, bool>) {
        if !self.pred_assignment.contains_key(&s) {
            self.pred_assignment.insert(s.clone(), hashmap![]);
        }
        let tmp = self.pred_assignment.get_mut(&s).unwrap();
        tmp.extend(assign);
    }
}

pub trait Model {
    fn evaluate_term(&self, term: &Term) -> u32;
    fn evaluate_formula(&mut self, fml: &Formula) -> bool;
}

impl Model for FiniteModel {
    fn evaluate_term(&self, term: &Term) -> u32 {
        match term {
            var @ Term::Var(_) => self.var_assignment[&var],
            Term::Func(name, terms) => {
                let func = NonLogicalSymbol {
                    name: name.into(),
                    arity: terms.len() as u32,
                };
                let assignment = &self.func_assignment[&func];
                let values = terms
                    .iter()
                    .map(|term| self.evaluate_term(term))
                    .collect::<Vec<u32>>();
                assignment[&values]
            }
        }
    }

    fn evaluate_formula(&mut self, fml: &Formula) -> bool {
        match fml {
            Formula::Pred(name, terms) => {
                let pred = NonLogicalSymbol {
                    name: name.into(),
                    arity: terms.len() as u32,
                };
                let assignment = &self.pred_assignment[&pred];
                let values = terms
                    .iter()
                    .map(|term| self.evaluate_term(term))
                    .collect::<Vec<u32>>();
                assignment[&values]
            }
            Formula::Equal(lhs, rhs) => self.evaluate_term(lhs) == self.evaluate_term(rhs),
            Formula::Not(bfml) => !self.evaluate_formula(bfml),
            Formula::And(lhs, rhs) => self.evaluate_formula(lhs) && self.evaluate_formula(rhs),
            Formula::Or(lhs, rhs) => self.evaluate_formula(lhs) || self.evaluate_formula(rhs),
            Formula::Forall(Term::Var(name), bfml) => (0..self.domain_size).any(|v| {
                self.var_assignment.insert(Term::Var(name.into()), v);
                self.evaluate_formula(bfml)
            }),
            Formula::Exists(Term::Var(name), bfml) => !(0..self.domain_size).any(|v| {
                self.var_assignment.insert(Term::Var(name.into()), v);
                !self.evaluate_formula(bfml)
            }),
            _ => {
                assert!(false);
                false
            }
        }
    }
}
