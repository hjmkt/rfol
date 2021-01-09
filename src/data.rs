#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Term {
    Var(String),
    Func(String, Vec<Term>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    LParen,
    RParen,
    Equal,
    Not,
    And,
    Or,
    Symbol(String),
    Forall,
    Exists,
}

#[derive(Debug, PartialEq)]
pub enum Formula {
    Pred(String, Vec<Term>),
    Equal(Term, Term),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Forall(Term, Box<Formula>),
    Exists(Term, Box<Formula>),
}

use std::collections::HashSet;

impl Term {
    fn _group_vars(&self, free_vars: &mut HashSet<Term>, bound_vars: &mut HashSet<Term>) {
        match self {
            Term::Var(s) => {
                if !bound_vars.contains(&Term::Var(s.into())) {
                    free_vars.insert(Term::Var(s.into()));
                }
            }
            Term::Func(_, terms) => {
                for term in terms.iter() {
                    term._group_vars(free_vars, bound_vars);
                }
            }
        }
    }
}

impl Formula {
    fn _group_vars(&self, free_vars: &mut HashSet<Term>, bound_vars: &mut HashSet<Term>) {
        match self {
            Formula::Forall(Term::Var(s), formula) | Formula::Exists(Term::Var(s), formula) => {
                bound_vars.insert(Term::Var(s.into()));
                formula._group_vars(free_vars, bound_vars);
            }
            Formula::Pred(_, terms) => {
                for term in terms {
                    term._group_vars(free_vars, bound_vars);
                }
            }
            Formula::Equal(lhs, rhs) => {
                lhs._group_vars(free_vars, bound_vars);
                rhs._group_vars(free_vars, bound_vars);
            }
            Formula::Not(formula) => {
                (*formula)._group_vars(free_vars, bound_vars);
            }
            Formula::And(lhs, rhs) | Formula::Or(lhs, rhs) => {
                (*lhs)._group_vars(free_vars, bound_vars);
                (*rhs)._group_vars(free_vars, bound_vars);
            }
            _ => assert!(false),
        }
    }

    pub fn get_free_vars(&self) -> HashSet<Term> {
        let mut free_vars = HashSet::new();
        let mut bound_vars = HashSet::new();
        self._group_vars(&mut free_vars, &mut bound_vars);
        free_vars
    }

    pub fn get_bound_vars(&self) -> HashSet<Term> {
        let mut free_vars = HashSet::new();
        let mut bound_vars = HashSet::new();
        self._group_vars(&mut free_vars, &mut bound_vars);
        bound_vars
    }
}
