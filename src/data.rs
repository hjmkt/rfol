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

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct NonLogicalSymbol {
    pub name: String,
    pub arity: u32,
}

use std::collections::HashSet;

impl Term {
    fn _get_vars(&self, vars: &mut HashSet<Term>) {
        match self {
            Term::Var(s) => {
                vars.insert(Term::Var(s.into()));
            }
            Term::Func(_, terms) => {
                terms.iter().for_each(|term| term._get_vars(vars));
            }
        }
    }

    pub fn get_vars(&self) -> HashSet<Term> {
        let mut vars: HashSet<Term> = HashSet::new();
        self._get_vars(&mut vars);
        vars
    }

    fn _get_funcs(&self, funcs: &mut HashSet<NonLogicalSymbol>) {
        match self {
            Term::Func(name, terms) => {
                funcs.insert(NonLogicalSymbol {
                    name: name.into(),
                    arity: terms.len() as u32,
                });
                terms.iter().for_each(|term| term._get_funcs(funcs));
            }
            _ => (),
        }
    }

    pub fn get_funcs(&self) -> HashSet<NonLogicalSymbol> {
        let mut funcs: HashSet<NonLogicalSymbol> = HashSet::new();
        self._get_funcs(&mut funcs);
        funcs
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
                let vars = terms
                    .iter()
                    .flat_map(|term| term.get_vars())
                    .filter(|var| !bound_vars.contains(var));
                free_vars.extend(vars);
            }
            Formula::Equal(lhs, rhs) => {
                let terms = [lhs, rhs];
                let vars = terms
                    .iter()
                    .flat_map(|term| term.get_vars())
                    .filter(|var| !bound_vars.contains(var));
                free_vars.extend(vars);
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

    fn _get_funcs(&self, funcs: &mut HashSet<NonLogicalSymbol>) {
        match self {
            Formula::Forall(_, formula) | Formula::Exists(_, formula) => {
                formula._get_funcs(funcs);
            }
            Formula::Pred(_, terms) => {
                funcs.extend(terms.iter().flat_map(|term| term.get_funcs()));
            }
            Formula::Equal(lhs, rhs) => {
                let terms = [lhs, rhs];
                funcs.extend(terms.iter().flat_map(|term| term.get_funcs()));
            }
            Formula::Not(formula) => {
                (*formula)._get_funcs(funcs);
            }
            Formula::And(lhs, rhs) | Formula::Or(lhs, rhs) => {
                (*lhs)._get_funcs(funcs);
                (*rhs)._get_funcs(funcs);
            }
        }
    }

    pub fn get_funcs(&self) -> HashSet<NonLogicalSymbol> {
        let mut funcs = HashSet::new();
        self._get_funcs(&mut funcs);
        funcs
    }

    fn _get_preds(&self, preds: &mut HashSet<NonLogicalSymbol>) {
        match self {
            Formula::Forall(_, formula) | Formula::Exists(_, formula) => {
                formula._get_preds(preds);
            }
            Formula::Pred(name, terms) => {
                preds.insert(NonLogicalSymbol {
                    name: name.into(),
                    arity: terms.len() as u32,
                });
            }
            Formula::Not(formula) => {
                (*formula)._get_preds(preds);
            }
            Formula::And(lhs, rhs) | Formula::Or(lhs, rhs) => {
                (*lhs)._get_preds(preds);
                (*rhs)._get_preds(preds);
            }
            _ => (),
        }
    }

    pub fn get_preds(&self) -> HashSet<NonLogicalSymbol> {
        let mut preds = HashSet::new();
        self._get_preds(&mut preds);
        preds
    }
}
