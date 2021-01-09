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

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
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

use std::collections::HashMap;

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
            Formula::Forall(Term::Var(name), bfml) => (0..self.domain_size)
                .map(|v| {
                    self.var_assignment.insert(Term::Var(name.into()), v);
                    self.evaluate_formula(bfml)
                })
                .any(std::convert::identity),
            Formula::Exists(Term::Var(name), bfml) => !(0..self.domain_size)
                .map(|v| {
                    self.var_assignment.insert(Term::Var(name.into()), v);
                    !self.evaluate_formula(bfml)
                })
                .any(std::convert::identity),
            _ => {
                assert!(false);
                false
            }
        }
    }
}
