#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    LParen,
    RParen,
    Equal,
    Not,
    And,
    Or,
    Implies,
    Symbol(String),
    Forall,
    Exists,
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Term {
    Var(String),
    Func(String, Vec<Term>),
}

macro_rules! hashset {
    () => { std::collections::HashSet::new() };
    ($( $e: expr ),*) => {{
         let mut set = ::std::collections::HashSet::new();
         $( set.insert($e); )*
         set
    }};
}

macro_rules! hashmap {
    () => { std::collections::HashMap::new() };
    ($( $key: expr => $val: expr ),*) => {{
         let mut map = ::std::collections::HashMap::new();
         $( map.insert($key, $val); )*
         map
    }};
}

macro_rules! var {
    ($name: expr) => {
        Term::Var($name.into())
    };
}

macro_rules! func{
    ($name: expr) => { Term::Func($name.into(), vec![]) };
    ($name: expr, $($args: expr),*) => { Term::Func($name.into(), vec![$( $args ),*]) };
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Formula {
    Pred(String, Vec<Term>),
    Equal(Term, Term),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Forall(Term, Box<Formula>),
    Exists(Term, Box<Formula>),
}

macro_rules! pred{
    ($name: expr) => { Box::new(Formula::Pred($name.into(), vec![])) };
    ($name: expr, $($args: expr),*) => { Box::new(Formula::Pred($name.into(), vec![$( $args ),*])) };
}
macro_rules! equal {
    ($lhs: expr, $rhs: expr) => {
        Box::new(Formula::Equal($lhs, $rhs))
    };
}
macro_rules! not {
    ($fml: expr) => {
        Box::new(Formula::Not($fml))
    };
}
macro_rules! and {
    ($lhs: expr, $rhs: expr) => {
        Box::new(Formula::And($lhs, $rhs))
    };
}
macro_rules! or {
    ($lhs: expr, $rhs: expr) => {
        Box::new(Formula::Or($lhs, $rhs))
    };
}
macro_rules! implies {
    ($lhs: expr, $rhs: expr) => {
        Box::new(Formula::Implies($lhs, $rhs))
    };
}
macro_rules! forall {
    ($var: expr, $fml: expr) => {
        Box::new(Formula::Forall($var, $fml))
    };
}
macro_rules! exists {
    ($var: expr, $fml: expr) => {
        Box::new(Formula::Exists($var, $fml))
    };
}

#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct NonLogicalSymbol {
    pub name: String,
    pub arity: u32,
}

macro_rules! nlsym {
    ($name: expr, $arity: expr) => {
        NonLogicalSymbol {
            name: $name.into(),
            arity: $arity,
        }
    };
}

use std::collections::HashSet;

impl Term {
    fn _get_vars(&self, vars: &mut HashSet<Term>) {
        match self {
            t @ Term::Var(_) => {
                vars.insert(t.clone());
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

    fn _get_subterms(&self, terms: &mut HashSet<Term>) {
        match self {
            Term::Func(_, subterms) => {
                for subterm in subterms {
                    terms.extend(subterm.get_subterms());
                }
            }
            _ => {}
        }
        terms.insert(self.clone());
    }

    pub fn get_subterms(&self) -> HashSet<Term> {
        let mut terms = HashSet::new();
        self._get_subterms(&mut terms);
        terms
    }

    pub fn substitute(&self, var: Term, term: Term) -> Term {
        match self {
            Term::Func(s, terms) => Term::Func(
                s.into(),
                terms
                    .iter()
                    .map(|t| t.substitute(var.clone(), term.clone()))
                    .collect(),
            ),
            v => {
                if v == &var {
                    term
                } else {
                    v.clone()
                }
            }
        }
    }
}

impl Formula {
    fn _group_vars(&self, free_vars: &mut HashSet<Term>, bound_vars: &mut HashSet<Term>) {
        match self {
            Formula::Forall(var, fml) | Formula::Exists(var, fml) => {
                bound_vars.insert(var.clone());
                fml._group_vars(free_vars, bound_vars);
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
            Formula::Not(fml) => {
                (*fml)._group_vars(free_vars, bound_vars);
            }
            Formula::And(lhs, rhs) | Formula::Or(lhs, rhs) | Formula::Implies(lhs, rhs) => {
                (*lhs)._group_vars(free_vars, bound_vars);
                (*rhs)._group_vars(free_vars, bound_vars);
            }
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
            Formula::Forall(_, formula) | Formula::Exists(_, formula) => formula._get_funcs(funcs),
            Formula::Pred(_, terms) => {
                funcs.extend(terms.iter().flat_map(|term| term.get_funcs()));
            }
            Formula::Equal(lhs, rhs) => {
                let terms = [lhs, rhs];
                funcs.extend(terms.iter().flat_map(|term| term.get_funcs()));
            }
            Formula::Not(fml) => (*fml)._get_funcs(funcs),
            Formula::And(lhs, rhs) | Formula::Or(lhs, rhs) | Formula::Implies(lhs, rhs) => {
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
            Formula::Forall(_, fml) | Formula::Exists(_, fml) => fml._get_preds(preds),
            Formula::Pred(name, terms) => {
                preds.insert(NonLogicalSymbol {
                    name: name.into(),
                    arity: terms.len() as u32,
                });
            }
            Formula::Not(fml) => (*fml)._get_preds(preds),
            Formula::And(lhs, rhs) | Formula::Or(lhs, rhs) | Formula::Implies(lhs, rhs) => {
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

    pub fn is_substitutible(&self, var: Term, term: Term) -> bool {
        let free_vars = self.get_free_vars();
        let bound_vars = self.get_bound_vars();
        if free_vars.contains(&var) {
            let term_vars = term.get_vars();
            term_vars.iter().any(|v| !bound_vars.contains(v))
        } else {
            true
        }
    }

    fn _get_subterms(&self, terms: &mut HashSet<Term>) {
        match self {
            Formula::Pred(_, subterms) => {
                for subterm in subterms {
                    terms.extend(subterm.get_subterms());
                }
            }
            Formula::Equal(lterm, rterm) => {
                terms.extend(lterm.get_subterms());
                terms.extend(rterm.get_subterms());
            }
            Formula::Not(fml) => fml._get_subterms(terms),
            Formula::And(lhs, rhs) | Formula::Or(lhs, rhs) | Formula::Implies(lhs, rhs) => {
                lhs._get_subterms(terms);
                rhs._get_subterms(terms);
            }
            Formula::Forall(_, fml) | Formula::Exists(_, fml) => fml._get_subterms(terms),
        }
    }

    pub fn get_subterms(&self) -> HashSet<Term> {
        let mut terms = HashSet::new();
        self._get_subterms(&mut terms);
        terms
    }

    pub fn substitute(&self, var: Term, term: Term) -> Formula {
        match self {
            Formula::Pred(s, subterms) => Formula::Pred(
                s.into(),
                subterms
                    .iter()
                    .map(|t| t.substitute(var.clone(), term.clone()))
                    .collect(),
            ),
            Formula::Equal(lterm, rterm) => Formula::Equal(
                lterm.substitute(var.clone(), term.clone()),
                rterm.substitute(var.clone(), term.clone()),
            ),
            Formula::Not(fml) => Formula::Not(Box::new((*fml).substitute(var, term))),
            Formula::And(lhs, rhs) => Formula::And(
                Box::new((*lhs).substitute(var.clone(), term.clone())),
                Box::new((*rhs).substitute(var.clone(), term.clone())),
            ),
            Formula::Or(lhs, rhs) => Formula::Or(
                Box::new((*lhs).substitute(var.clone(), term.clone())),
                Box::new((*rhs).substitute(var.clone(), term.clone())),
            ),
            Formula::Implies(lhs, rhs) => Formula::Implies(
                Box::new((*lhs).substitute(var.clone(), term.clone())),
                Box::new((*rhs).substitute(var, term)),
            ),
            Formula::Forall(var, fml) => Formula::Forall(
                var.clone(),
                Box::new((*fml).substitute(var.clone(), term.clone())),
            ),
            Formula::Exists(var, fml) => Formula::Exists(
                var.clone(),
                Box::new((*fml).substitute(var.clone(), term.clone())),
            ),
        }
    }
}
