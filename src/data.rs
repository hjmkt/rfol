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
    Implies,
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
    Implies(Box<Formula>, Box<Formula>),
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

    fn _get_subterms(&self, terms: &mut HashSet<Term>) {
        match self {
            Term::Func(_, subterms) => {
                for subterm in subterms {
                    terms.insert(subterm.clone());
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
            t @ Term::Var(_) => t.substitute(var, term),
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
            Formula::And(lhs, rhs) | Formula::Or(lhs, rhs) | Formula::Implies(lhs, rhs) => {
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
                    terms.insert(subterm.clone());
                }
            }
            Formula::Equal(lterm, rterm) => {
                terms.insert(lterm.clone());
                terms.insert(rterm.clone());
            }
            Formula::Not(fml) => fml._get_subterms(terms),
            Formula::And(lhs, rhs) | Formula::Or(lhs, rhs) | Formula::Implies(lhs, rhs) => {
                lhs._get_subterms(terms);
                rhs._get_subterms(terms);
            }
            Formula::Forall(_, fml) | Formula::Exists(_, fml) => {
                fml._get_subterms(terms);
            }
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

pub struct Sequent {
    pub antecedent: Vec<Formula>,
    pub succedent: Vec<Formula>,
}

pub enum LK {
    Axiom(Sequent),
    WeakeningLeft(Sequent, Sequent),
    WeakeningRight(Sequent, Sequent),
    ContractionLeft(Sequent, Sequent),
    ContractionRight(Sequent, Sequent),
    ExchangeLeft(Sequent, Sequent),
    ExchangeRight(Sequent, Sequent),
    AndLeft1(Sequent, Sequent),
    AndLeft2(Sequent, Sequent),
    AndRight([Sequent; 2], Sequent),
    OrLeft([Sequent; 2], Sequent),
    OrRight1(Sequent, Sequent),
    OrRight2(Sequent, Sequent),
    ImpliesLeft([Sequent; 2], Sequent),
    ImpliesRight(Sequent, Sequent),
    NotLeft(Sequent, Sequent),
    NotRight(Sequent, Sequent),
    ForallLeft(Sequent, Sequent),
    ForallRight(Sequent, Sequent),
    ExistsLeft(Sequent, Sequent),
    ExistsRight(Sequent, Sequent),
    Cut([Sequent; 2], Sequent),
}

impl LK {
    pub fn is_valid_inference(&self) -> bool {
        match self {
            LK::Axiom(conclusion) => conclusion.antecedent == conclusion.succedent,
            LK::WeakeningLeft(premise, conclusion) => {
                premise.antecedent == conclusion.antecedent[1..]
                    && premise.succedent == conclusion.succedent
            }
            LK::WeakeningRight(premise, conclusion) => {
                premise.antecedent == conclusion.antecedent
                    && premise.succedent == conclusion.succedent.split_last().unwrap().1
            }
            LK::ContractionLeft(premise, conclusion) => {
                premise.antecedent[0] == premise.antecedent[1]
                    && premise.antecedent[1..] == conclusion.antecedent
                    && premise.succedent == conclusion.succedent
            }
            LK::ContractionRight(premise, conclusion) => {
                premise.antecedent == conclusion.antecedent
                    && premise.succedent[premise.succedent.len() - 2]
                        == premise.succedent[conclusion.succedent.len() - 1]
                    && premise.succedent.split_last().unwrap().1 == conclusion.succedent
            }
            LK::ExchangeLeft(premise, conclusion) => {
                if premise.succedent == conclusion.succedent {
                    let mut valid = false;
                    for i in 0..premise.antecedent.len() - 1 {
                        if premise.antecedent[..i] == conclusion.antecedent[..i]
                            && premise.antecedent[i + 2..] == conclusion.antecedent[i + 2..]
                            && premise.antecedent[i] == conclusion.antecedent[i + 1]
                            && premise.antecedent[i + 1] == conclusion.antecedent[i]
                        {
                            valid = true;
                            break;
                        }
                    }
                    valid
                } else {
                    false
                }
            }
            LK::ExchangeRight(premise, conclusion) => {
                if premise.antecedent == conclusion.antecedent {
                    let mut valid = false;
                    for i in 0..premise.succedent.len() - 1 {
                        if premise.succedent[..i] == conclusion.succedent[..i]
                            && premise.succedent[i + 2..] == conclusion.succedent[i + 2..]
                            && premise.succedent[i] == conclusion.succedent[i + 1]
                            && premise.succedent[i + 1] == conclusion.succedent[i]
                        {
                            valid = true;
                            break;
                        }
                    }
                    valid
                } else {
                    false
                }
            }
            LK::AndLeft1(premise, conclusion) => {
                premise.antecedent[1..] == conclusion.antecedent[1..]
                    && premise.succedent == conclusion.succedent
                    && if let Formula::And(fml, _) = &conclusion.antecedent[0] {
                        **fml == premise.antecedent[0]
                    } else {
                        false
                    }
            }
            LK::AndLeft2(premise, conclusion) => {
                premise.antecedent[1..] == conclusion.antecedent[1..]
                    && premise.succedent == conclusion.succedent
                    && if let Formula::And(_, fml) = &conclusion.antecedent[0] {
                        **fml == premise.antecedent[0]
                    } else {
                        false
                    }
            }
            LK::AndRight([lpremise, rpremise], conclusion) => {
                lpremise.antecedent == conclusion.antecedent
                    && rpremise.antecedent == conclusion.antecedent
                    && lpremise.succedent.split_last().unwrap().1
                        == conclusion.succedent.split_last().unwrap().1
                    && rpremise.succedent.split_last().unwrap().1
                        == conclusion.succedent.split_last().unwrap().1
                    && if let Formula::And(lhs, rhs) = conclusion.succedent.last().unwrap() {
                        lpremise.succedent.last().unwrap() == &**lhs
                            && rpremise.succedent.last().unwrap() == &**rhs
                    } else {
                        false
                    }
            }
            LK::OrLeft([lpremise, rpremise], conclusion) => {
                lpremise.succedent == conclusion.succedent
                    && rpremise.succedent == conclusion.succedent
                    && lpremise.antecedent[1..] == conclusion.antecedent[1..]
                    && rpremise.antecedent[1..] == conclusion.antecedent[1..]
                    && if let Formula::Or(lhs, rhs) = &conclusion.succedent[0] {
                        lpremise.succedent[0] == **lhs && rpremise.succedent[0] == **rhs
                    } else {
                        false
                    }
            }
            LK::OrRight1(premise, conclusion) => {
                premise.antecedent == conclusion.antecedent
                    && premise.succedent.split_last().unwrap().1
                        == conclusion.succedent.split_last().unwrap().1
                    && if let Formula::Or(fml, _) = conclusion.antecedent.last().unwrap() {
                        &**fml == premise.antecedent.last().unwrap()
                    } else {
                        false
                    }
            }
            LK::OrRight2(premise, conclusion) => {
                premise.antecedent == conclusion.antecedent
                    && premise.succedent.split_last().unwrap().1
                        == conclusion.succedent.split_last().unwrap().1
                    && if let Formula::Or(_, fml) = conclusion.antecedent.last().unwrap() {
                        &**fml == premise.antecedent.last().unwrap()
                    } else {
                        false
                    }
            }
            LK::ImpliesLeft([lpremise, rpremise], conclusion) => {
                let gamma = &lpremise.antecedent;
                let delta = lpremise.succedent.split_last().unwrap().1;
                let fml1 = lpremise.succedent.last().unwrap();
                let fml2 = &rpremise.antecedent[0];
                let pi = &rpremise.antecedent[1..];
                let sigma = &rpremise.succedent;
                fml1 == fml2
                    && conclusion.antecedent == [gamma, pi].concat()
                    && conclusion.succedent == [delta, &sigma].concat()
            }
            LK::ImpliesRight(premise, conclusion) => {
                premise.antecedent[1..] == conclusion.antecedent
                    && premise.succedent.split_last().unwrap().1
                        == conclusion.succedent.split_last().unwrap().1
                    && if let Formula::Implies(lhs, rhs) = conclusion.succedent.last().unwrap() {
                        **lhs == premise.antecedent[0]
                            && &**rhs == premise.succedent.last().unwrap()
                    } else {
                        false
                    }
            }
            LK::NotLeft(premise, conclusion) => {
                premise.antecedent == conclusion.antecedent[1..]
                    && premise.succedent.split_last().unwrap().1 == conclusion.succedent
                    && if let Formula::Not(fml) = &conclusion.antecedent[0] {
                        &**fml == premise.succedent.last().unwrap()
                    } else {
                        false
                    }
            }
            LK::NotRight(premise, conclusion) => {
                premise.antecedent[1..] == conclusion.antecedent
                    && premise.succedent == conclusion.succedent.split_last().unwrap().1
                    && if let Formula::Not(fml) = conclusion.succedent.last().unwrap() {
                        **fml == premise.antecedent[0]
                    } else {
                        false
                    }
            }
            LK::ForallLeft(premise, conclusion) => {
                premise.succedent == conclusion.succedent
                    && premise.antecedent[1..] == conclusion.antecedent[1..]
                    && if let Formula::Forall(Term::Var(s), fml) = &conclusion.antecedent[0] {
                        if !fml.get_bound_vars().contains(&Term::Var(s.into())) {
                            let mut valid = false;
                            for term in fml.get_subterms() {
                                if fml.is_substitutible(Term::Var(s.into()), term.clone()) {
                                    let tfml = fml.substitute(Term::Var(s.into()), term);
                                    if tfml == premise.antecedent[0] {
                                        valid = true;
                                        break;
                                    }
                                } else {
                                    break;
                                }
                            }
                            valid
                        } else {
                            false
                        }
                    } else {
                        false
                    }
            }
            LK::ForallRight(premise, conclusion) => {
                premise.antecedent == conclusion.antecedent
                    && premise.succedent.split_last().unwrap().1
                        == conclusion.succedent.split_last().unwrap().1
                    && if let Formula::Forall(term, fml) = &conclusion.succedent.last().unwrap() {
                        let mut valid = false;
                        for var in premise.succedent.last().unwrap().get_free_vars() {
                            if fml.is_substitutible(term.clone(), var.clone()) {
                                let tfml = fml.substitute(term.clone(), var.clone());
                                if &tfml == premise.succedent.last().unwrap() {
                                    if !premise
                                        .antecedent
                                        .iter()
                                        .flat_map(|f| f.get_free_vars())
                                        .collect::<Vec<Term>>()
                                        .contains(&var.clone())
                                        && !premise
                                            .succedent
                                            .split_last()
                                            .unwrap()
                                            .1
                                            .iter()
                                            .flat_map(|f| f.get_free_vars())
                                            .collect::<Vec<Term>>()
                                            .contains(&var.clone())
                                    {
                                        valid = true;
                                        break;
                                    }
                                }
                            }
                        }
                        valid
                    } else {
                        false
                    }
            }
            LK::ExistsRight(premise, conclusion) => {
                premise.antecedent == conclusion.antecedent
                    && premise.succedent.split_last().unwrap().1
                        == conclusion.succedent.split_last().unwrap().1
                    && if let Formula::Exists(Term::Var(s), fml) =
                        &conclusion.succedent.last().unwrap()
                    {
                        if !fml.get_bound_vars().contains(&Term::Var(s.into())) {
                            let mut valid = false;
                            for term in fml.get_subterms() {
                                if fml.is_substitutible(Term::Var(s.into()), term.clone()) {
                                    let tfml = fml.substitute(Term::Var(s.into()), term);
                                    if &tfml == premise.succedent.last().unwrap() {
                                        valid = true;
                                        break;
                                    }
                                } else {
                                    break;
                                }
                            }
                            valid
                        } else {
                            false
                        }
                    } else {
                        false
                    }
            }
            LK::ExistsLeft(premise, conclusion) => {
                premise.succedent == conclusion.succedent
                    && premise.succedent.split_last().unwrap().1
                        == conclusion.succedent.split_last().unwrap().1
                    && if let Formula::Forall(term, fml) = &conclusion.antecedent[0] {
                        let mut valid = false;
                        for var in premise.antecedent[0].get_free_vars() {
                            if fml.is_substitutible(term.clone(), var.clone()) {
                                let tfml = fml.substitute(term.clone(), var.clone());
                                if tfml == premise.antecedent[0] {
                                    if !premise
                                        .succedent
                                        .iter()
                                        .flat_map(|f| f.get_free_vars())
                                        .collect::<Vec<Term>>()
                                        .contains(&var.clone())
                                        && !premise.antecedent[1..]
                                            .iter()
                                            .flat_map(|f| f.get_free_vars())
                                            .collect::<Vec<Term>>()
                                            .contains(&var.clone())
                                    {
                                        valid = true;
                                        break;
                                    }
                                }
                            }
                        }
                        valid
                    } else {
                        false
                    }
            }
            LK::Cut([lpremise, rpremise], conclusion) => {
                if lpremise.succedent.last().unwrap() == &rpremise.antecedent[0] {
                    let gamma = &lpremise.antecedent;
                    let delta = lpremise.succedent.split_last().unwrap().1;
                    let pi = &rpremise.antecedent[1..];
                    let sigma = &rpremise.succedent;
                    conclusion.antecedent == [gamma, delta].concat()
                        && conclusion.succedent == [pi, &sigma].concat()
                } else {
                    false
                }
            }
        }
    }
}
