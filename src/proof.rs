use crate::language::*;

#[derive(Debug, Clone)]
pub struct Sequent {
    pub antecedent: Vec<Formula>,
    pub succedent: Vec<Formula>,
}

#[derive(Debug, Clone)]
pub enum LK {
    Axiom(Sequent),
    WeakeningLeft(Box<LK>, Sequent),
    WeakeningRight(Box<LK>, Sequent),
    ContractionLeft(Box<LK>, Sequent),
    ContractionRight(Box<LK>, Sequent),
    ExchangeLeft(Box<LK>, Sequent),
    ExchangeRight(Box<LK>, Sequent),
    AndLeft1(Box<LK>, Sequent),
    AndLeft2(Box<LK>, Sequent),
    AndRight(Box<[LK; 2]>, Sequent),
    OrLeft(Box<[LK; 2]>, Sequent),
    OrRight1(Box<LK>, Sequent),
    OrRight2(Box<LK>, Sequent),
    ImpliesLeft(Box<[LK; 2]>, Sequent),
    ImpliesRight(Box<LK>, Sequent),
    NotLeft(Box<LK>, Sequent),
    NotRight(Box<LK>, Sequent),
    ForallLeft(Box<LK>, Sequent),
    ForallRight(Box<LK>, Sequent),
    ExistsLeft(Box<LK>, Sequent),
    ExistsRight(Box<LK>, Sequent),
    Cut(Box<[LK; 2]>, Sequent),
}

impl LK {
    pub fn last(&self) -> &Sequent {
        use LK::*;
        match self {
            Axiom(s) => s,
            WeakeningLeft(_, s)
            | WeakeningRight(_, s)
            | ContractionLeft(_, s)
            | ContractionRight(_, s)
            | ExchangeLeft(_, s)
            | ExchangeRight(_, s)
            | AndLeft1(_, s)
            | AndLeft2(_, s)
            | AndRight(_, s)
            | OrLeft(_, s)
            | OrRight1(_, s)
            | OrRight2(_, s)
            | ImpliesLeft(_, s)
            | ImpliesRight(_, s)
            | NotLeft(_, s)
            | NotRight(_, s)
            | ForallLeft(_, s)
            | ForallRight(_, s)
            | ExistsLeft(_, s)
            | ExistsRight(_, s)
            | Cut(_, s) => s,
        }
    }
}

pub trait Proof {
    fn is_valid_inference(&self) -> bool;
}

impl Proof for LK {
    fn is_valid_inference(&self) -> bool {
        match self {
            LK::Axiom(conclusion) => conclusion.antecedent == conclusion.succedent,
            LK::WeakeningLeft(premise, conclusion) => {
                premise.last().antecedent == conclusion.antecedent[1..]
                    && premise.last().succedent == conclusion.succedent
            }
            LK::WeakeningRight(premise, conclusion) => {
                premise.last().antecedent == conclusion.antecedent
                    && premise.last().succedent == conclusion.succedent.split_last().unwrap().1
            }
            LK::ContractionLeft(premise, conclusion) => {
                premise.last().antecedent[0] == premise.last().antecedent[1]
                    && premise.last().antecedent[1..] == conclusion.antecedent
                    && premise.last().succedent == conclusion.succedent
            }
            LK::ContractionRight(premise, conclusion) => {
                premise.last().antecedent == conclusion.antecedent
                    && premise.last().succedent[premise.last().succedent.len() - 2]
                        == premise.last().succedent[conclusion.succedent.len() - 1]
                    && premise.last().succedent.split_last().unwrap().1 == conclusion.succedent
            }
            LK::ExchangeLeft(premise, conclusion) => {
                if premise.last().succedent == conclusion.succedent {
                    let mut valid = false;
                    for i in 0..premise.last().antecedent.len() - 1 {
                        if premise.last().antecedent[..i] == conclusion.antecedent[..i]
                            && premise.last().antecedent[i + 2..] == conclusion.antecedent[i + 2..]
                            && premise.last().antecedent[i] == conclusion.antecedent[i + 1]
                            && premise.last().antecedent[i + 1] == conclusion.antecedent[i]
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
                if premise.last().antecedent == conclusion.antecedent {
                    let mut valid = false;
                    for i in 0..premise.last().succedent.len() - 1 {
                        if premise.last().succedent[..i] == conclusion.succedent[..i]
                            && premise.last().succedent[i + 2..] == conclusion.succedent[i + 2..]
                            && premise.last().succedent[i] == conclusion.succedent[i + 1]
                            && premise.last().succedent[i + 1] == conclusion.succedent[i]
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
                premise.last().antecedent[1..] == conclusion.antecedent[1..]
                    && premise.last().succedent == conclusion.succedent
                    && if let Formula::And(fml, _) = &conclusion.antecedent[0] {
                        **fml == premise.last().antecedent[0]
                    } else {
                        false
                    }
            }
            LK::AndLeft2(premise, conclusion) => {
                premise.last().antecedent[1..] == conclusion.antecedent[1..]
                    && premise.last().succedent == conclusion.succedent
                    && if let Formula::And(_, fml) = &conclusion.antecedent[0] {
                        **fml == premise.last().antecedent[0]
                    } else {
                        false
                    }
            }
            LK::AndRight(premises, conclusion) => {
                let [lpremise, rpremise] = &**premises;
                lpremise.last().antecedent == conclusion.antecedent
                    && rpremise.last().antecedent == conclusion.antecedent
                    && lpremise.last().succedent.split_last().unwrap().1
                        == conclusion.succedent.split_last().unwrap().1
                    && rpremise.last().succedent.split_last().unwrap().1
                        == conclusion.succedent.split_last().unwrap().1
                    && if let Formula::And(lhs, rhs) = conclusion.succedent.last().unwrap() {
                        lpremise.last().succedent.last().unwrap() == &**lhs
                            && rpremise.last().succedent.last().unwrap() == &**rhs
                    } else {
                        false
                    }
            }
            LK::OrLeft(premises, conclusion) => {
                let [lpremise, rpremise] = &**premises;
                lpremise.last().succedent == conclusion.succedent
                    && rpremise.last().succedent == conclusion.succedent
                    && lpremise.last().antecedent[1..] == conclusion.antecedent[1..]
                    && rpremise.last().antecedent[1..] == conclusion.antecedent[1..]
                    && if let Formula::Or(lhs, rhs) = &conclusion.antecedent[0] {
                        lpremise.last().antecedent[0] == **lhs
                            && rpremise.last().antecedent[0] == **rhs
                    } else {
                        false
                    }
            }
            LK::OrRight1(premise, conclusion) => {
                premise.last().antecedent == conclusion.antecedent
                    && premise.last().succedent.split_last().unwrap().1
                        == conclusion.succedent.split_last().unwrap().1
                    && if let Formula::Or(fml, _) = conclusion.succedent.last().unwrap() {
                        &**fml == premise.last().succedent.last().unwrap()
                    } else {
                        false
                    }
            }
            LK::OrRight2(premise, conclusion) => {
                premise.last().antecedent == conclusion.antecedent
                    && premise.last().succedent.split_last().unwrap().1
                        == conclusion.succedent.split_last().unwrap().1
                    && if let Formula::Or(_, fml) = conclusion.succedent.last().unwrap() {
                        &**fml == premise.last().succedent.last().unwrap()
                    } else {
                        false
                    }
            }
            LK::ImpliesLeft(premises, conclusion) => {
                let [lpremise, rpremise] = &**premises;
                let gamma = &lpremise.last().antecedent;
                let delta = lpremise.last().succedent.split_last().unwrap().1;
                let fml1 = &lpremise.last().succedent.last().unwrap();
                let fml2 = &rpremise.last().antecedent[0];
                let pi = &rpremise.last().antecedent[1..];
                let sigma = &rpremise.last().succedent;
                conclusion.antecedent[1..] == [gamma, pi].concat()
                    && conclusion.succedent == [delta, sigma].concat()
                    && if let Formula::Implies(lhs, rhs) = &conclusion.antecedent[0]{
                        &**lhs == *fml1 && **rhs == *fml2
                    } else{
                        false
                    }
            }
            LK::ImpliesRight(premise, conclusion) => {
                premise.last().antecedent[1..] == conclusion.antecedent
                    && premise.last().succedent.split_last().unwrap().1
                        == conclusion.succedent.split_last().unwrap().1
                    && if let Formula::Implies(lhs, rhs) = conclusion.succedent.last().unwrap() {
                        **lhs == premise.last().antecedent[0]
                            && &**rhs == premise.last().succedent.last().unwrap()
                    } else {
                        false
                    }
            }
            LK::NotLeft(premise, conclusion) => {
                premise.last().antecedent == conclusion.antecedent[1..]
                    && premise.last().succedent.split_last().unwrap().1 == conclusion.succedent
                    && if let Formula::Not(fml) = &conclusion.antecedent[0] {
                        &**fml == premise.last().succedent.last().unwrap()
                    } else {
                        false
                    }
            }
            LK::NotRight(premise, conclusion) => {
                premise.last().antecedent[1..] == conclusion.antecedent
                    && premise.last().succedent == conclusion.succedent.split_last().unwrap().1
                    && if let Formula::Not(fml) = conclusion.succedent.last().unwrap() {
                        **fml == premise.last().antecedent[0]
                    } else {
                        false
                    }
            }
            LK::ForallLeft(premise, conclusion) => {
                premise.last().succedent == conclusion.succedent
                    && premise.last().antecedent[1..] == conclusion.antecedent[1..]
                    && if let Formula::Forall(var, fml) = &conclusion.antecedent[0] {
                        if !fml.get_bound_vars().contains(var) {
                            let mut valid = false;
                            for term in premise.last().antecedent[0].get_subterms() {
                                if fml.is_substitutible(var.clone(), term.clone()) {
                                    let tfml = fml.substitute(var.clone(), term);
                                    if tfml == premise.last().antecedent[0] {
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
                premise.last().antecedent == conclusion.antecedent
                    && premise.last().succedent.split_last().unwrap().1
                        == conclusion.succedent.split_last().unwrap().1
                    && if let Formula::Forall(term, fml) = &conclusion.succedent.last().unwrap() {
                        let mut valid = false;
                        for var in premise.last().succedent.last().unwrap().get_free_vars() {
                            if fml.is_substitutible(term.clone(), var.clone()) {
                                let tfml = fml.substitute(term.clone(), var.clone());
                                if &tfml == premise.last().succedent.last().unwrap() {
                                    if !premise
                                        .last()
                                        .antecedent
                                        .iter()
                                        .flat_map(|f| f.get_free_vars())
                                        .collect::<Vec<Term>>()
                                        .contains(&var.clone())
                                        && !premise
                                            .last()
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
                premise.last().antecedent == conclusion.antecedent
                    && premise.last().succedent.split_last().unwrap().1
                        == conclusion.succedent.split_last().unwrap().1
                    && if let Formula::Exists(Term::Var(s), fml) =
                        &conclusion.succedent.last().unwrap()
                    {
                        if !fml.get_bound_vars().contains(&Term::Var(s.into())) {
                            let mut valid = false;
                            for term in premise.last().succedent.last().unwrap().get_subterms() {
                                if fml.is_substitutible(Term::Var(s.into()), term.clone()) {
                                    let tfml = fml.substitute(Term::Var(s.into()), term);
                                    if &tfml == premise.last().succedent.last().unwrap() {
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
                premise.last().succedent == conclusion.succedent
                    && premise.last().antecedent[1..]
                        == conclusion.antecedent[1..]
                    && if let Formula::Exists(term, fml) = &conclusion.antecedent[0] {
                        let mut valid = false;
                        for var in premise.last().antecedent[0].get_free_vars() {
                            if fml.is_substitutible(term.clone(), var.clone()) {
                                let tfml = fml.substitute(term.clone(), var.clone());
                                if tfml == premise.last().antecedent[0] {
                                    if !premise
                                        .last()
                                        .succedent
                                        .iter()
                                        .flat_map(|f| f.get_free_vars())
                                        .collect::<Vec<Term>>()
                                        .contains(&var.clone())
                                        && !premise.last().antecedent[1..]
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
            LK::Cut(premises, conclusion) => {
                let [lpremise, rpremise] = &**premises;
                if lpremise.last().succedent.last().unwrap() == &rpremise.last().antecedent[0] {
                    let gamma = &lpremise.last().antecedent;
                    let delta = lpremise.last().succedent.split_last().unwrap().1;
                    let pi = &rpremise.last().antecedent[1..];
                    let sigma = &rpremise.last().succedent;
                    conclusion.antecedent == [gamma, delta].concat()
                        && conclusion.succedent == [pi, &sigma].concat()
                } else {
                    false
                }
            }
        }
    }
}
