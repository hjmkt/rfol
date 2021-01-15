use crate::language::*;
use crate::model::*;
use crate::proof::*;
use Formula::*;
use std::collections::HashMap;

fn _enumerate_vecs(vectors: Vec<Vec<u32>>, size: u32, rem_size: u32) -> Vec<Vec<u32>> {
    if rem_size == 0 {
        vectors
    } else {
        let mut new_vectors = vec![];
        for vector in vectors {
            for n in 0..size {
                let mut tmp = vector.clone();
                tmp.push(n);
                new_vectors.push(tmp);
            }
        }
        _enumerate_vecs(new_vectors, size, rem_size - 1)
    }
}

fn _enumerate_assign_func(
    assigns: Vec<HashMap<Vec<u32>, u32>>,
    vector: &[Vec<u32>],
    domain_size: u32,
) -> Vec<HashMap<Vec<u32>, u32>> {
    if vector.len() == 0 {
        assigns
    } else {
        let mut new_assigns = vec![];
        for assign in assigns {
            for n in 0..domain_size {
                let mut tmp = assign.clone();
                tmp.insert(vector[0].clone(), n);
                new_assigns.push(tmp);
            }
        }
        _enumerate_assign_func(new_assigns, &vector[1..], domain_size)
    }
}

fn enumerate_assign_func(arity: u32, domain_size: u32) -> Vec<HashMap<Vec<u32>, u32>> {
    if arity == 0 {
        let mut assigns = vec![];
        for n in 0..domain_size {
            assigns.push(assign![[] => n]);
        }
        assigns
    } else {
        let mut vectors = vec![vec![]];
        vectors = _enumerate_vecs(vectors, domain_size, arity);
        _enumerate_assign_func(vec![assign![]], &vectors[..], arity)
    }
}

fn _enumerate_assign_pred(
    assigns: Vec<HashMap<Vec<u32>, bool>>,
    vector: &[Vec<u32>],
    domain_size: u32,
) -> Vec<HashMap<Vec<u32>, bool>> {
    if vector.len() == 0 {
        assigns
    } else {
        let mut new_assigns = vec![];
        for assign in assigns {
            for b in [true, false].iter() {
                let mut tmp = assign.clone();
                tmp.insert(vector[0].clone(), *b);
                new_assigns.push(tmp);
            }
        }
        _enumerate_assign_pred(new_assigns, &vector[1..], domain_size)
    }
}

fn enumerate_assign_pred(arity: u32, domain_size: u32) -> Vec<HashMap<Vec<u32>, bool>> {
    if arity == 0 {
        let mut assigns = vec![];
        assigns.push(assign![[] => true]);
        assigns.push(assign![[] => false]);
        assigns
    } else {
        let mut vectors = vec![vec![]];
        vectors = _enumerate_vecs(vectors, domain_size, arity);
        _enumerate_assign_pred(vec![assign![]], &vectors[..], arity)
    }
}

fn _refute_on_finite_models(
    fml: &Formula,
    domain_size: u32,
    free_vars: &[Term],
    funcs: &[NonLogicalSymbol],
    preds: &[NonLogicalSymbol],
    model: &mut FiniteModel,
) -> Option<FiniteModel> {
    if !free_vars.is_empty() {
        for n in 0..domain_size {
            model.assign_var(assign![free_vars[0].clone() => n]);
            if let m @ Some(_) =
                _refute_on_finite_models(fml, domain_size, &free_vars[1..], funcs, preds, model)
            {
                return m;
            }
        }
        None
    } else if !funcs.is_empty() {
        for assign in enumerate_assign_func(funcs[0].arity, domain_size) {
            model.assign_func(funcs[0].clone(), assign);
            if let m @ Some(_) =
                _refute_on_finite_models(fml, domain_size, free_vars, &funcs[1..], preds, model)
            {
                return m;
            }
        }
        None
    } else if !preds.is_empty() {
        for assign in enumerate_assign_pred(preds[0].arity, domain_size) {
            model.assign_pred(preds[0].clone(), assign);
            if let t @ Some(_) =
                _refute_on_finite_models(fml, domain_size, free_vars, funcs, &preds[1..], model)
            {
                return t;
            }
        }
        None
    } else {
        let truth_value = model.evaluate_formula(&fml);
        if truth_value {
            None
        } else {
            Some(model.clone())
        }
    }
}

pub fn refute_on_finite_models(fml: Formula, max_domain_size: u32) -> Option<FiniteModel> {
    let free_vars = fml.get_free_vars().into_iter().collect::<Vec<Term>>();
    let funcs = fml
        .get_funcs()
        .into_iter()
        .collect::<Vec<NonLogicalSymbol>>();
    let preds = fml
        .get_preds()
        .into_iter()
        .collect::<Vec<NonLogicalSymbol>>();

    for domain_size in 0..max_domain_size + 1 {
        let mut model = FiniteModel::new(domain_size);
        if let Some(m) = _refute_on_finite_models(
            &fml,
            domain_size,
            &free_vars[..],
            &funcs[..],
            &preds[..],
            &mut model,
        ) {
            let mut model = m.clone();
            model.var_assignment.retain(|k, _| free_vars.contains(&k));
            return Some(model);
        }
    }
    None
}

fn _prove_with_lk(sequent: &Sequent, max_depth: u32, checked_sequents: &mut HashMap<Sequent, Option<LK>>) -> Option<LK>{
    if max_depth == 0{
        checked_sequents.insert(sequent.clone(), None);
        None
    } else if checked_sequents.contains_key(sequent){
        checked_sequents[sequent].clone()
    } else{
        if sequent.antecedent == sequent.succedent{
            let prf = Some(LK::Axiom(sequent.clone()));
            checked_sequents.insert(sequent.clone(), prf.clone());
            return prf;
        }
        if sequent.antecedent.len() > 0{
            match sequent.ant_first() {
                Not(bfml) => {
                    let mut parent_suc = sequent.succedent.clone();
                    let last = parent_suc.len() - 1;
                    parent_suc[last] = *bfml.clone();
                    let parent = Sequent{antecedent: sequent.antecedent.clone(), succedent: parent_suc};
                    if let Some(subprf) = _prove_with_lk(&parent, max_depth-1, checked_sequents){
                        let prf = LK::NotLeft(
                            Box::new(subprf),
                            sequent.clone()
                        );
                        checked_sequents.insert(sequent.clone(), Some(prf.clone()));
                        return Some(prf);
                    }
                    checked_sequents.insert(sequent.clone(), None);
                }
                And(lhs, rhs) => {
                    let mut parent_ant = sequent.antecedent.clone();
                    parent_ant[0] = *lhs.clone();
                    let parent = Sequent{antecedent: parent_ant.clone(), succedent: sequent.succedent.clone()};
                    if let Some(subprf) = _prove_with_lk(&parent, max_depth-1, checked_sequents){
                        let prf = LK::AndLeft1(Box::new(subprf), sequent.clone());
                        checked_sequents.insert(sequent.clone(), Some(prf.clone()));
                        return Some(prf);
                    }
                    parent_ant[0] = *rhs.clone();
                    let parent = Sequent{antecedent: parent_ant, succedent: sequent.succedent.clone()};
                    if let Some(subprf) = _prove_with_lk(&parent, max_depth-1, checked_sequents){
                        let prf = LK::AndLeft2(Box::new(subprf), sequent.clone());
                        checked_sequents.insert(sequent.clone(), Some(prf.clone()));
                        return Some(prf);
                    }
                    checked_sequents.insert(sequent.clone(), None);
                }
                Or(lhs, rhs) => {
                    let mut left_sequent = sequent.clone();
                    left_sequent.antecedent[0] = *lhs.clone();
                    let mut right_sequent = sequent.clone();
                    right_sequent.antecedent[0] = *rhs.clone();
                    if let (Some(lprf), Some(rprf)) = (_prove_with_lk(&left_sequent, max_depth-1, checked_sequents), _prove_with_lk(&right_sequent, max_depth-1, checked_sequents)){
                        let prf = LK::OrLeft(Box::new([lprf, rprf]), sequent.clone());
                        checked_sequents.insert(sequent.clone(), Some(prf.clone()));
                        return Some(prf);
                    }
                    checked_sequents.insert(sequent.clone(), None);
                }
                Implies(lhs, rhs) => {
                    let left_fmls = sequent.ant_but_first();
                    let right_fmls = sequent.succedent.clone();
                    let left_len = left_fmls.len();
                    let right_len = right_fmls.len();
                    for l in 0..left_len+1{
                        let gamma = left_fmls[..l].to_vec();
                        let pi = left_fmls[l..].to_vec();
                        for r in 0..right_len+1{
                            let delta = right_fmls[..r].to_vec();
                            let sigma = right_fmls[r..].to_vec();
                            let mut left_suc = delta;
                            left_suc.push(*lhs.clone());
                            let mut right_ant = vec![*rhs.clone()];
                            right_ant.extend(pi.clone());
                            let left_sequent = Sequent{antecedent: gamma.clone(), succedent: left_suc};
                            let right_sequent = Sequent{antecedent: right_ant, succedent: sigma.clone()};
                            if let (Some(lprf), Some(rprf)) = (_prove_with_lk(&left_sequent, max_depth-1, checked_sequents), _prove_with_lk(&right_sequent, max_depth-1, checked_sequents)){
                                let prf = LK::ImpliesLeft(Box::new([lprf, rprf]), sequent.clone());
                                checked_sequents.insert(sequent.clone(), Some(prf.clone()));
                                return Some(prf);
                            }
                        }
                    }
                    checked_sequents.insert(sequent.clone(), None);
                }
                Forall(term, bfml) => {
                    let mut parent_ant = sequent.antecedent.clone();
                    parent_ant[0] = *bfml.clone();
                    let parent = Sequent{antecedent: parent_ant, succedent: sequent.succedent.clone()};
                    let mut substitutible_terms = hashset![];
                    for fml in [sequent.antecedent.clone(), sequent.succedent.clone()].concat(){
                        let terms = fml.get_subterms();
                        substitutible_terms.extend(terms);
                    }
                    for t in substitutible_terms{
                        if parent.antecedent[0].is_substitutible(term.clone(), t.clone()){
                            let tmp_fml = parent.antecedent[0].substitute(term.clone(), t.clone());
                            let mut tmp_sequent = parent.clone();
                            tmp_sequent.antecedent[0] = tmp_fml;
                            if let Some(subprf) = _prove_with_lk(&tmp_sequent, max_depth-1, checked_sequents){
                                let prf = LK::ForallLeft(
                                    Box::new(subprf),
                                    sequent.clone()
                                );
                                checked_sequents.insert(sequent.clone(), Some(prf.clone()));
                                return Some(prf);
                            }
                        }
                    }
                    checked_sequents.insert(sequent.clone(), None);
                }
                _ => {}
            }
        }
        if sequent.succedent.len() > 0{

        }
        None
    }
}

pub fn prove_with_lk(fml: Formula, max_depth: u32) -> Option<LK>{
    let sequent = sequent!( => fml);
    let mut checked_sequents = hashmap![];
    _prove_with_lk(&sequent, max_depth, &mut checked_sequents)
}
