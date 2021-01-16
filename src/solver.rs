use crate::language::*;
use crate::model::*;
use crate::proof::*;
use std::collections::HashMap;
use Formula::*;

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

    for domain_size in 1..max_domain_size + 1 {
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

fn _prove_with_lk(
    sequent: &Sequent,
    max_depth: u32,
    use_cut: bool,
    checked_sequents: &mut HashMap<Sequent, Result<LK, u32>>,
) -> Result<LK, u32> {
    if max_depth == 0 {
        //checked_sequents.insert(sequent.clone(), None);
        Err(0)
    } else if checked_sequents.contains_key(sequent)
        && match checked_sequents[sequent] {
            Ok(_) => true,
            Err(d) => max_depth <= d,
        }
    {
        checked_sequents[sequent].clone()
    } else {
        if (sequent.antecedent == sequent.succedent && sequent.antecedent.len() > 0)
            || (sequent.antecedent.is_empty()
                && sequent.succedent.len() == 1
                && match sequent.suc_last() {
                    Formula::Equal(s, t) => s == t,
                    _ => false,
                })
        {
            let prf = Ok(LK::Axiom(sequent.clone()));
            checked_sequents.insert(sequent.clone(), prf.clone());
            return prf;
        }
        if sequent.antecedent.len() > 0 {
            match sequent.ant_first() {
                Not(bfml) => {
                    let mut parent_suc = sequent.succedent.clone();
                    parent_suc.push(*bfml.clone());
                    let parent_ant = sequent.antecedent[1..].to_vec();
                    let parent = Sequent {
                        antecedent: parent_ant,
                        succedent: parent_suc,
                    };
                    if let Ok(subprf) =
                        _prove_with_lk(&parent, max_depth - 1, use_cut, checked_sequents)
                    {
                        let prf = LK::NotLeft(Box::new(subprf), sequent.clone());
                        checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                        return Ok(prf);
                    }
                    //checked_sequents.insert(sequent.clone(), None);
                }
                And(lhs, rhs) => {
                    let mut parent_ant = sequent.antecedent.clone();
                    parent_ant[0] = *lhs.clone();
                    let parent = Sequent {
                        antecedent: parent_ant.clone(),
                        succedent: sequent.succedent.clone(),
                    };
                    if let Ok(subprf) =
                        _prove_with_lk(&parent, max_depth - 1, use_cut, checked_sequents)
                    {
                        let prf = LK::AndLeft1(Box::new(subprf), sequent.clone());
                        checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                        return Ok(prf);
                    }
                    parent_ant[0] = *rhs.clone();
                    let parent = Sequent {
                        antecedent: parent_ant,
                        succedent: sequent.succedent.clone(),
                    };
                    if let Ok(subprf) =
                        _prove_with_lk(&parent, max_depth - 1, use_cut, checked_sequents)
                    {
                        let prf = LK::AndLeft2(Box::new(subprf), sequent.clone());
                        checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                        return Ok(prf);
                    }
                    //checked_sequents.insert(sequent.clone(), None);
                }
                Or(lhs, rhs) => {
                    let mut left_sequent = sequent.clone();
                    left_sequent.antecedent[0] = *lhs.clone();
                    let mut right_sequent = sequent.clone();
                    right_sequent.antecedent[0] = *rhs.clone();
                    if let (Ok(lprf), Ok(rprf)) = (
                        _prove_with_lk(&left_sequent, max_depth - 1, use_cut, checked_sequents),
                        _prove_with_lk(&right_sequent, max_depth - 1, use_cut, checked_sequents),
                    ) {
                        let prf = LK::OrLeft(Box::new([lprf, rprf]), sequent.clone());
                        checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                        return Ok(prf);
                    }
                    //checked_sequents.insert(sequent.clone(), None);
                }
                Implies(lhs, rhs) => {
                    let left_fmls = sequent.ant_but_first();
                    let right_fmls = sequent.succedent.clone();
                    let left_len = left_fmls.len();
                    let right_len = right_fmls.len();
                    for l in 0..left_len + 1 {
                        let gamma = left_fmls[..l].to_vec();
                        let pi = left_fmls[l..].to_vec();
                        for r in 0..right_len + 1 {
                            let delta = right_fmls[..r].to_vec();
                            let sigma = right_fmls[r..].to_vec();
                            let mut left_suc = delta;
                            left_suc.push(*lhs.clone());
                            let mut right_ant = vec![*rhs.clone()];
                            right_ant.extend(pi.clone());
                            let left_sequent = Sequent {
                                antecedent: gamma.clone(),
                                succedent: left_suc,
                            };
                            let right_sequent = Sequent {
                                antecedent: right_ant,
                                succedent: sigma.clone(),
                            };
                            if let (Ok(lprf), Ok(rprf)) = (
                                _prove_with_lk(
                                    &left_sequent,
                                    max_depth - 1,
                                    use_cut,
                                    checked_sequents,
                                ),
                                _prove_with_lk(
                                    &right_sequent,
                                    max_depth - 1,
                                    use_cut,
                                    checked_sequents,
                                ),
                            ) {
                                let prf = LK::ImpliesLeft(Box::new([lprf, rprf]), sequent.clone());
                                checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                                return Ok(prf);
                            }
                        }
                    }
                    //checked_sequents.insert(sequent.clone(), None);
                }
                Forall(term, bfml) => {
                    let mut parent_ant = sequent.antecedent.clone();
                    parent_ant[0] = *bfml.clone();
                    let parent = Sequent {
                        antecedent: parent_ant,
                        succedent: sequent.succedent.clone(),
                    };
                    let mut substitutible_terms = hashset![];
                    for fml in [sequent.antecedent.clone(), sequent.succedent.clone()].concat() {
                        let terms = fml.get_subterms();
                        substitutible_terms.extend(terms);
                    }
                    for t in substitutible_terms {
                        if parent.antecedent[0].is_substitutible(term.clone(), t.clone()) {
                            let tmp_fml = parent.antecedent[0].substitute(term.clone(), t.clone());
                            let mut tmp_sequent = parent.clone();
                            tmp_sequent.antecedent[0] = tmp_fml;
                            if let Ok(subprf) = _prove_with_lk(
                                &tmp_sequent,
                                max_depth - 1,
                                use_cut,
                                checked_sequents,
                            ) {
                                let prf = LK::ForallLeft(Box::new(subprf), sequent.clone());
                                checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                                return Ok(prf);
                            }
                        }
                    }
                    //checked_sequents.insert(sequent.clone(), None);
                }
                Exists(term, bfml) => {
                    let mut parent_ant = sequent.antecedent.clone();
                    parent_ant[0] = *bfml.clone();
                    let parent = Sequent {
                        antecedent: parent_ant,
                        succedent: sequent.succedent.clone(),
                    };
                    let mut free_vars = hashset![];
                    for fml in [sequent.antecedent.clone(), sequent.succedent.clone()].concat() {
                        let vars = fml.get_free_vars();
                        free_vars.extend(vars);
                    }
                    let mut idx = 1;
                    while free_vars.contains(&var!(format!("x{}", idx))) {
                        idx += 1;
                    }
                    let v = var!(format!("x{}", idx));
                    let tmp_fml = parent.antecedent[0].substitute(term.clone(), v.clone());
                    let mut tmp_sequent = parent.clone();
                    tmp_sequent.antecedent[0] = tmp_fml;
                    if let Ok(subprf) =
                        _prove_with_lk(&tmp_sequent, max_depth - 1, use_cut, checked_sequents)
                    {
                        let prf = LK::ExistsLeft(Box::new(subprf), sequent.clone());
                        checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                        return Ok(prf);
                    }
                    //checked_sequents.insert(sequent.clone(), None);
                }
                _ => {}
            }
        }
        if sequent.succedent.len() > 0 {
            match sequent.suc_last() {
                Not(bfml) => {
                    let mut parent_ant = vec![*bfml.clone()];
                    parent_ant.extend(sequent.antecedent.clone());
                    let parent_suc = sequent.suc_but_last();
                    let parent = Sequent {
                        antecedent: parent_ant,
                        succedent: parent_suc.to_vec(),
                    };
                    if let Ok(subprf) =
                        _prove_with_lk(&parent, max_depth - 1, use_cut, checked_sequents)
                    {
                        let prf = LK::NotRight(Box::new(subprf), sequent.clone());
                        checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                        return Ok(prf);
                    }
                    //checked_sequents.insert(sequent.clone(), None);
                }
                Or(lhs, rhs) => {
                    let mut parent_suc = sequent.succedent.clone();
                    let len = parent_suc.len();
                    parent_suc[len - 1] = *lhs.clone();
                    let parent = Sequent {
                        antecedent: sequent.antecedent.clone(),
                        succedent: parent_suc.clone(),
                    };
                    if let Ok(subprf) =
                        _prove_with_lk(&parent, max_depth - 1, use_cut, checked_sequents)
                    {
                        let prf = LK::OrRight1(Box::new(subprf), sequent.clone());
                        checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                        return Ok(prf);
                    }
                    let len = parent_suc.len();
                    parent_suc[len - 1] = *rhs.clone();
                    let parent = Sequent {
                        antecedent: sequent.antecedent.clone(),
                        succedent: parent_suc.clone(),
                    };
                    if let Ok(subprf) =
                        _prove_with_lk(&parent, max_depth - 1, use_cut, checked_sequents)
                    {
                        let prf = LK::OrRight2(Box::new(subprf), sequent.clone());
                        checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                        return Ok(prf);
                    }
                    //checked_sequents.insert(sequent.clone(), None);
                }
                And(lhs, rhs) => {
                    let mut left_sequent = sequent.clone();
                    let len = left_sequent.succedent.len();
                    left_sequent.succedent[len - 1] = *lhs.clone();
                    let mut right_sequent = sequent.clone();
                    let len = right_sequent.succedent.len();
                    right_sequent.succedent[len - 1] = *rhs.clone();
                    if let (Ok(lprf), Ok(rprf)) = (
                        _prove_with_lk(&left_sequent, max_depth - 1, use_cut, checked_sequents),
                        _prove_with_lk(&right_sequent, max_depth - 1, use_cut, checked_sequents),
                    ) {
                        let prf = LK::AndRight(Box::new([lprf, rprf]), sequent.clone());
                        checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                        return Ok(prf);
                    }
                    //checked_sequents.insert(sequent.clone(), None);
                }
                Implies(lhs, rhs) => {
                    let mut parent_sequent = sequent.clone();
                    parent_sequent.antecedent = vec![*lhs.clone()];
                    parent_sequent.antecedent.extend(sequent.antecedent.clone());
                    let len = parent_sequent.succedent.len();
                    parent_sequent.succedent[len - 1] = *rhs.clone();
                    if let Ok(subprf) =
                        _prove_with_lk(&parent_sequent, max_depth - 1, use_cut, checked_sequents)
                    {
                        let prf = LK::ImpliesRight(Box::new(subprf), sequent.clone());
                        checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                        return Ok(prf);
                    }
                    //checked_sequents.insert(sequent.clone(), None);
                }
                Exists(term, bfml) => {
                    let mut parent_suc = sequent.succedent.clone();
                    let len = parent_suc.len();
                    parent_suc[len - 1] = *bfml.clone();
                    let parent = Sequent {
                        antecedent: sequent.antecedent.clone(),
                        succedent: parent_suc,
                    };
                    let mut substitutible_terms = hashset![];
                    for fml in [sequent.antecedent.clone(), sequent.succedent.clone()].concat() {
                        let terms = fml.get_subterms();
                        substitutible_terms.extend(terms);
                    }
                    for t in substitutible_terms {
                        if parent.suc_last().is_substitutible(term.clone(), t.clone()) {
                            let tmp_fml = parent.suc_last().substitute(term.clone(), t.clone());
                            let mut tmp_sequent = parent.clone();
                            let len = tmp_sequent.succedent.len();
                            tmp_sequent.succedent[len - 1] = tmp_fml;
                            if let Ok(subprf) = _prove_with_lk(
                                &tmp_sequent,
                                max_depth - 1,
                                use_cut,
                                checked_sequents,
                            ) {
                                let prf = LK::ExistsRight(Box::new(subprf), sequent.clone());
                                checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                                return Ok(prf);
                            }
                        }
                    }
                    //checked_sequents.insert(sequent.clone(), None);
                }
                Forall(term, bfml) => {
                    let mut parent_suc = sequent.succedent.clone();
                    let len = parent_suc.len();
                    parent_suc[len - 1] = *bfml.clone();
                    let parent = Sequent {
                        antecedent: sequent.antecedent.clone(),
                        succedent: parent_suc,
                    };
                    let mut free_vars = hashset![];
                    for fml in [sequent.antecedent.clone(), sequent.succedent.clone()].concat() {
                        let vars = fml.get_free_vars();
                        free_vars.extend(vars);
                    }
                    let mut idx = 1;
                    while free_vars.contains(&var!(format!("x{}", idx))) {
                        idx += 1;
                    }
                    let v = var!(format!("x{}", idx));
                    let tmp_fml = parent.suc_last().substitute(term.clone(), v.clone());
                    let mut tmp_sequent = parent.clone();
                    let len = tmp_sequent.succedent.len();
                    tmp_sequent.succedent[len - 1] = tmp_fml;
                    if let Ok(subprf) =
                        _prove_with_lk(&tmp_sequent, max_depth - 1, use_cut, checked_sequents)
                    {
                        let prf = LK::ForallRight(Box::new(subprf), sequent.clone());
                        checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                        return Ok(prf);
                    }
                }
                _ => {}
            }
        }
        if sequent.antecedent.len() > 0 {
            //println!("pass {:?}", sequent);
            let mut parent_sequent = sequent.clone();
            parent_sequent.antecedent = sequent.ant_but_first().to_vec();
            //println!("pass2 {:?}, {:?}", parent_sequent, max_depth-1);
            //if checked_sequents.contains_key(&parent_sequent.clone()){
            //println!("pass3 {:?}", checked_sequents[&parent_sequent.clone()]);
            //}
            if let Ok(subprf) =
                _prove_with_lk(&parent_sequent, max_depth - 1, use_cut, checked_sequents)
            {
                //println!("wl {:?}", parent_sequent);
                let prf = LK::WeakeningLeft(Box::new(subprf), sequent.clone());
                checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                return Ok(prf);
            }

            parent_sequent = sequent.clone();
            parent_sequent.antecedent = vec![sequent.ant_first().clone()];
            parent_sequent.antecedent.extend(sequent.antecedent.clone());
            if let Ok(subprf) =
                _prove_with_lk(&parent_sequent, max_depth - 1, use_cut, checked_sequents)
            {
                let prf = LK::ContractionLeft(Box::new(subprf), sequent.clone());
                checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                return Ok(prf);
            }
        }
        if sequent.succedent.len() > 0 {
            let mut parent_sequent = sequent.clone();
            parent_sequent.succedent = parent_sequent.suc_but_last().to_vec();
            if let Ok(subprf) =
                _prove_with_lk(&parent_sequent, max_depth - 1, use_cut, checked_sequents)
            {
                let prf = LK::WeakeningRight(Box::new(subprf), sequent.clone());
                checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                return Ok(prf);
            }

            let mut parent_sequent = sequent.clone();
            parent_sequent.succedent.push(sequent.suc_last().clone());
            if let Ok(subprf) =
                _prove_with_lk(&parent_sequent, max_depth - 1, use_cut, checked_sequents)
            {
                let prf = LK::ContractionRight(Box::new(subprf), sequent.clone());
                checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                return Ok(prf);
            }
        }
        if sequent.antecedent.len() > 1 {
            for idx in 0..sequent.antecedent.len() - 1 {
                let mut tmp_sequent = sequent.clone();
                tmp_sequent.antecedent.swap(idx, idx + 1);
                if let Ok(subprf) =
                    _prove_with_lk(&tmp_sequent, max_depth - 1, use_cut, checked_sequents)
                {
                    let prf = LK::ExchangeLeft(Box::new(subprf), sequent.clone());
                    checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                    return Ok(prf);
                }
            }
        }
        if sequent.succedent.len() > 1 {
            for idx in 0..sequent.succedent.len() - 1 {
                let mut tmp_sequent = sequent.clone();
                tmp_sequent.succedent.swap(idx, idx + 1);
                if let Ok(subprf) =
                    _prove_with_lk(&tmp_sequent, max_depth - 1, use_cut, checked_sequents)
                {
                    let prf = LK::ExchangeRight(Box::new(subprf), sequent.clone());
                    checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                    return Ok(prf);
                }
            }
        }
        if use_cut {
            let left_len = sequent.antecedent.len();
            let right_len = sequent.succedent.len();
            let subfmls = sequent.get_subformulas();
            for l in 0..left_len + 1 {
                let gamma = sequent.antecedent[..l].to_vec();
                let pi = sequent.antecedent[l..].to_vec();
                for r in 0..right_len + 1 {
                    let delta = sequent.succedent[..r].to_vec();
                    let sigma = sequent.succedent[r..].to_vec();
                    let mut left_sequent = Sequent {
                        antecedent: gamma.clone(),
                        succedent: delta,
                    };
                    for subfml in &subfmls {
                        left_sequent.succedent.push(subfml.clone());
                        let mut right_sequent = Sequent {
                            antecedent: vec![subfml.clone()],
                            succedent: sigma.clone(),
                        };
                        right_sequent.antecedent.extend(pi.clone());
                        if let (Ok(lprf), Ok(rprf)) = (
                            _prove_with_lk(&left_sequent, max_depth - 1, use_cut, checked_sequents),
                            _prove_with_lk(
                                &right_sequent,
                                max_depth - 1,
                                use_cut,
                                checked_sequents,
                            ),
                        ) {
                            let prf = LK::Cut(Box::new([lprf, rprf]), sequent.clone());
                            checked_sequents.insert(sequent.clone(), Ok(prf.clone()));
                            return Ok(prf);
                        }
                    }
                }
            }
        }
        if checked_sequents.contains_key(sequent) {
            if let Err(d) = checked_sequents[sequent] {
                if max_depth > d.clone() {
                    checked_sequents.insert(sequent.clone(), Err(max_depth));
                }
                Err(d)
            } else {
                checked_sequents[sequent].clone()
            }
        } else {
            checked_sequents.insert(sequent.clone(), Err(max_depth));
            Err(max_depth)
        }
    }
}

pub fn prove_with_lk(fml: Formula, max_depth: u32, use_cut: bool) -> Result<LK, u32> {
    let sequent = sequent!( => fml);
    let mut checked_sequents = hashmap![];
    _prove_with_lk(&sequent, max_depth, use_cut, &mut checked_sequents)
}
