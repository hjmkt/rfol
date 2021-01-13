use crate::language::*;
use crate::model::*;
use std::collections::HashMap;

fn _enumerate_vecs(vectors: Vec<Vec<u32>>, size: u32, rem_size: u32) -> Vec<Vec<u32>> {
    if rem_size == 0 {
        vectors
    } else {
        let mut new_vectors = vec![];
        for vector in vectors {
            for n in 0..size - 1 {
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
            for n in 0..domain_size - 1 {
                let mut tmp = assign.clone();
                tmp.insert(vector[0].clone(), n);
                new_assigns.push(tmp);
            }
        }
        _enumerate_assign_func(new_assigns, &vector[1..], domain_size)
    }
}

fn enumerate_assign_func(arity: u32, domain_size: u32) -> Vec<HashMap<Vec<u32>, u32>> {
    let mut vectors = vec![];
    vectors = _enumerate_vecs(vectors, domain_size, arity);
    _enumerate_assign_func(vec![], &vectors[..], arity)
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
    let mut vectors = vec![];
    vectors = _enumerate_vecs(vectors, domain_size, arity);
    _enumerate_assign_pred(vec![], &vectors[..], arity)
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
        for n in 0..domain_size - 1 {
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
            model.assign_pred(funcs[0].clone(), assign);
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

    for domain_size in 0..max_domain_size {
        let mut model = FiniteModel::new(domain_size);
        if let m @ Some(_) = _refute_on_finite_models(
            &fml,
            domain_size,
            &free_vars[..],
            &funcs[..],
            &preds[..],
            &mut model,
        ) {
            return m;
        }
    }
    None
}
