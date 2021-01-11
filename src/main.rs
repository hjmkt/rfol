mod language;
mod model;
mod parser;
mod proof;
mod tokenizer;

fn main() {
    let mut tokenizer = tokenizer::Tokenizer::new();
    let tokens = tokenizer.tokenize("(Vx0 (Ex1 (^ (= (a x y) (b x y)) (v (~ (p y)) (q y)))))");
    println!("{:?}", tokens);

    let mut parser = parser::Parser::new();
    if let Ok(formula) = parser.parse(&tokens) {
        println!("{:?}", formula);
        let free_vars = formula.get_free_vars();
        let bound_vars = formula.get_bound_vars();
        println!("{:?}", free_vars);
        println!("{:?}", bound_vars);
        let funcs = formula.get_funcs();
        println!("{:?}", funcs);
        let preds = formula.get_preds();
        println!("{:?}", preds);

        use language::NonLogicalSymbol;
        use language::Term::*;
        use model::*;
        use std::collections::HashMap;

        let mut model = FiniteModel::new(2);

        model.var_assignment.insert(Var("x".into()), 0);
        model.var_assignment.insert(Var("y".into()), 1);

        model.func_assignment.insert(
            NonLogicalSymbol {
                name: "a".into(),
                arity: 2,
            },
            HashMap::new(),
        );
        model.func_assignment.insert(
            NonLogicalSymbol {
                name: "b".into(),
                arity: 2,
            },
            HashMap::new(),
        );

        {
            let assignment_a = model
                .func_assignment
                .get_mut(&NonLogicalSymbol {
                    name: "a".into(),
                    arity: 2,
                })
                .unwrap();
            assignment_a.insert(vec![0, 0], 0);
            assignment_a.insert(vec![0, 1], 1);
            assignment_a.insert(vec![1, 0], 1);
            assignment_a.insert(vec![1, 1], 0);
        }

        {
            let assignment_b = model
                .func_assignment
                .get_mut(&NonLogicalSymbol {
                    name: "b".into(),
                    arity: 2,
                })
                .unwrap();
            assignment_b.insert(vec![0, 0], 1);
            assignment_b.insert(vec![0, 1], 0);
            assignment_b.insert(vec![1, 0], 0);
            assignment_b.insert(vec![1, 1], 1);
        }

        model.pred_assignment.insert(
            NonLogicalSymbol {
                name: "p".into(),
                arity: 1,
            },
            HashMap::new(),
        );
        model.pred_assignment.insert(
            NonLogicalSymbol {
                name: "q".into(),
                arity: 0,
            },
            HashMap::new(),
        );

        {
            let assignment_p = model
                .pred_assignment
                .get_mut(&NonLogicalSymbol {
                    name: "p".into(),
                    arity: 1,
                })
                .unwrap();
            assignment_p.insert(vec![0], true);
            assignment_p.insert(vec![1], false);
        }

        {
            let assignment_q = model
                .pred_assignment
                .get_mut(&NonLogicalSymbol {
                    name: "q".into(),
                    arity: 0,
                })
                .unwrap();
            assignment_q.insert(vec![], true);
        }

        let truth_value = model.evaluate_formula(&formula);
        println!("{:?}", truth_value);
    } else {
        println!("{:?}", parser);
    }
}
