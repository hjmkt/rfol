#[macro_use]
mod language;
mod model;
mod parser;
mod proof;
mod tokenizer;

fn main() {
    use language::*;
    let mut tokenizer = tokenizer::Tokenizer::new();
    let tokens = tokenizer.tokenize("(Vx0 (Ex1 (^ (= (a x y) (b x y)) (v (~ (p y)) (q y)))))");
    println!("{:?}", tokens);

    let mut parser = parser::Parser::new();
    if let Ok(fml) = parser.parse(&tokens) {
        println!("{:?}", fml);
        let free_vars = fml.get_free_vars();
        let bound_vars = fml.get_bound_vars();
        println!("{:?}", free_vars);
        println!("{:?}", bound_vars);
        let funcs = fml.get_funcs();
        println!("{:?}", funcs);
        let preds = fml.get_preds();
        println!("{:?}", preds);

        let terms = fml.get_subterms();
        println!("{:?}, {:?}", terms, hashset![func!("a", var!("x"), var!("y")), func!("b", var!("x"), var!("x")), var!("x"), var!("y")]);

        use model::*;

        let mut model = FiniteModel::new(2);

        model.var_assignment.insert(var!("x"), 0);
        model.var_assignment.insert(var!("y"), 1);

        model.func_assignment.insert(nlsym!("a", 2), hashmap![]);
        model.func_assignment.insert(nlsym!("b", 2), hashmap![]);

        {
            let assignment_a = model.func_assignment.get_mut(&nlsym!("a", 2)).unwrap();
            assignment_a.insert(vec![0, 0], 0);
            assignment_a.insert(vec![0, 1], 1);
            assignment_a.insert(vec![1, 0], 1);
            assignment_a.insert(vec![1, 1], 0);
        }

        {
            let assignment_b = model.func_assignment.get_mut(&nlsym!("b", 2)).unwrap();
            assignment_b.insert(vec![0, 0], 1);
            assignment_b.insert(vec![0, 1], 0);
            assignment_b.insert(vec![1, 0], 0);
            assignment_b.insert(vec![1, 1], 1);
        }

        model.pred_assignment.insert(nlsym!("p", 1), hashmap![]);
        model.pred_assignment.insert(nlsym!("q", 0), hashmap![]);

        {
            let assignment_p = model.pred_assignment.get_mut(&nlsym!("p", 1)).unwrap();
            assignment_p.insert(vec![0], true);
            assignment_p.insert(vec![1], false);
        }

        {
            let assignment_q = model.pred_assignment.get_mut(&nlsym!("q", 0)).unwrap();
            assignment_q.insert(vec![], true);
        }

        let truth_value = model.evaluate_formula(&fml);
        println!("{:?}", truth_value);

        use proof::*;

        let valid_axiom = LK::Axiom(Sequent{
            antecedent: vec![*pred!("p")],
            succedent: vec![*pred!("p")],
        });
        println!("{:?}", valid_axiom);

        let valid_weakening_left = LK::WeakeningLeft(Box::new(valid_axiom.clone()), Sequent{
            antecedent: vec![*pred!("p"), *pred!("p")],
            succedent: vec![*pred!("p")],
        });
        println!("{:?}", valid_weakening_left);

        let valid_weakening_right = LK::WeakeningRight(Box::new(valid_axiom.clone()), Sequent{
            antecedent: vec![*pred!("p")],
            succedent: vec![*pred!("p"), *pred!("q")],
        });
        println!("{:?}", valid_weakening_right);

        let valid_contraction_left = LK::ContractionLeft(Box::new(valid_weakening_left.clone()), valid_axiom.last().clone());
        println!("{:?}", valid_contraction_left);

        let valid_contraction_right = LK::ContractionRight(Box::new(valid_weakening_right.clone()), valid_axiom.last().clone());
        println!("{:?}", valid_contraction_right);

        let valid_exchange_left = LK::ExchangeLeft(
            Box::new(LK::Axiom( Sequent{
                antecedent: vec![*pred!("p"), *pred!("q")],
                succedent: vec![*pred!("p"), *pred!("q")],
            })),
            Sequent{
                antecedent: vec![*pred!("q"), *pred!("p")],
                succedent: vec![*pred!("p"), *pred!("q")],
            }
        );
        println!("{:?}", valid_exchange_left);

        let valid_exchange_right = LK::ExchangeRight(
            Box::new(LK::Axiom( Sequent{
                antecedent: vec![*pred!("p"), *pred!("q")],
                succedent: vec![*pred!("p"), *pred!("q")],
            })),
            Sequent{
                antecedent: vec![*pred!("p"), *pred!("q")],
                succedent: vec![*pred!("q"), *pred!("p")],
            }
        );
        println!("{:?}", valid_exchange_right);

        let valid_and_left1 = LK::AndLeft1(Box::new(valid_axiom.clone()), Sequent{
            antecedent: vec![*and!(pred!("p"), pred!("q"))],
            succedent: vec![*pred!("p")],
        });
        println!("{:?}", valid_and_left1);

        let valid_and_left2 = LK::AndLeft2(Box::new(valid_axiom.clone()), Sequent{
            antecedent: vec![*and!(pred!("q"), pred!("p"))],
            succedent: vec![*pred!("p")],
        });
        println!("{:?}", valid_and_left2);

        let valid_and_right = LK::AndRight(
            Box::new([
                LK::Axiom(Sequent{
                    antecedent: vec![*pred!("p")],
                    succedent: vec![*pred!("p")]
                }),
                LK::Axiom(Sequent{
                    antecedent: vec![*pred!("p")],
                    succedent: vec![*pred!("q")]
                }),
            ]),
            Sequent{
                antecedent: vec![*pred!("p")],
                succedent: vec![*and!(pred!("p"), pred!("q"))]
            },
        );
        println!("{:?}", valid_and_right);

        let valid_or_left = LK::OrLeft(
            Box::new([
                LK::Axiom(Sequent{
                    antecedent: vec![*pred!("p")],
                    succedent: vec![*pred!("p")]
                }),
                LK::Axiom(Sequent{
                    antecedent: vec![*pred!("q")],
                    succedent: vec![*pred!("p")]
                }),
            ]),
            Sequent{
                antecedent: vec![*or!(pred!("p"), pred!("q"))],
                succedent: vec![*pred!("p")],
            },
        );
        println!("{:?}", valid_or_left);

        let valid_or_right1 = LK::OrRight1(Box::new(valid_axiom.clone()), Sequent{
            antecedent: vec![*pred!("p")],
            succedent: vec![*or!(pred!("p"), pred!("q"))],
        });
        println!("{:?}", valid_or_right1);

        let valid_or_right2 = LK::OrRight2(Box::new(valid_axiom.clone()), Sequent{
            antecedent: vec![*pred!("p")],
            succedent: vec![*or!(pred!("q"), pred!("p"))],
        });
        println!("{:?}", valid_or_right2);

        let valid_implies_left = LK::ImpliesLeft(
            Box::new([
                LK::Axiom(Sequent{
                    antecedent: vec![*pred!("p")],
                    succedent: vec![*pred!("p")]
                }),
                LK::Axiom(Sequent{
                    antecedent: vec![*pred!("q")],
                    succedent: vec![*pred!("q")]
                }),
            ]),
            Sequent{
                antecedent: vec![*implies!(pred!("p"), pred!("q")), *pred!("p")],
                succedent: vec![*pred!("q")]
            }
        );
        println!("{:?}", valid_implies_left);

        let valid_implies_right = LK::ImpliesRight(
            Box::new( LK::Axiom(Sequent{
                antecedent: vec![*pred!("p"), *pred!("p")],
                succedent: vec![*pred!("q"), *pred!("q")],
            })),
            Sequent{
                antecedent: vec![*pred!("p")],
                succedent: vec![*pred!("q"), *implies!(pred!("p"), pred!("q"))],
            }
        );
        println!("{:?}", valid_implies_right);

        let valid_not_left = LK::NotLeft(Box::new(valid_axiom.clone()), Sequent{
            antecedent: vec![*not!(pred!("p")), *pred!("p")],
            succedent: vec![],
        });
        println!("{:?}", valid_not_left);

        let valid_not_right = LK::NotRight(Box::new(valid_axiom.clone()), Sequent{
            antecedent: vec![],
            succedent: vec![*pred!("p"), *not!(pred!("p"))]
        });
        println!("{:?}", valid_not_right);

        let valid_forall_left = LK::ForallLeft(
            Box::new(LK::Axiom(Sequent{
                antecedent: vec![*equal!(var!("x"), var!("x"))],
                succedent: vec![]
            })),
            Sequent{
                antecedent: vec![*forall!(var!("y"), equal!(var!("y"), var!("y")))],
                succedent: vec![]
            }
        );
        println!("{:?}", valid_forall_left);

        let valid_forall_right = LK::ForallRight(
            Box::new(LK::Axiom(Sequent{
                antecedent: vec![],
                succedent: vec![*equal!(var!("x"), var!("x"))],
            })),
            Sequent{
                antecedent: vec![],
                succedent: vec![*forall!(var!("y"), equal!(var!("y"), var!("y")))],
            }
        );
        println!("{:?}", valid_forall_right);

        let valid_exists_left = LK::ExistsLeft(
            Box::new(LK::Axiom(Sequent{
                antecedent: vec![*equal!(var!("x"), var!("x"))],
                succedent: vec![]
            })),
            Sequent{
                antecedent: vec![*exists!(var!("y"), equal!(var!("y"), var!("y")))],
                succedent: vec![]
            }
        );
        println!("{:?}", valid_exists_left);

        let valid_exists_right = LK::ExistsRight(
            Box::new(LK::Axiom(Sequent{
                antecedent: vec![],
                succedent: vec![*equal!(var!("x"), var!("x"))],
            })),
            Sequent{
                antecedent: vec![],
                succedent: vec![*exists!(var!("y"), equal!(var!("y"), var!("y")))],
            }
        );
        println!("{:?}", valid_exists_right);

        let valid_cut = LK::Cut(
            Box::new([
                LK::Axiom(Sequent{
                    antecedent: vec![],
                    succedent: vec![*pred!("p")]
                }),
                LK::Axiom(Sequent{
                    antecedent: vec![*pred!("p")],
                    succedent: vec![]
                })
            ]),
            Sequent{
                antecedent: vec![],
                succedent: vec![]
            }
        );
        println!("{:?}", valid_cut);
    } else {
        println!("{:?}", parser);
    }
}
