#[macro_use]
#[allow(unused_macros)]

pub mod language;
pub mod model;
pub mod parser;
pub mod proof;
pub mod tokenizer;

#[test]
fn tokenizer_works() {
    use language::Token::*;
    use tokenizer::Tokenizer;

    let mut tokenizer = Tokenizer::new();
    let tokens = tokenizer.tokenize("(Vx0 (Ex1 (^ (= (a x y) (b x y)) (v (~ (p y)) (> q r)))))");
    let gt = vec![
        LParen,
        Forall,
        Symbol("x0".into()),
        LParen,
        Exists,
        Symbol("x1".into()),
        LParen,
        And,
        LParen,
        Equal,
        LParen,
        Symbol("a".into()),
        Symbol("x".into()),
        Symbol("y".into()),
        RParen,
        LParen,
        Symbol("b".into()),
        Symbol("x".into()),
        Symbol("y".into()),
        RParen,
        RParen,
        LParen,
        Or,
        LParen,
        Not,
        LParen,
        Symbol("p".into()),
        Symbol("y".into()),
        RParen,
        RParen,
        LParen,
        Implies,
        Symbol("q".into()),
        Symbol("r".into()),
        RParen,
        RParen,
        RParen,
        RParen,
        RParen,
    ];

    assert_eq!(gt, tokens);
}

#[test]
fn parser_works() {
    use language::*;
    use language::Token::*;
    use parser::Parser;

    let mut parser = Parser::new();
    let tokens = vec![
        LParen,
        Forall,
        Symbol("x0".into()),
        LParen,
        Exists,
        Symbol("x1".into()),
        LParen,
        And,
        LParen,
        Equal,
        LParen,
        Symbol("a".into()),
        Symbol("x".into()),
        Symbol("y".into()),
        RParen,
        LParen,
        Symbol("b".into()),
        Symbol("x".into()),
        Symbol("y".into()),
        RParen,
        RParen,
        LParen,
        Or,
        LParen,
        Not,
        LParen,
        Symbol("p".into()),
        Symbol("y".into()),
        RParen,
        RParen,
        LParen,
        Implies,
        Symbol("q".into()),
        Symbol("r".into()),
        RParen,
        RParen,
        RParen,
        RParen,
        RParen,
    ];
    let gt = Formula::Forall(
        var!("x0"),
        exists!(
            var!("x1"),
            and!(
                equal!(
                    func!("a", var!("x"), var!("y")),
                    func!("b", var!("x"), var!("y"))
                ),
                or!(
                    not!(pred!("p", var!("y"))),
                    implies!(pred!("q"), pred!("r"))
                )
            )
        ),
    );

    if let Ok(fml) = parser.parse(&tokens) {
        assert_eq!(gt, fml);
    } else {
        panic!("Parse error.");
    }
}

#[test]
fn var_group_works() {
    use language::*;

    let fml = Formula::Forall(
        var!("x0"),
        exists!(
            var!("x1"),
            and!(
                equal!(
                    func!("a", var!("x"), var!("y")),
                    func!("b", var!("x"), var!("y"))
                ),
                or!(
                    not!(pred!("p", var!("y"))),
                    implies!(pred!("q"), pred!("r"))
                )
            )
        ),
    );

    let free_vars = fml.get_free_vars();
    let bound_vars = fml.get_bound_vars();

    let free_gt = hashset![var!("x"), var!("y")];
    let bound_gt = hashset![var!("x0"), var!("x1")];

    assert_eq!(free_gt, free_vars);
    assert_eq!(bound_gt, bound_vars);
}

#[test]
fn get_funcs_works() {
    use language::*;

    let fml = Formula::Forall(
        var!("x0"),
        exists!(
            var!("x1"),
            and!(
                equal!(
                    func!("a", var!("x"), var!("y")),
                    func!("b", var!("x"), var!("y"))
                ),
                or!(
                    not!(pred!("p", var!("y"))),
                    implies!(pred!("q"), pred!("r"))
                )
            )
        ),
    );

    let funcs = fml.get_funcs();
    let gt = hashset![nlsym!("a", 2), nlsym!("b", 2)];
    assert_eq!(gt, funcs);
}

#[test]
fn get_preds_works() {
    use language::*;

    let fml = Formula::Forall(
        var!("x0"),
        exists!(
            var!("x1"),
            and!(
                equal!(
                    func!("a", var!("x"), var!("y")),
                    func!("b", var!("x"), var!("y"))
                ),
                or!(
                    not!(pred!("p", var!("y"))),
                    implies!(pred!("q"), pred!("r"))
                )
            )
        ),
    );

    let preds = fml.get_preds();
    let gt = hashset![nlsym!("p", 1), nlsym!("q", 0), nlsym!("r", 0)];
    assert_eq!(gt, preds);
}

#[test]
fn get_subterms_works() {
    use language::*;

    let fml = Formula::Forall(
        var!("x0"),
        exists!(
            var!("x1"),
            and!(
                equal!(
                    func!("a", var!("x"), var!("y")),
                    func!("b", var!("x"), var!("y"))
                ),
                or!(
                    not!(pred!("p", var!("y"))),
                    implies!(pred!("q"), pred!("r"))
                )
            )
        ),
    );

    let terms = fml.get_subterms();
    let gt = hashset![
        func!("a", var!("x"), var!("y")),
        func!("b", var!("x"), var!("y")),
        var!("x"),
        var!("y")
    ];
    assert_eq!(gt, terms);
}

#[test]
fn finite_model_evaluate_works() {
    use language::*;
    use model::*;

    let fml = Formula::Forall(
        var!("x0"),
        exists!(
            var!("x1"),
            and!(
                equal!(
                    func!("a", var!("x"), var!("y")),
                    func!("b", var!("x"), var!("y"))
                ),
                or!(
                    not!(pred!("p", var!("y"))),
                    implies!(pred!("q"), pred!("r"))
                )
            )
        ),
    );

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
    model.pred_assignment.insert(nlsym!("r", 0), hashmap![]);

    {
        let assignment_p = model.pred_assignment.get_mut(&nlsym!("p", 1)).unwrap();
        assignment_p.insert(vec![0], true);
        assignment_p.insert(vec![1], false);
    }

    {
        let assignment_q = model.pred_assignment.get_mut(&nlsym!("q", 0)).unwrap();
        assignment_q.insert(vec![], true);
    }

    {
        let assignment_r = model.pred_assignment.get_mut(&nlsym!("r", 0)).unwrap();
        assignment_r.insert(vec![], true);
    }

    let truth_value = model.evaluate_formula(&fml);
    assert!(!truth_value);

    {
        let mut model = FiniteModel::new(1);
        model.pred_assignment.insert(nlsym!("a", 0), hashmap![vec![] => true]);
        let fml = pred!("a");
        assert_eq!(true, model.evaluate_formula(&fml));
        let fml = not!(fml);
        assert_eq!(false, model.evaluate_formula(&fml));
    }
}

#[test]
fn lk_inference_rule_works() {
    use language::*;
    use proof::*;

    let valid_axiom = LK::Axiom(Sequent{
        antecedent: vec![*pred!("p")],
        succedent: vec![*pred!("p")],
    });
    assert!(valid_axiom.is_valid_inference());

    let invalid_axiom = LK::Axiom(Sequent{
        antecedent: vec![*pred!("p")],
        succedent: vec![*pred!("q")],
    });
    assert!(!invalid_axiom.is_valid_inference());

    let valid_weakening_left = LK::WeakeningLeft(Box::new(valid_axiom.clone()), Sequent{
        antecedent: vec![*pred!("p"), *pred!("p")],
        succedent: vec![*pred!("p")],
    });
    assert!(valid_weakening_left.is_valid_inference());

    let invalid_weakening_left = LK::WeakeningLeft(Box::new(valid_axiom.clone()), Sequent{
        antecedent: vec![*pred!("q"), *pred!("q")],
        succedent: vec![*pred!("p")],
    });
    assert!(!invalid_weakening_left.is_valid_inference());

    let valid_weakening_right = LK::WeakeningRight(Box::new(valid_axiom.clone()), Sequent{
        antecedent: vec![*pred!("p")],
        succedent: vec![*pred!("p"), *pred!("p")],
    });
    assert!(valid_weakening_right.is_valid_inference());

    let invalid_weakening_right = LK::WeakeningRight(Box::new(valid_axiom.clone()), Sequent{
        succedent: vec![*pred!("p")],
        antecedent: vec![*pred!("q"), *pred!("q")],
    });
    assert!(!invalid_weakening_right.is_valid_inference());

    let valid_contraction_left = LK::ContractionLeft(Box::new(valid_weakening_left.clone()), valid_axiom.last().clone());
    assert!(valid_contraction_left.is_valid_inference());

    let invalid_contraction_left = LK::ContractionLeft(Box::new(valid_weakening_left.clone()), valid_weakening_left.clone().last().clone());
    assert!(!invalid_contraction_left.is_valid_inference());

    let valid_contraction_right = LK::ContractionRight(Box::new(valid_weakening_right.clone()), valid_axiom.last().clone());
    assert!(valid_contraction_right.is_valid_inference());

    let invalid_contraction_right = LK::ContractionRight(Box::new(valid_weakening_right.clone()), valid_weakening_right.last().clone());
    assert!(!invalid_contraction_right.is_valid_inference());

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
    assert!(valid_exchange_left.is_valid_inference());

    let invalid_exchange_left = LK::ExchangeLeft(
        Box::new(LK::Axiom( Sequent{
            antecedent: vec![*pred!("p"), *pred!("q")],
            succedent: vec![*pred!("p"), *pred!("q")],
        })),
        Sequent{
            antecedent: vec![*pred!("p"), *pred!("q")],
            succedent: vec![*pred!("p"), *pred!("q")],
        }
    );
    assert!(!invalid_exchange_left.is_valid_inference());

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
    assert!(valid_exchange_right.is_valid_inference());

    let invalid_exchange_right = LK::ExchangeLeft(
        Box::new(LK::Axiom( Sequent{
            antecedent: vec![*pred!("p"), *pred!("q")],
            succedent: vec![*pred!("p"), *pred!("q")],
        })),
        Sequent{
            antecedent: vec![*pred!("p"), *pred!("q")],
            succedent: vec![*pred!("p"), *pred!("q")],
        }
    );
    assert!(!invalid_exchange_right.is_valid_inference());

    let valid_and_left1 = LK::AndLeft1(Box::new(valid_axiom.clone()), Sequent{
        antecedent: vec![*and!(pred!("p"), pred!("q"))],
        succedent: vec![*pred!("p")],
    });
    assert!(valid_and_left1.is_valid_inference());

    let invalid_and_left1 = LK::AndLeft1(Box::new(valid_axiom.clone()), Sequent{
        antecedent: vec![*or!(pred!("p"), pred!("q"))],
        succedent: vec![*pred!("p")],
    });
    assert!(!invalid_and_left1.is_valid_inference());

    let valid_and_left2 = LK::AndLeft2(Box::new(valid_axiom.clone()), Sequent{
        antecedent: vec![*and!(pred!("q"), pred!("p"))],
        succedent: vec![*pred!("p")],
    });
    assert!(valid_and_left2.is_valid_inference());

    let invalid_and_left2 = LK::AndLeft2(Box::new(valid_axiom.clone()), Sequent{
        antecedent: vec![*or!(pred!("q"), pred!("p"))],
        succedent: vec![*pred!("p")],
    });
    assert!(!invalid_and_left2.is_valid_inference());

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
    assert!(valid_and_right.is_valid_inference());

    let invalid_and_right = LK::AndRight(
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
            antecedent: vec![*pred!("q")],
            succedent: vec![*pred!("q")]
        },
    );
    assert!(!invalid_and_right.is_valid_inference());

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
    assert!(valid_or_left.is_valid_inference());

    let invalid_or_left = LK::OrLeft(
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
            antecedent: vec![*pred!("q")],
            succedent: vec![*pred!("q")]
        },
    );
    assert!(!invalid_or_left.is_valid_inference());

    let valid_or_right1 = LK::OrRight1(Box::new(valid_axiom.clone()), Sequent{
        antecedent: vec![*pred!("p")],
        succedent: vec![*or!(pred!("p"), pred!("q"))],
    });
    assert!(valid_or_right1.is_valid_inference());

    let invalid_or_right1 = LK::OrRight1(Box::new(valid_axiom.clone()), Sequent{
        antecedent: vec![*pred!("p")],
        succedent: vec![*and!(pred!("p"), pred!("q"))],
    });
    assert!(!invalid_or_right1.is_valid_inference());

    let valid_or_right2 = LK::OrRight2(Box::new(valid_axiom.clone()), Sequent{
        antecedent: vec![*pred!("p")],
        succedent: vec![*or!(pred!("q"), pred!("p"))],
    });
    assert!(valid_or_right2.is_valid_inference());

    let invalid_or_right2 = LK::OrRight2(Box::new(valid_axiom.clone()), Sequent{
        antecedent: vec![*pred!("p")],
        succedent: vec![*and!(pred!("q"), pred!("p"))],
    });
    assert!(!invalid_or_right2.is_valid_inference());

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
    assert!(valid_implies_left.is_valid_inference());

    let invalid_implies_left = LK::ImpliesLeft(
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
            antecedent: vec![*implies!(pred!("q"), pred!("p")), *pred!("p")],
            succedent: vec![*pred!("q")]
        }
    );
    assert!(!invalid_implies_left.is_valid_inference());

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
    assert!(valid_implies_right.is_valid_inference());

    let invalid_implies_right = LK::ImpliesRight(
        Box::new( LK::Axiom(Sequent{
            antecedent: vec![*pred!("p"), *pred!("p")],
            succedent: vec![*pred!("q"), *pred!("q")],
        })),
        Sequent{
            antecedent: vec![*pred!("p")],
            succedent: vec![*pred!("q"), *implies!(pred!("q"), pred!("p"))],
        }
    );
    assert!(!invalid_implies_right.is_valid_inference());

    let valid_not_left = LK::NotLeft(Box::new(valid_axiom.clone()), Sequent{
        antecedent: vec![*not!(pred!("p")), *pred!("p")],
        succedent: vec![]
    });
    assert!(valid_not_left.is_valid_inference());

    let invalid_not_left = LK::NotLeft(Box::new(valid_axiom.clone()), Sequent{
        antecedent: vec![*pred!("p"), *pred!("p")],
        succedent: vec![]
    });
    assert!(!invalid_not_left.is_valid_inference());

    let valid_not_right = LK::NotRight(Box::new(valid_axiom.clone()), Sequent{
        antecedent: vec![],
        succedent: vec![*pred!("p"), *not!(pred!("p"))]
    });
    assert!(valid_not_right.is_valid_inference());

    let invalid_not_right = LK::NotRight(Box::new(valid_axiom.clone()), Sequent{
        antecedent: vec![],
        succedent: vec![*pred!("p"), *pred!("p")]
    });
    assert!(!invalid_not_right.is_valid_inference());

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
    assert!(valid_forall_left.is_valid_inference());

    let invalid_forall_left = LK::ForallLeft(
        Box::new(LK::Axiom(Sequent{
            antecedent: vec![*equal!(var!("x"), var!("x"))],
            succedent: vec![]
        })),
        Sequent{
            antecedent: vec![*exists!(var!("y"), equal!(var!("y"), var!("y")))],
            succedent: vec![]
        }
    );
    assert!(!invalid_forall_left.is_valid_inference());

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
    assert!(valid_forall_right.is_valid_inference());

    let invalid_forall_right = LK::ForallRight(
        Box::new(LK::Axiom(Sequent{
            antecedent: vec![],
            succedent: vec![*equal!(var!("x"), var!("x"))],
        })),
        Sequent{
            antecedent: vec![],
            succedent: vec![*exists!(var!("y"), equal!(var!("y"), var!("y")))],
        }
    );
    assert!(!invalid_forall_right.is_valid_inference());

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
    assert!(valid_exists_left.is_valid_inference());

    let invalid_exists_left = LK::ExistsLeft(
        Box::new(LK::Axiom(Sequent{
            antecedent: vec![*equal!(var!("x"), var!("x"))],
            succedent: vec![]
        })),
        Sequent{
            antecedent: vec![*forall!(var!("y"), equal!(var!("y"), var!("y")))],
            succedent: vec![]
        }
    );
    assert!(!invalid_exists_left.is_valid_inference());

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
    assert!(valid_exists_right.is_valid_inference());

    let invalid_exists_right = LK::ExistsRight(
        Box::new(LK::Axiom(Sequent{
            antecedent: vec![],
            succedent: vec![*equal!(var!("x"), var!("x"))],
        })),
        Sequent{
            antecedent: vec![],
            succedent: vec![*forall!(var!("y"), equal!(var!("y"), var!("y")))],
        }
    );
    assert!(!invalid_exists_right.is_valid_inference());

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
    assert!(valid_cut.is_valid_inference());

    let invalid_cut = LK::Cut(
        Box::new([
            LK::Axiom(Sequent{
                antecedent: vec![],
                succedent: vec![*pred!("p")]
            }),
            LK::Axiom(Sequent{
                antecedent: vec![*pred!("q")],
                succedent: vec![]
            })
        ]),
        Sequent{
            antecedent: vec![],
            succedent: vec![]
        }
    );
    assert!(!invalid_cut.is_valid_inference());
}
