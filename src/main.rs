#[allow(unused_macros)]
#[macro_use]
mod language;
mod model;
mod parser;
#[allow(unused_macros)]
#[macro_use]
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
        println!(
            "{:?}, {:?}",
            terms,
            hashset![
                func!("a", var!("x"), var!("y")),
                func!("b", var!("x"), var!("x")),
                var!("x"),
                var!("y")
            ]
        );

        use model::*;
        use proof::*;

        let mut model = FiniteModel::new(2);
        model.assign_var(assign![var!("x") => 0]);
        model.assign_var(assign![var!("y") => 1]);
        model.assign_func(
            nlsym!("a", 2),
            assign![[0, 0] => 0, [0, 1] => 1, [1, 0] => 1, [1, 1] => 0],
        );
        model.assign_func(
            nlsym!("b", 2),
            assign![[0, 0] => 1, [0, 1] => 0, [1, 0] => 0, [1, 1] => 1],
        );
        model.assign_pred(nlsym!("p", 1), assign![[0] => true, [1] => false]);
        model.assign_pred(nlsym!("q", 0), assign![[] => true]);

        let truth_value = model.evaluate_formula(&fml);
        println!("{:?}", truth_value);

        let valid_axiom = LK::Axiom(sequent!(pred!("p") => pred!("p")));
        println!("{:?}", valid_axiom.is_valid_inference());

        let valid_weakening_left = LK::WeakeningLeft(
            Box::new(valid_axiom.clone()),
            sequent!(pred!("p"), pred!("p") => pred!("p")),
        );
        println!("{:?}", valid_weakening_left.is_valid_inference());

        let valid_weakening_right = LK::WeakeningRight(
            Box::new(valid_axiom.clone()),
            sequent!(pred!("p") => pred!("p"), pred!("q")),
        );
        println!("{:?}", valid_weakening_right.is_valid_inference());

        let valid_contraction_left = LK::ContractionLeft(
            Box::new(valid_weakening_left.clone()),
            valid_axiom.last().clone(),
        );
        println!("{:?}", valid_contraction_left.is_valid_inference());

        let valid_contraction_right = LK::ContractionRight(
            Box::new(valid_weakening_right.clone()),
            valid_axiom.last().clone(),
        );
        println!("{:?}", valid_contraction_right.is_valid_inference());

        let valid_exchange_left = LK::ExchangeLeft(
            Box::new(LK::Axiom(
                sequent!(pred!("p"), pred!("q") => pred!("p"), pred!("q")),
            )),
            sequent!(pred!("q"), pred!("p") => pred!("p"), pred!("q")),
        );
        println!("{:?}", valid_exchange_left.is_valid_inference());

        let valid_exchange_right = LK::ExchangeRight(
            Box::new(LK::Axiom(
                sequent!(pred!("p"), pred!("q") => pred!("p"), pred!("q")),
            )),
            sequent!(pred!("p"), pred!("q") => pred!("q"), pred!("p")),
        );
        println!("{:?}", valid_exchange_right.is_valid_inference());

        let valid_and_left1 = LK::AndLeft1(
            Box::new(valid_axiom.clone()),
            sequent!(and!(pred!("p"), pred!("q")) => pred!("p")),
        );
        println!("{:?}", valid_and_left1.is_valid_inference());

        let valid_and_left2 = LK::AndLeft2(
            Box::new(valid_axiom.clone()),
            sequent!(and!(pred!("q"), pred!("p")) => pred!("p")),
        );
        println!("{:?}", valid_and_left2.is_valid_inference());

        let valid_and_right = LK::AndRight(
            Box::new([
                LK::Axiom(sequent!(pred!("p") => pred!("p"))),
                LK::Axiom(sequent!(pred!("p") => pred!("q"))),
            ]),
            sequent!(pred!("p") => and!(pred!("p"), pred!("q"))),
        );
        println!("{:?}", valid_and_right.is_valid_inference());

        let valid_or_left = LK::OrLeft(
            Box::new([
                LK::Axiom(sequent!(pred!("p") => pred!("p"))),
                LK::Axiom(sequent!(pred!("q") => pred!("p"))),
            ]),
            sequent!(or!(pred!("p"), pred!("q")) => pred!("p")),
        );
        println!("{:?}", valid_or_left.is_valid_inference());

        let valid_or_right1 = LK::OrRight1(
            Box::new(valid_axiom.clone()),
            sequent!(pred!("p") => or!(pred!("p"), pred!("q"))),
        );
        println!("{:?}", valid_or_right1.is_valid_inference());

        let valid_or_right2 = LK::OrRight2(
            Box::new(valid_axiom.clone()),
            sequent!(pred!("p") => or!(pred!("q"), pred!("p"))),
        );
        println!("{:?}", valid_or_right2.is_valid_inference());

        let valid_implies_left = LK::ImpliesLeft(
            Box::new([
                LK::Axiom(sequent!(pred!("p") => pred!("p"))),
                LK::Axiom(sequent!(pred!("q") => pred!("q"))),
            ]),
            sequent!(implies!(pred!("p"), pred!("q")), pred!("p") => pred!("q")),
        );
        println!("{:?}", valid_implies_left.is_valid_inference());

        let valid_implies_right = LK::ImpliesRight(
            Box::new(LK::Axiom(
                sequent!(pred!("p"), pred!("p") => pred!("q"), pred!("q")),
            )),
            sequent!(pred!("p") => pred!("q"), implies!(pred!("p"), pred!("q"))),
        );
        println!("{:?}", valid_implies_right.is_valid_inference());

        let valid_not_left = LK::NotLeft(
            Box::new(valid_axiom.clone()),
            sequent!(not!(pred!("p")), pred!("p") => ),
        );
        println!("{:?}", valid_not_left.is_valid_inference());

        let valid_not_right = LK::NotRight(
            Box::new(valid_axiom.clone()),
            sequent!( => pred!("p"), not!(pred!("p"))),
        );
        println!("{:?}", valid_not_right.is_valid_inference());

        let valid_forall_left = LK::ForallLeft(
            Box::new(LK::Axiom(sequent!(equal!(var!("x"), var!("x")) => ))),
            sequent!(forall!(var!("y"), equal!(var!("y"), var!("y"))) => ),
        );
        println!("{:?}", valid_forall_left.is_valid_inference());

        let valid_forall_right = LK::ForallRight(
            Box::new(LK::Axiom(sequent!( => equal!(var!("x"), var!("x"))))),
            sequent!( => forall!(var!("y"), equal!(var!("y"), var!("y")))),
        );
        println!("{:?}", valid_forall_right.is_valid_inference());

        let valid_exists_left = LK::ExistsLeft(
            Box::new(LK::Axiom(sequent!(equal!(var!("x"), var!("x")) => ))),
            sequent!(exists!(var!("y"), equal!(var!("y"), var!("y"))) => ),
        );
        println!("{:?}", valid_exists_left.is_valid_inference());

        let valid_exists_right = LK::ExistsRight(
            Box::new(LK::Axiom(sequent!( => equal!(var!("x"), var!("x"))))),
            sequent!( => exists!(var!("y"), equal!(var!("y"), var!("y")))),
        );
        println!("{:?}", valid_exists_right.is_valid_inference());

        let valid_cut = LK::Cut(
            Box::new([
                LK::Axiom(sequent!( => pred!("p"))),
                LK::Axiom(sequent!(pred!("p") => )),
            ]),
            sequent!( => ),
        );
        println!("{:?}", valid_cut.is_valid_inference());
    } else {
        println!("{:?}", parser);
    }
}
