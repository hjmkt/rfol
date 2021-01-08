pub mod data;
pub mod tokenizer;
pub mod parser;

#[test]
fn tokenizer_works(){
    use data::Token::*;
    use tokenizer::Tokenizer;

    let mut tokenizer = Tokenizer::new();
    let tokens = tokenizer.tokenize("(Vx0 (Ex1 (^ (= (a x y) (b x y)) (v (~ (p y)) (q y)))))");
    let gt = vec![LParen, Forall, Symbol("x0".to_string()), LParen, Exists, Symbol("x1".to_string()), LParen, And, LParen, Equal, LParen, Symbol("a".to_string()), Symbol("x".to_string()), Symbol("y".to_string()), RParen, LParen, Symbol("b".to_string()), Symbol("x".to_string()), Symbol("y".to_string()), RParen, RParen, LParen, Or, LParen, Not, LParen, Symbol("p".to_string()), Symbol("y".to_string()), RParen, RParen, LParen, Symbol("q".to_string()), Symbol("y".to_string()), RParen, RParen, RParen, RParen, RParen];

    assert_eq!(gt, tokens);
}

#[test]
fn parser_works(){
    use data::Token::*;
    use data::Term::*;
    use data::Formula;
    use parser::Parser;

    let mut parser = Parser::new();
    let tokens = vec![LParen, Forall, Symbol("x0".to_string()), LParen, Exists, Symbol("x1".to_string()), LParen, And, LParen, Equal, LParen, Symbol("a".to_string()), Symbol("x".to_string()), Symbol("y".to_string()), RParen, LParen, Symbol("b".to_string()), Symbol("x".to_string()), Symbol("y".to_string()), RParen, RParen, LParen, Or, LParen, Not, LParen, Symbol("p".to_string()), Symbol("y".to_string()), RParen, RParen, LParen, Symbol("q".to_string()), Symbol("y".to_string()), RParen, RParen, RParen, RParen, RParen];
    let gt = Formula::Forall(Var("x0".to_string()), Box::new(Formula::Exists(Var("x1".to_string()), Box::new(Formula::And(Box::new(Formula::Equal(Func("a".to_string(), vec![Var("x".to_string()), Var("y".to_string())]), Func("b".to_string(), vec![Var("x".to_string()), Var("y".to_string())]))), Box::new(Formula::Or(Box::new(Formula::Not(Box::new(Formula::Pred("p".to_string(), vec![Var("y".to_string())])))), Box::new(Formula::Pred("q".to_string(), vec![Var("y".to_string())])))))))));

    if let Ok(formula) = parser.parse(&tokens){
        assert_eq!(gt, formula);
    } else{
        panic!("Parse error.");
    }
}
