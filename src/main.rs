mod data;
mod parser;
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
    } else {
        println!("{:?}", parser);
    }
}
