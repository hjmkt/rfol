mod data;
mod tokenizer;
mod parser;

fn main() {
    println!("Hello, world!");
    let mut tokenizer = tokenizer::Tokenizer::new();
    let tokens = tokenizer.tokenize("(Vx0 (Ex1 (^ (= (a x y) (b x y)) (v (~ (p y)) (q y)))))");
    println!("{:?}", tokens);

    let mut parser = parser::Parser::new();
    if let Ok(formula) = parser.parse(&tokens){
        println!("{:?}", formula);
    }
    else{
        println!("{:?}", parser);
    }
}
