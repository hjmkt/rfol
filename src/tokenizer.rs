use crate::data::*;

#[derive(Debug)]
pub struct Tokenizer<'a>{
    pub iter: std::iter::Peekable<std::str::Chars<'a>>,
    pub tokens: Vec<Token>,
}

impl<'a> Tokenizer<'a>{
    pub fn new() -> Tokenizer<'a>{
        Tokenizer{iter: "".chars().peekable(), tokens: Vec::new()}
    }

    fn _tokenize(&mut self) -> (){
        match self.iter.next(){
            None => (),
            Some(s) => {
                let token = match s{
                    '(' => Token::LParen,
                    ')' => Token::RParen,
                    '~' => Token::Not,
                    '^' => Token::And,
                    'v' => Token::Or,
                    '=' => Token::Equal,
                    'V' => Token::Forall,
                    'E' => Token::Exists,
                    ' ' => {
                        self._tokenize();
                        return;
                    },
                    _ => {
                        let mut symbol = String::new();
                        symbol.push(s);
                        loop{
                            match self.iter.peek(){
                                None => break,
                                Some(s) => match s {
                                    '(' | ')' | '=' | 'V' | 'E' | ' ' => break,
                                    _ => symbol.push(self.iter.next().unwrap())
                                }
                            }
                        }
                        Token::Symbol(symbol)
                    }
                };
                self.tokens.push(token);
                self._tokenize();
            }
        }
    }

    pub fn tokenize(&mut self, s: &'a str) -> Vec<Token>{
        self.iter = s.chars().peekable();
        self.tokens.clear();
        self._tokenize();
        return self.tokens.to_vec();
    }
}

