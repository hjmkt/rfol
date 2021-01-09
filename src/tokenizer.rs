use crate::data::*;

#[derive(Debug)]
pub struct Tokenizer<'a> {
    pub iter: std::iter::Peekable<std::str::Chars<'a>>,
    pub tokens: Vec<Token>,
}

impl<'a> Tokenizer<'a> {
    pub fn new() -> Tokenizer<'a> {
        Tokenizer {
            iter: "".chars().peekable(),
            tokens: Vec::new(),
        }
    }

    fn _tokenize(&mut self) -> () {
        if let Some(s) = self.iter.next() {
            let token = match s {
                '(' => Token::LParen,
                ')' => Token::RParen,
                '~' => Token::Not,
                '^' => Token::And,
                'v' => Token::Or,
                '=' => Token::Equal,
                'V' => Token::Forall,
                'E' => Token::Exists,
                ' ' => return self._tokenize(),
                _ => {
                    let mut symbol = String::new();
                    symbol.push(s);
                    loop {
                        if let Some(s) = self.iter.peek() {
                            if let '(' | ')' | '=' | 'V' | 'E' | ' ' = s {
                                break;
                            } else {
                                symbol.push(self.iter.next().unwrap())
                            }
                        } else {
                            symbol.push(self.iter.next().unwrap())
                        }
                    }
                    Token::Symbol(symbol)
                }
            };
            self.tokens.push(token);
            self._tokenize();
        } else {
            ()
        }
    }

    pub fn tokenize(&mut self, s: &'a str) -> Vec<Token> {
        self.iter = s.chars().peekable();
        self.tokens.clear();
        self._tokenize();
        self.tokens.to_vec()
    }
}
