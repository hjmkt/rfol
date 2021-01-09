extern crate itertools;

use crate::data::*;
use itertools::Itertools;

#[derive(Debug)]
pub struct Tokenizer<'a> {
    pub iter: std::str::Chars<'a>,
    pub tokens: Vec<Token>,
}

impl<'a> Tokenizer<'a> {
    pub fn new() -> Tokenizer<'a> {
        Tokenizer {
            iter: "".chars(),
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
                    let symbol = self.iter.take_while_ref(|s| {
                        if let '(' | ')' | '=' | 'V' | 'E' | ' ' = s {
                            false
                        } else {
                            true
                        }
                    });
                    Token::Symbol(s.to_string() + &symbol.collect::<String>())
                }
            };
            self.tokens.push(token);
            self._tokenize();
        } else {
            ()
        }
    }

    pub fn tokenize(&mut self, s: &'a str) -> Vec<Token> {
        self.iter = s.chars();
        self.tokens.clear();
        self._tokenize();
        self.tokens.to_vec()
    }
}
