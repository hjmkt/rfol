use crate::data::*;

#[derive(Debug)]
pub struct Parser<'a> {
    pub iter: std::iter::Peekable<std::slice::Iter<'a, Token>>,
}

impl<'a> Parser<'a> {
    pub fn new() -> Parser<'a> {
        Parser {
            iter: [].iter().peekable(),
        }
    }

    fn _parse_term(&mut self) -> Result<Term, &'static str> {
        if let Some(token) = self.iter.next() {
            let term = match token {
                Token::LParen => {
                    if let Some(Token::Symbol(s)) = self.iter.next() {
                        let mut terms = vec![];
                        loop {
                            if let Ok(term) = self._parse_term() {
                                terms.push(term)
                            } else {
                                return Err("Parse error.");
                            }
                            if let Some(Token::RParen) = self.iter.peek() {
                                break;
                            }
                        }
                        Ok(Term::Func(s.into(), terms))
                    } else {
                        Err("Parse error.")
                    }
                }
                Token::Symbol(s) => return Ok(Term::Var(s.into())),
                _ => Err("Parse error."),
            };
            if let Some(Token::RParen) = self.iter.next() {
                term
            } else {
                Err("Parse error.")
            }
        } else {
            Err("Parse error.")
        }
    }

    fn _parse(&mut self) -> Result<Formula, &'static str> {
        match self.iter.next() {
            Some(Token::LParen) => {
                let formula = match self.iter.next() {
                    Some(token) => match token {
                        Token::Symbol(s) => {
                            let mut terms = vec![];
                            loop {
                                if let Ok(term) = self._parse_term() {
                                    terms.push(term)
                                } else {
                                    return Err("Parse error.");
                                }
                                if let Some(Token::RParen) = self.iter.peek() {
                                    break;
                                }
                            }
                            Ok(Formula::Pred(s.into(), terms))
                        }
                        Token::Not => {
                            if let Ok(formula) = self._parse() {
                                Ok(Formula::Not(Box::new(formula)))
                            } else {
                                Err("Parse error.")
                            }
                        }
                        t @ Token::And | t @ Token::Or => {
                            if let (Ok(lhs), Ok(rhs)) = (self._parse(), self._parse()) {
                                match t {
                                    Token::And => Ok(Formula::And(Box::new(lhs), Box::new(rhs))),
                                    _ => Ok(Formula::Or(Box::new(lhs), Box::new(rhs))),
                                }
                            } else {
                                Err("Parse error.")
                            }
                        }
                        Token::Equal => {
                            if let (Ok(lhs), Ok(rhs)) = (self._parse_term(), self._parse_term()) {
                                Ok(Formula::Equal(lhs, rhs))
                            } else {
                                Err("Parse error.")
                            }
                        }
                        t @ Token::Forall | t @ Token::Exists => {
                            match (self.iter.next(), self._parse()) {
                                (Some(Token::Symbol(s)), Ok(fml)) => match t {
                                    Token::Forall => {
                                        Ok(Formula::Forall(Term::Var(s.into()), Box::new(fml)))
                                    }
                                    Token::Exists => {
                                        Ok(Formula::Exists(Term::Var(s.into()), Box::new(fml)))
                                    }
                                    _ => Err("Parse error."),
                                },
                                _ => Err("Parse error."),
                            }
                        }
                        _ => Err("Parse error."),
                    },
                    _ => Err("Parse error."),
                };
                if let Some(Token::RParen) = self.iter.next() {
                    formula
                } else {
                    Err("Parse error.")
                }
            }
            Some(Token::Symbol(s)) => Ok(Formula::Pred(s.into(), vec![])),
            _ => Err("Parse error."),
        }
    }

    pub fn parse(&mut self, tokens: &'a Vec<Token>) -> Result<Formula, &'static str> {
        self.iter = tokens.iter().peekable();
        self._parse()
    }
}
