use crate::data::*;

#[derive(Debug)]
pub struct Parser<'a>{
    pub iter: std::iter::Peekable<std::slice::Iter<'a, Token>>,
}

impl<'a> Parser<'a>{
    pub fn new() -> Parser<'a>{
        Parser{iter: [].iter().peekable()}
    }

    fn _parse_term(&mut self) -> Result<Term, String>{
        match self.iter.next(){
            None => Err("Parse error.".to_owned()),
            Some(token) =>{
                let term = match token{
                    Token::LParen =>{
                        match self.iter.next(){
                            Some(Token::Symbol(s)) => {
                                let mut terms = vec![];
                                loop{
                                    match self._parse_term(){
                                        Ok(term) => terms.push(term),
                                        _ => return Err("Parse error.".to_owned())
                                    }
                                    if let Some(Token::RParen) = self.iter.peek(){
                                        break
                                    }
                                }
                                Ok(Term::Func(s.to_string(), terms))
                            },
                            _ => return Err("Parse error.".to_owned()),
                        }
                    },
                    Token::Symbol(s) => return Ok(Term::Var(s.to_string())),
                    _ => Err("Parse error.".to_owned()),
                };
                if let Some(Token::RParen) = self.iter.next(){
                    return term;
                }
                else{
                    return Err("Parse error.".to_owned());
                }
            }
        }
    }

    fn _parse(&mut self) -> Result<Formula, String>{
        match self.iter.next(){
            None => Err("Parse error.".to_owned()),
            Some(token) => match token{
                Token::LParen => {
                    let formula = match self.iter.next(){
                        Some(Token::Symbol(s)) => {
                            let mut terms = vec![];
                            loop{
                                match self._parse_term(){
                                    Ok(term) => terms.push(term),
                                    _ => return Err("Parse error.".to_owned())
                                }
                                if let Some(Token::RParen) = self.iter.peek(){
                                    break
                                }
                            }
                            Ok(Formula::Pred(s.to_string(), terms))
                        },
                        Some(Token::Not) => {
                            if let Ok(formula) = self._parse(){
                                Ok(Formula::Not(Box::new(formula)))
                            } else{
                                Err("Parse error.".to_owned())
                            }
                        },
                        Some(Token::And) => {
                            if let Ok(lformula) = self._parse(){
                                if let Ok(rformula) = self._parse(){
                                    Ok(Formula::And(Box::new(lformula), Box::new(rformula)))
                                }
                                else{
                                    Err("Parse error.".to_owned())
                                }
                            } else{
                                Err("Parse error.".to_owned())
                            }
                        },
                        Some(Token::Or) => {
                            if let Ok(lformula) = self._parse(){
                                if let Ok(rformula) = self._parse(){
                                    Ok(Formula::Or(Box::new(lformula), Box::new(rformula)))
                                }
                                else{
                                    Err("Parse error.".to_owned())
                                }
                            } else{
                                Err("Parse error.".to_owned())
                            }
                        },
                        Some(Token::Equal) => {
                            if let Ok(lterm) = self._parse_term(){
                                if let Ok(rterm) = self._parse_term(){
                                    Ok(Formula::Equal(lterm, rterm))
                                }
                                else{
                                    Err("Parse error.".to_owned())
                                }
                            } else{
                                Err("Parse error.".to_owned())
                            }
                        },
                        Some(Token::Forall) => {
                            if let Some(Token::Symbol(s)) = self.iter.next(){
                                match self._parse(){
                                    Ok(formula) => Ok(Formula::Forall(Term::Var(s.to_string()), Box::new(formula))),
                                    _ => Err("Parse error.".to_owned()),
                                }
                            } else{
                                Err("Parse error.".to_owned())
                            }
                        },
                        Some(Token::Exists) => {
                            if let Some(Token::Symbol(s)) = self.iter.next(){
                                match self._parse(){
                                    Ok(formula) => Ok(Formula::Exists(Term::Var(s.to_string()), Box::new(formula))),
                                    _ => Err("Parse error.".to_owned()),
                                }
                            } else{
                                Err("Parse error.".to_owned())
                            }
                        },
                        _ => return Err("Parse error.".to_owned()),
                    };
                    if let Some(Token::RParen) = self.iter.next(){
                        return formula;
                    }
                    else{
                        return Err("Parse error.".to_owned());
                    }
                },
                _ => Err("Parse error.".to_owned()),
            }
        }
    }

    pub fn parse(&mut self, tokens: &'a Vec<Token>) -> Result<Formula, String>{
        self.iter = tokens.iter().peekable();
        return self._parse();
    }
}
