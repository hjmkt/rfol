use crate::data::*;

#[derive(Debug)]
pub struct Parser<'a>{
    pub iter: std::iter::Peekable<std::slice::Iter<'a, Token>>,
}

impl<'a> Parser<'a>{
    pub fn new() -> Parser<'a>{ Parser{iter: [].iter().peekable()} }

    fn _parse_term(&mut self) -> Result<Term, String>{
        if let Some(token) = self.iter.next(){
            let term = match token{
                Token::LParen =>{
                    if let Some(Token::Symbol(s)) = self.iter.next(){
                        let mut terms = vec![];
                        loop{
                            if let Ok(term) = self._parse_term(){ terms.push(term) }
                            else { return Err("Parse error.".into()); }
                            if let Some(Token::RParen) = self.iter.peek(){ break }
                        }
                        Ok(Term::Func(s.into(), terms))
                    } else{ Err("Parse error.".into()) }
                },
                Token::Symbol(s) => return Ok(Term::Var(s.into())),
                _ => Err("Parse error.".into()),
            };
            if let Some(Token::RParen) = self.iter.next() { term }
            else { Err("Parse error.".into()) }
        } else { Err("Parse error.".into()) }
    }

    fn _parse(&mut self) -> Result<Formula, String>{
        if let Some(Token::LParen) = self.iter.next(){
            let formula = match self.iter.next(){
                Some(Token::Symbol(s)) => {
                    let mut terms = vec![];
                    loop{
                        if let Ok(term) = self._parse_term(){ terms.push(term) }
                        else { return Err("Parse error.".into()); }
                        if let Some(Token::RParen) = self.iter.peek(){ break }
                    }
                    Ok(Formula::Pred(s.into(), terms))
                },
                Some(Token::Not) => {
                    if let Ok(formula) = self._parse(){ Ok(Formula::Not(Box::new(formula))) }
                    else{ Err("Parse error.".into()) }
                },
                Some(t @ Token::And | t @ Token::Or) => {
                    if let (Ok(lhs), Ok(rhs)) = (self._parse(), self._parse()){ match t{
                        Token::And => Ok(Formula::And(Box::new(lhs), Box::new(rhs))),
                        _ => Ok(Formula::Or(Box::new(lhs), Box::new(rhs))),
                    }} else { Err("Parse error.".into()) }
                },
                Some(Token::Equal) => {
                    if let (Ok(lhs), Ok(rhs)) = (self._parse_term(), self._parse_term()){
                        Ok(Formula::Equal(lhs, rhs))
                    } else { Err("Parse error.".into()) }
                },
                Some(t @ Token::Forall | t @ Token::Exists) => {
                    match (self.iter.next(), self._parse()){
                        (Some(Token::Symbol(s)), Ok(fml)) => match t{
                            Token::Forall => Ok(Formula::Forall(Term::Var(s.into()), Box::new(fml))),
                            Token::Exists => Ok(Formula::Exists(Term::Var(s.into()), Box::new(fml))),
                            _ => Err("Parse error.".into())
                        },
                        _ => Err("Parse error.".into()),
                    }
                },
                _ => Err("Parse error.".into()),
            };
            if let Some(Token::RParen) = self.iter.next() { formula }
            else { Err("Parse error.".into()) }
        } else{ Err("Parse error.".into()) }
    }

    pub fn parse(&mut self, tokens: &'a Vec<Token>) -> Result<Formula, String>{
        self.iter = tokens.iter().peekable();
        self._parse()
    }
}
