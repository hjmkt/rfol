#[derive(Debug, PartialEq)]
pub enum Term{
    Var(String),
    Func(String, Vec<Term>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Token{
    LParen,
    RParen,
    Equal,
    Not,
    And,
    Or,
    Symbol(String),
    Forall,
    Exists,
}

#[derive(Debug, PartialEq)]
pub enum Formula{
    Pred(String, Vec<Term>),
    Equal(Term, Term),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Forall(Term, Box<Formula>),
    Exists(Term, Box<Formula>),
}

