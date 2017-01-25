#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Identifier<'a>(pub &'a str);

#[derive(Debug, PartialEq, Eq)]
pub enum Expression<'a> {
    Input,
    Malloc,
    Null,
    Deref(Box<Expression<'a>>),
    Integer(isize),
    Identifier(Identifier<'a>),
    Addition(Box<[Expression<'a>; 2]>),
    Subtraction(Box<[Expression<'a>; 2]>),
    Multiplication(Box<[Expression<'a>; 2]>),
    Division(Box<[Expression<'a>; 2]>),
    Equal(Box<[Expression<'a>; 2]>),
    Greater(Box<[Expression<'a>; 2]>),
    Negation(Box<Expression<'a>>),
    Call(Identifier<'a>, Vec<Expression<'a>>),
    IndirectCall(Box<Expression<'a>>, Vec<Expression<'a>>),
    AddressOf(Identifier<'a>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Statement<'a> {
    Assignment(Identifier<'a>, Expression<'a>),
    DerefAssignment(Identifier<'a>, Expression<'a>),
    Output(Expression<'a>),
    If(Expression<'a>, Vec<Statement<'a>>, Option<Vec<Statement<'a>>>),
    While(Expression<'a>, Vec<Statement<'a>>),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Function<'a> {
    pub name: Identifier<'a>,
    pub arguments: Vec<Identifier<'a>>,
    pub variables: Vec<Identifier<'a>>,
    pub body: Vec<Statement<'a>>,
    pub ret: Expression<'a>,
}
