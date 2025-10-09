use string_interner::StringInterner;
use string_interner::backend::StringBackend;
use string_interner::symbol::SymbolU16;

pub type Symbol = SymbolU16;
pub type Interner = StringInterner<StringBackend<Symbol>>;
pub type Location = u32;

#[derive(Debug)]
pub struct ProgramAST {
    pub funcs: Vec<FunctionAST>,
}

#[derive(Debug)]
pub struct FunctionAST {
    pub name: Symbol,
    pub params: Vec<Symbol>,
    pub location: Location,
    pub body: StatementAST,
}

#[derive(Debug)]
pub enum StatementAST {
    Block(Location, Vec<StatementAST>),
    Assign(Location, Symbol, ExpressionAST),
    IfElse(Location, ExpressionAST, Box<StatementAST>, Option<Box<StatementAST>>),
    While(Location, ExpressionAST, Box<StatementAST>),
    Return(Location, ExpressionAST),
}

impl StatementAST {
    pub fn loc(&self) -> Location {
        match self {
            StatementAST::Block(loc, ..) => *loc,
            StatementAST::Assign(loc, ..) => *loc,
            StatementAST::IfElse(loc, ..) => *loc,
            StatementAST::While(loc, ..) => *loc,
            StatementAST::Return(loc, ..) => *loc,
        }
    }
}

#[derive(Debug)]
pub enum ExpressionAST {
    NumberLiteral(i32),
    Variable(Symbol),

    Call(Symbol, Vec<ExpressionAST>),

    Add(Box<ExpressionAST>, Box<ExpressionAST>),
    Subtract(Box<ExpressionAST>, Box<ExpressionAST>),
    Multiply(Box<ExpressionAST>, Box<ExpressionAST>),
    Divide(Box<ExpressionAST>, Box<ExpressionAST>),
    Modulo(Box<ExpressionAST>, Box<ExpressionAST>),

    EqualsEquals(Box<ExpressionAST>, Box<ExpressionAST>),
    NotEquals(Box<ExpressionAST>, Box<ExpressionAST>),
    Less(Box<ExpressionAST>, Box<ExpressionAST>),
    LessEquals(Box<ExpressionAST>, Box<ExpressionAST>),
    Greater(Box<ExpressionAST>, Box<ExpressionAST>),
    GreaterEquals(Box<ExpressionAST>, Box<ExpressionAST>),
}
