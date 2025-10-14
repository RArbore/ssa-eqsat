use std::collections::BTreeMap;
use std::io::{Result, Write};

use enumn::N;
use string_interner::Symbol as _;

use crate::ast::{ExpressionAST, FunctionAST, Location, StatementAST, Symbol};

pub type TermId = u32;

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub enum Term {
    Constant(i32),
    Param(i32),
    Phi(Location, TermId, TermId),
    Unary(UnaryOp, TermId),
    Binary(BinaryOp, TermId, TermId),
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, N)]
pub enum UnaryOp {
    Negate,
    Not,
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq, N)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    EE,
    NE,
    LT,
    LE,
    GT,
    GE,
}

type Context = BTreeMap<Symbol, TermId>;

#[derive(Debug, Clone)]
pub struct Terms {
    name: Symbol,
    terms: Vec<Term>,
    intern: BTreeMap<Term, TermId>,
}

impl Term {
    fn symbol(&self) -> String {
        match self {
            Term::Constant(val) => format!("{}", val),
            Term::Param(idx) => format!("#{}", idx),
            Term::Phi(_, _, _) => "Φ".to_string(),
            Term::Unary(op, _) => format!("{:?}", op),
            Term::Binary(op, _, _) => format!("{:?}", op),
        }
    }
}

impl Terms {
    fn add_term(&mut self, term: Term) -> TermId {
        if let Some(id) = self.intern.get(&term) {
            *id
        } else {
            let id = self.alloc_term();
            self.set_term(id, term);
            id
        }
    }

    fn alloc_term(&mut self) -> TermId {
        let id = self.terms.len() as TermId;
        self.terms.push(Term::Param(!0));
        id
    }

    fn set_term(&mut self, id: TermId, term: Term) {
        self.terms[id as usize] = term;
        self.intern.insert(term, id);
    }

    pub fn terms(&self) -> impl Iterator<Item = (TermId, Term)> + '_ {
        self.terms.iter().enumerate().map(|(idx, term)| (idx as TermId, *term))
    }
}

pub fn naive_ssa_translation(func: &FunctionAST) -> Terms {
    let mut terms = Terms {
        name: func.name,
        terms: vec![],
        intern: BTreeMap::new(),
    };
    let mut ctx = Context::new();
    for (idx, sym) in func.params.iter().enumerate() {
        ctx.insert(*sym, terms.add_term(Term::Param(idx as i32)));
    }
    handle_stmt(&mut ctx, &mut terms, &func.body);
    terms
}

fn handle_stmt(ctx: &mut Context, terms: &mut Terms, stmt: &StatementAST) {
    use StatementAST::*;
    match stmt {
        Block(_, stmts) => stmts.iter().for_each(|stmt| handle_stmt(ctx, terms, stmt)),
        Assign(_, sym, expr) => {
            let term = handle_expr(ctx, terms, expr);
            ctx.insert(*sym, term);
        }
        IfElse(loc, cond_expr, then_stmt, else_stmt) => {
            handle_expr(ctx, terms, cond_expr);
            let mut then_ctx = ctx.clone();
            handle_stmt(&mut then_ctx, terms, then_stmt);
            let mut else_ctx = ctx.clone();
            if let Some(else_stmt) = else_stmt {
                handle_stmt(&mut else_ctx, terms, else_stmt);
            }
            for (sym, then_term) in &then_ctx {
                let Some(else_term) = else_ctx.get(sym) else {
                    continue;
                };
                ctx.insert(
                    *sym,
                    terms.add_term(Term::Phi(*loc, *then_term, *else_term)),
                );
            }
        }
        While(loc, cond_expr, body_stmt) => {
            let mut sym_entry_phi_tuples = vec![];
            for (sym, entry) in ctx.iter_mut() {
                let old_entry = *entry;
                let phi = terms.alloc_term();
                *entry = phi;
                sym_entry_phi_tuples.push((*sym, old_entry, phi));
            }
            handle_expr(ctx, terms, cond_expr);
            let mut body_ctx = ctx.clone();
            handle_stmt(&mut body_ctx, terms, body_stmt);
            for (sym, entry, phi) in sym_entry_phi_tuples {
                let bottom = body_ctx[&sym];
                terms.set_term(phi, Term::Phi(*loc, entry, bottom));
            }
        }
        Return(_, expr) => {
            handle_expr(ctx, terms, expr);
        }
    }
}

fn handle_expr(ctx: &Context, terms: &mut Terms, expr: &ExpressionAST) -> TermId {
    use ExpressionAST::*;
    match expr {
        NumberLiteral(val) => terms.add_term(Term::Constant(*val)),
        Variable(sym) => ctx[sym],
        Call(_, _) => todo!(),
        Add(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            terms.add_term(Term::Binary(BinaryOp::Add, lhs, rhs))
        }
        Subtract(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            terms.add_term(Term::Binary(BinaryOp::Sub, lhs, rhs))
        }
        Multiply(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            terms.add_term(Term::Binary(BinaryOp::Mul, lhs, rhs))
        }
        Divide(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            terms.add_term(Term::Binary(BinaryOp::Div, lhs, rhs))
        }
        Modulo(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            terms.add_term(Term::Binary(BinaryOp::Rem, lhs, rhs))
        }
        EqualsEquals(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            terms.add_term(Term::Binary(BinaryOp::EE, lhs, rhs))
        }
        NotEquals(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            terms.add_term(Term::Binary(BinaryOp::NE, lhs, rhs))
        }
        Less(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            terms.add_term(Term::Binary(BinaryOp::LT, lhs, rhs))
        }
        LessEquals(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            terms.add_term(Term::Binary(BinaryOp::LE, lhs, rhs))
        }
        Greater(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            terms.add_term(Term::Binary(BinaryOp::GT, lhs, rhs))
        }
        GreaterEquals(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            terms.add_term(Term::Binary(BinaryOp::GE, lhs, rhs))
        }
    }
}

pub fn terms_to_dot<W: Write>(terms: &Terms, w: &mut W) -> Result<()> {
    writeln!(w, "digraph F{} {{", terms.name.to_usize())?;
    for (term_id, term) in terms.terms() {
        writeln!(w, "N{}[label=\"{}\"];", term_id, term.symbol())?;
        match term {
            Term::Constant(_) | Term::Param(_) => {}
            Term::Unary(_, input) => writeln!(w, "N{} -> N{};", input, term_id)?,
            Term::Phi(_, lhs, rhs) | Term::Binary(_, lhs, rhs) => {
                writeln!(w, "N{} -> N{};", lhs, term_id)?;
                writeln!(w, "N{} -> N{};", rhs, term_id)?;
            }
        }
    }
    writeln!(w, "}}")
}
