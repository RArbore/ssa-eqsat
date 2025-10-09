use std::collections::BTreeMap;

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

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
pub enum UnaryOp {
    Negate,
    Not,
}

#[derive(Debug, Clone, Copy, PartialOrd, Ord, PartialEq, Eq)]
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

pub type Terms = (Vec<Term>, BTreeMap<Term, TermId>);

type Context = BTreeMap<Symbol, TermId>;

fn add_term(terms: &mut Terms, term: Term) -> TermId {
    if let Some(id) = terms.1.get(&term) {
        *id
    } else {
        let id = alloc_term(terms);
        set_term(terms, id, term);
        id
    }
}

fn alloc_term(terms: &mut Terms) -> TermId {
    let id = terms.0.len() as TermId;
    terms.0.push(Term::Param(!0));
    id
}

fn set_term(terms: &mut Terms, id: TermId, term: Term) {
    terms.0[id as usize] = term;
    terms.1.insert(term, id);
}

pub fn naive_ssa_translation(func: &FunctionAST) -> Terms {
    let mut terms = Terms::default();
    let mut ctx = Context::new();
    for (idx, sym) in func.params.iter().enumerate() {
        ctx.insert(*sym, add_term(&mut terms, Term::Param(idx as i32)));
    }
    handle_stmt(&mut ctx, &mut terms, &func.body);
    terms
}

fn handle_stmt(ctx: &mut Context, terms: &mut Terms, stmt: &StatementAST) {
    use StatementAST::*;
    match stmt {
        Block(_, stmts) => {
            stmts.iter().for_each(|stmt| handle_stmt(ctx, terms, stmt))
        }
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
                let Some(else_term) = else_ctx.get(sym) else { continue };
                ctx.insert(*sym, add_term(terms, Term::Phi(*loc, *then_term, *else_term)));
            }
        }
        While(loc, cond_expr, body_stmt) => {
            let mut sym_entry_phi_tuples = vec![];
            for (sym, entry) in ctx.iter_mut() {
                let old_entry = *entry;
                let phi = alloc_term(terms);
                *entry = phi;
                sym_entry_phi_tuples.push((*sym, old_entry, phi));
            }
            handle_expr(ctx, terms, cond_expr);
            let mut body_ctx = ctx.clone();
            handle_stmt(&mut body_ctx, terms, body_stmt);
            for (sym, entry, phi) in sym_entry_phi_tuples {
                let bottom = body_ctx[&sym];
                set_term(terms, phi, Term::Phi(*loc, entry, bottom));
            }
        }
        Return(_, expr) => {
            handle_expr(ctx, terms, expr);
        },
    }
}

fn handle_expr(ctx: &Context, terms: &mut Terms, expr: &ExpressionAST) -> TermId {
    use ExpressionAST::*;
    match expr {
        NumberLiteral(val) => add_term(terms, Term::Constant(*val)),
        Variable(sym) => ctx[sym],
        Call(_, _) => todo!(),
        Add(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            add_term(terms, Term::Binary(BinaryOp::Add, lhs, rhs))
        }
        Subtract(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            add_term(terms, Term::Binary(BinaryOp::Sub, lhs, rhs))
        }
        Multiply(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            add_term(terms, Term::Binary(BinaryOp::Mul, lhs, rhs))
        }
        Divide(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            add_term(terms, Term::Binary(BinaryOp::Div, lhs, rhs))
        }
        Modulo(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            add_term(terms, Term::Binary(BinaryOp::Rem, lhs, rhs))
        }
        EqualsEquals(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            add_term(terms, Term::Binary(BinaryOp::EE, lhs, rhs))
        }
        NotEquals(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            add_term(terms, Term::Binary(BinaryOp::NE, lhs, rhs))
        }
        Less(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            add_term(terms, Term::Binary(BinaryOp::LT, lhs, rhs))
        }
        LessEquals(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            add_term(terms, Term::Binary(BinaryOp::LE, lhs, rhs))
        }
        Greater(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            add_term(terms, Term::Binary(BinaryOp::GT, lhs, rhs))
        }
        GreaterEquals(lhs, rhs) => {
            let lhs = handle_expr(ctx, terms, lhs);
            let rhs = handle_expr(ctx, terms, rhs);
            add_term(terms, Term::Binary(BinaryOp::GE, lhs, rhs))
        }
    }
}

pub fn terms_to_dot(terms: &Terms) {

}
