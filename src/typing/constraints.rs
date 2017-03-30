//! Type constraints and their generation.

use ast;
use std::io::{self, Write};
use typing::{Context, TypeId};
use typing::ty::{Function, Type};

/// An equality constraint between two types.
///
/// This expresses the constraint that `self.0 == self.1`.
#[derive(Clone, Copy, Debug)]
pub struct TypeConstraint(pub TypeId, pub TypeId);

impl TypeConstraint {
    /// Construct a new type constraint.
    pub fn new<T, U>(t: T, u: U) -> TypeConstraint
        where T: Into<TypeId>,
              U: Into<TypeId>
    {
        TypeConstraint(t.into(), u.into())
    }

    /// Display this type constraint, writing it to the given output.
    ///
    /// Not a `Display` implementation because we need the context as an extra
    /// parameter.
    pub fn display<W: Write>(&self, ctx: &Context, w: &mut W) -> io::Result<()> {
        ctx.display_type(w, self.0)?;
        write!(w, " == ")?;
        ctx.display_type(w, self.1)
    }
}

/// A trait for walking the AST and generating type constraints.
pub trait ConstrainTypes<'a> {
    /// Generate the type constraints for this AST node and all other nodes
    /// transitively reachable from it.
    ///
    /// Report each type constraint by invoking the `f` function.
    ///
    /// This callback interface allows us to avoid allocations compared to
    /// returning a `Vec`. Compared to a `&mut Vec<TypeConstraint>` out
    /// parameter, this allows easier testing, as well as filtering trivially
    /// true constraints like `int == int` immediately, rather than before
    /// inserting them into the constraint set (which can in turn potentially
    /// save some storage resizing). In practice, `f` should always get inlined,
    /// and we'll avoid function call overhead as well.
    fn constrain_types<'b, F>(&'b self, ctx: &mut Context<'a, 'b>, f: &mut F)
        where 'a: 'b,
              F: FnMut(TypeConstraint);
}

impl<'a> ConstrainTypes<'a> for ast::Expression<'a> {
    fn constrain_types<'b, F>(&'b self, ctx: &mut Context<'a, 'b>, f: &mut F)
        where 'a: 'b,
              F: FnMut(TypeConstraint)
    {
        let self_ty_var = ctx.type_var_for_node(self);
        match *self {
            ast::Expression::Identifier(_) => {
                // Expression -> AstNode will collapse Expression::Identifier to
                // an AstNode::Identifier instead of an
                // AstNode::Expression(Expression::Identifier), so we don't need
                // to constrain the self type var to be equal to the underlying
                // id here.
            }

            ast::Expression::Input |
            ast::Expression::Integer(_) => {
                f(TypeConstraint::new(self_ty_var, ctx.int_type()));
            }

            ast::Expression::Malloc | ast::Expression::Null => {
                let pointee_ty = ctx.fresh_type_var();
                let pointer_ty = ctx.insert_type(Type::new_pointer(pointee_ty));
                f(TypeConstraint::new(self_ty_var, pointer_ty));
            }

            ast::Expression::AddressOf(id) => {
                let pointee_ty = ctx.type_var_for_node(id);
                let pointer_ty = ctx.insert_type(Type::new_pointer(pointee_ty));
                f(TypeConstraint::new(self_ty_var, pointer_ty));
            }

            ast::Expression::Deref(ref expr) => {
                let pointer_ty = ctx.insert_type(Type::new_pointer(self_ty_var));
                f(TypeConstraint::new(pointer_ty, ctx.type_var_for_node(&**expr)));
                expr.constrain_types(ctx, f);
            }

            ast::Expression::Addition(ref exprs) |
            ast::Expression::Subtraction(ref exprs) |
            ast::Expression::Multiplication(ref exprs) |
            ast::Expression::Division(ref exprs) |
            ast::Expression::Equal(ref exprs) |
            ast::Expression::Greater(ref exprs) => {
                f(TypeConstraint::new(self_ty_var, ctx.int_type()));
                f(TypeConstraint::new(ctx.type_var_for_node(&exprs[0]), ctx.int_type()));
                f(TypeConstraint::new(ctx.type_var_for_node(&exprs[1]), ctx.int_type()));
                exprs[0].constrain_types(ctx, f);
                exprs[1].constrain_types(ctx, f);
            }

            ast::Expression::Negation(ref expr) => {
                f(TypeConstraint::new(self_ty_var, ctx.int_type()));
                f(TypeConstraint::new(ctx.type_var_for_node(&**expr), ctx.int_type()));
                expr.constrain_types(ctx, f);
            }

            ast::Expression::Call(func_id, ref args) => {
                let arg_types: Vec<_> = args.iter().map(|a| ctx.type_var_for_node(&*a)).collect();
                let func_ty = ctx.insert_function(Function::new(arg_types, self_ty_var));
                f(TypeConstraint::new(func_ty, ctx.type_var_for_node(func_id)));
                for arg in args.iter() {
                    arg.constrain_types(ctx, f);
                }
            }

            ast::Expression::IndirectCall(ref expr, ref args) => {
                let arg_types: Vec<_> = args.iter().map(|a| ctx.type_var_for_node(&*a)).collect();
                let func_ty = ctx.insert_function(Function::new(arg_types, self_ty_var));
                f(TypeConstraint::new(func_ty, ctx.type_var_for_node(&**expr)));
                expr.constrain_types(ctx, f);
                for arg in args.iter() {
                    arg.constrain_types(ctx, f);
                }
            }
        }
    }
}

impl<'a> ConstrainTypes<'a> for ast::Statement<'a> {
    fn constrain_types<'b, F>(&'b self, ctx: &mut Context<'a, 'b>, f: &mut F)
        where 'a: 'b,
              F: FnMut(TypeConstraint)
    {
        match *self {
            ast::Statement::Assignment(id, ref expr) => {
                f(TypeConstraint::new(ctx.type_var_for_node(id), ctx.type_var_for_node(expr)));
                expr.constrain_types(ctx, f);
            }
            ast::Statement::DerefAssignment(id, ref expr) => {
                let expr_ty = ctx.type_var_for_node(expr);
                let pointer_ty = ctx.insert_type(Type::new_pointer(expr_ty));
                f(TypeConstraint::new(pointer_ty, ctx.type_var_for_node(id)));
                expr.constrain_types(ctx, f);
            }
            ast::Statement::Output(ref expr) => {
                f(TypeConstraint::new(ctx.type_var_for_node(expr), ctx.int_type()));
                expr.constrain_types(ctx, f);
            }
            ast::Statement::If(ref condition, ref consequent, ref alternative) => {
                f(TypeConstraint::new(ctx.type_var_for_node(condition), ctx.int_type()));
                condition.constrain_types(ctx, f);
                for stmt in consequent.iter() {
                    stmt.constrain_types(ctx, f);
                }
                if let Some(ref alternative) = *alternative {
                    for stmt in alternative.iter() {
                        stmt.constrain_types(ctx, f);
                    }
                }
            }
            ast::Statement::While(ref condition, ref statements) => {
                f(TypeConstraint::new(ctx.type_var_for_node(condition), ctx.int_type()));
                condition.constrain_types(ctx, f);
                for stmt in statements.iter() {
                    stmt.constrain_types(ctx, f);
                }
            }
        }
    }
}

impl<'a> ConstrainTypes<'a> for ast::Function<'a> {
    fn constrain_types<'b, F>(&'b self, ctx: &mut Context<'a, 'b>, f: &mut F)
        where 'a: 'b,
              F: FnMut(TypeConstraint)
    {
        let param_types: Vec<_> = self.arguments
            .iter()
            .map(|a| ctx.type_var_for_node(*a))
            .collect();
        let return_ty = ctx.type_var_for_node(&self.ret);
        let func_ty = ctx.insert_function(Function::new(param_types, return_ty));
        f(TypeConstraint::new(ctx.type_var_for_node(self.name), func_ty));

        for stmt in &self.body {
            stmt.constrain_types(ctx, f);
        }
        self.ret.constrain_types(ctx, f);
    }
}

impl<'a> ConstrainTypes<'a> for ast::Program<'a> {
    fn constrain_types<'b, F>(&'b self, ctx: &mut Context<'a, 'b>, f: &mut F)
        where 'a: 'b,
              F: FnMut(TypeConstraint)
    {
        for func in &self.functions {
            func.constrain_types(ctx, f);
        }
    }
}

#[cfg(test)]
mod tests {
    use ast::{CanonicalizeIdentifiers, DumpAst};
    use parser;
    use std::collections::HashMap;
    use typing::Context;
    use typing::constraints::ConstrainTypes;

    fn assert_constraints<C>(source: &'static str, constraints: C)
        where C: AsRef<[&'static str]>
    {
        let constraints = constraints.as_ref();
        let mut program =
            Box::new(parser::parse_Program(source).expect("source parses as a program"));

        println!();
        println!("AST before CanonicalizeIdentifiers");
        println!();
        program.dump_ast(0);

        let functions = HashMap::new();
        let locals = HashMap::new();
        program.canonicalize_identifiers(&functions, &locals).unwrap();

        println!();
        println!("AST after CanonicalizeIdentifiers");
        println!();
        program.dump_ast(0);
        println!();

        let mut ctx = Context::new();
        let mut actual_constraints = vec![];
        program.constrain_types(&mut ctx,
                                &mut |constraint| { actual_constraints.push(constraint); });

        let actual_constraints: Vec<_> = actual_constraints.into_iter()
            .map(|c| {
                     let mut constraint = Vec::new();
                     c.display(&ctx, &mut constraint).unwrap();
                     String::from(String::from_utf8_lossy(&constraint))
                 })
            .collect();
        println!("actual_constraints = {:#?}", actual_constraints);

        assert_eq!(constraints.len(), actual_constraints.len());

        for (actual, expected) in actual_constraints.iter().zip(constraints.iter()) {
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn polymorphic_id_function() {
        let source = "
poly(x) {
    return x;
}
";
        assert_constraints(source, ["?b == (?a) -> ?a"]);
    }

    #[test]
    fn polymorphic_deref_function() {
        let source = "
poly(x) {
    return *x;
}
";
        assert_constraints(source, ["?c == (?a) -> ?b", "&?b == ?a"]);
    }

    #[test]
    fn iterable_factorial() {
        let source = "
ite(n) {
    var f;
    f = 1;
    while (n>0) {
        f = f*n;
        n = n-1;
    }
    return f;
}
";
        assert_constraints(source,
                           ["?c == (?a) -> ?b",
                            "?b == ?d",
                            "?d == int",
                            "?e == int",
                            "?e == int",
                            "?a == int",
                            "?f == int",
                            "?f == int",
                            "?b == ?g",
                            "?g == int",
                            "?b == int",
                            "?a == int",
                            "?a == ?h",
                            "?h == int",
                            "?a == int",
                            "?i == int",
                            "?i == int"]);
    }

    #[test]
    fn recursive_factorial() {
        let source = "
rec(n) {
    var f;
    if (n==0) { f=1; }
    else { f=n*rec(n-1); }
    return f;
}
";
        assert_constraints(source,
                           ["?c == (?a) -> ?b",
                            "?d == int",
                            "?d == int",
                            "?a == int",
                            "?e == int",
                            "?e == int",
                            "?b == ?f",
                            "?f == int",
                            "?b == ?g",
                            "?g == int",
                            "?a == int",
                            "?h == int",
                            "(?i) -> ?h == ?c",
                            "?i == int",
                            "?a == int",
                            "?j == int",
                            "?j == int"]);
    }

    #[test]
    fn complicated_factorial() {
        let source = "
foo(p,x) {
    var f,q;
    if (*p == 0) { f = 1; }
    else {
        q = malloc;
        *q = (*p) - 1;
        f = (*p) * ((x)(q, x));
    }
    return f;
}
";
        assert_constraints(source,
                           ["?d == (?a, ?b) -> ?c",
                            "?e == int",
                            "?e == int",
                            "?f == int",
                            "?g == int",
                            "&?f == ?a",
                            "?g == int",
                            "?c == ?h",
                            "?h == int",
                            "?i == ?j",
                            "?j == &?k",
                            "&?l == ?i",
                            "?l == int",
                            "?m == int",
                            "?n == int",
                            "&?m == ?a",
                            "?n == int",
                            "?c == ?o",
                            "?o == int",
                            "?p == int",
                            "?q == int",
                            "&?p == ?a",
                            "(?i, ?b) -> ?q == ?b"]);
    }

    #[test]
    fn recursive_type() {
        let source = "
f() {
    var p;
    p = malloc;
    *p = p;
    return 0;
}
";
        assert_constraints(source,
                           ["?b == () -> ?a", "?c == ?d", "?d == &?e", "&?c == ?c", "?a == int"]);
    }
}
