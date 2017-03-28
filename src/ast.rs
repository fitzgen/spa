use error;
use std::collections::HashMap;
use std::hash;
use std::iter::FromIterator;

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

#[derive(Debug, PartialEq, Eq)]
pub struct Program<'a> {
    pub functions: Vec<Function<'a>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AstNode<'a, 'b>
    where 'a: 'b
{
    Identifier(Identifier<'a>),
    Expression(&'b Expression<'a>),
    Statement(&'b Statement<'a>),
    Function(&'b Function<'a>),
    Program(&'b Program<'a>),
}

impl<'a, 'b, 'c> From<&'c AstNode<'a, 'b>> for *const ()
    where 'c: 'a,
          'a: 'b
{
    fn from(node: &'c AstNode<'a, 'b>) -> *const () {
        match *node {
            AstNode::Identifier(id) => id.0.as_ptr() as *const _,
            AstNode::Expression(expr) => expr as *const _ as *const _,
            AstNode::Statement(stmt) => stmt as *const _ as *const _,
            AstNode::Function(func) => func as *const _ as *const _,
            AstNode::Program(prgm) => prgm as *const _ as *const _,
        }
    }
}

impl<'a, 'b> hash::Hash for AstNode<'a, 'b>
    where 'a: 'b
{
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        let addr: *const () = self.into();
        addr.hash(state);
    }
}

impl<'a, 'b> From<Identifier<'a>> for AstNode<'a, 'b>
    where 'a: 'b
{
    fn from(id: Identifier<'a>) -> AstNode<'a, 'b> {
        AstNode::Identifier(id)
    }
}

impl<'a, 'b> From<&'b Expression<'a>> for AstNode<'a, 'b>
    where 'a: 'b
{
    fn from(expr: &'b Expression<'a>) -> AstNode<'a, 'b> {
        match *expr {
            Expression::Identifier(id) => id.into(),
            ref otherwise => AstNode::Expression(otherwise),
        }
    }
}

impl<'a, 'b> From<&'b Statement<'a>> for AstNode<'a, 'b>
    where 'a: 'b
{
    fn from(stmt: &'b Statement<'a>) -> AstNode<'a, 'b> {
        AstNode::Statement(stmt)
    }
}

impl<'a, 'b> From<&'b Function<'a>> for AstNode<'a, 'b>
    where 'a: 'b
{
    fn from(func: &'b Function<'a>) -> AstNode<'a, 'b> {
        AstNode::Function(func)
    }
}

impl<'a, 'b> From<&'b Program<'a>> for AstNode<'a, 'b>
    where 'a: 'b
{
    fn from(prgm: &'b Program<'a>) -> AstNode<'a, 'b> {
        AstNode::Program(prgm)
    }
}

/// Dump an AST to stdout. Has even more detailed diagnostics than exposed the
/// `Debug` implementation.
pub trait DumpAst {
    /// Dump this AST to stdout.
    fn dump_ast(&self, indent: usize);
}

fn print_indent(indent: usize) {
    for _ in 0..indent {
        print!("    ");
    }
}

fn addr<'a, 'b, T>(t: T) -> *const ()
    where 'a: 'b,
          T: Into<AstNode<'a, 'b>>
{
    let t = t.into();
    (&t).into()
}

impl<'a, 'b> DumpAst for AstNode<'a, 'b>
    where 'a: 'b
{
    fn dump_ast(&self, indent: usize) {
        match *self {
            AstNode::Identifier(i) => i.dump_ast(indent),
            AstNode::Expression(e) => e.dump_ast(indent),
            AstNode::Statement(s) => s.dump_ast(indent),
            AstNode::Function(f) => f.dump_ast(indent),
            AstNode::Program(p) => p.dump_ast(indent),
        }
    }
}

impl<'a> DumpAst for Identifier<'a> {
    fn dump_ast(&self, indent: usize) {
        print!("{:p} ", addr(*self));
        print_indent(indent);
        println!("{:?}", self);
    }
}

impl<'a> DumpAst for Expression<'a> {
    fn dump_ast(&self, indent: usize) {
        print!("{:p} ", addr(self));
        print_indent(indent);
        print!("Expression::");

        match *self {
            Expression::Input => {
                println!("Input");
            }
            Expression::Malloc => {
                println!("Malloc");
            }
            Expression::Integer(x) => {
                println!("Integer({})", x);
            }
            Expression::Null => {
                println!("Null");
            }
            Expression::AddressOf(ident) => {
                println!("AddressOf");
                ident.dump_ast(indent + 1);
            }
            Expression::Identifier(ident) => {
                println!("Identifier");
                ident.dump_ast(indent + 1);
            }
            Expression::Negation(ref expr) => {
                println!("Negation");
                expr.dump_ast(indent + 1);
            }
            Expression::Deref(ref expr) => {
                println!("Deref");
                expr.dump_ast(indent + 1);
            }
            Expression::Subtraction(ref operands) => {
                println!("Subtraction");
                operands[0].dump_ast(indent + 1);
                operands[1].dump_ast(indent + 1);
            }
            Expression::Multiplication(ref operands) => {
                println!("Multiplication");
                operands[0].dump_ast(indent + 1);
                operands[1].dump_ast(indent + 1);
            }
            Expression::Division(ref operands) => {
                println!("Division");
                operands[0].dump_ast(indent + 1);
                operands[1].dump_ast(indent + 1);
            }
            Expression::Equal(ref operands) => {
                println!("Equal");
                operands[0].dump_ast(indent + 1);
                operands[1].dump_ast(indent + 1);
            }
            Expression::Greater(ref operands) => {
                println!("Greater");
                operands[0].dump_ast(indent + 1);
                operands[1].dump_ast(indent + 1);
            }
            Expression::Addition(ref operands) => {
                println!("Addition");
                operands[0].dump_ast(indent + 1);
                operands[1].dump_ast(indent + 1);
            }
            Expression::Call(ref ident, ref args) => {
                println!("Call");

                print!("........... ");
                print_indent(indent + 1);
                println!("ident:");
                ident.dump_ast(indent + 2);

                print!("........... ");
                print_indent(indent + 1);
                println!("args:");
                for arg in args {
                    arg.dump_ast(indent + 2);
                }
            }
            Expression::IndirectCall(ref func, ref args) => {
                println!("IndirectCall");

                print!("........... ");
                print_indent(indent + 1);
                println!("func:");
                func.dump_ast(indent + 2);

                print!("........... ");
                print_indent(indent + 1);
                println!("args:");
                for arg in args {
                    arg.dump_ast(indent + 2);
                }
            }
        }
    }
}

impl<'a> DumpAst for Statement<'a> {
    fn dump_ast(&self, indent: usize) {
        print!("{:p} ", addr(self));
        print_indent(indent);
        print!("Statement::");

        match *self {
            Statement::Assignment(ref ident, ref expr) => {
                println!("Assignment");
                ident.dump_ast(indent + 1);
                expr.dump_ast(indent + 1);
            }
            Statement::DerefAssignment(ref ident, ref expr) => {
                println!("DerefAssignment");
                ident.dump_ast(indent + 1);
                expr.dump_ast(indent + 1);
            }
            Statement::Output(ref expr) => {
                println!("Output");
                expr.dump_ast(indent + 1);
            }
            Statement::If(ref condition, ref consequent, ref alternative) => {
                println!("If");

                print!("........... ");
                print_indent(indent + 1);
                println!("Condition");
                condition.dump_ast(indent + 2);

                print!("........... ");
                print_indent(indent + 1);
                println!("Consequent");
                for s in consequent {
                    s.dump_ast(indent + 2);
                }

                if let Some(ref alternative) = *alternative {
                    print!("........... ");
                    print_indent(indent + 1);
                    println!("Alternative");
                    for s in alternative {
                        s.dump_ast(indent + 2);
                    }
                } else {
                    print!("........... ");
                    print_indent(indent + 1);
                    println!("No alternative");
                }
            }
            Statement::While(ref condition, ref statements) => {
                println!("While");

                print!("........... ");
                print_indent(indent + 1);
                println!("Condition");
                condition.dump_ast(indent + 2);

                print!("........... ");
                print_indent(indent + 1);
                println!("Statements");
                for s in statements {
                    s.dump_ast(indent + 2);
                }
            }
        }
    }
}

impl<'a> DumpAst for Function<'a> {
    fn dump_ast(&self, indent: usize) {
        print!("{:p} ", addr(self));
        print_indent(indent);
        println!("Function");

        print!("........... ");
        print_indent(indent + 1);
        println!("Name");
        self.name.dump_ast(indent + 2);

        print!("........... ");
        print_indent(indent + 1);
        println!("Arguments");
        for a in &self.arguments {
            a.dump_ast(indent + 2);
        }

        print!("........... ");
        print_indent(indent + 1);
        println!("Variables");
        for v in &self.variables {
            v.dump_ast(indent + 2);
        }

        print!("........... ");
        print_indent(indent + 1);
        println!("Body");
        for b in &self.body {
            b.dump_ast(indent + 2);
        }

        print!("........... ");
        print_indent(indent + 1);
        println!("Return");
        self.ret.dump_ast(indent + 2);
    }
}

impl<'a> DumpAst for Program<'a> {
    fn dump_ast(&self, indent: usize) {
        print!("{:p} ", addr(self));
        print_indent(indent);
        println!("Program");

        for f in &self.functions {
            f.dump_ast(indent + 1);
        }
    }
}

/// Walk the AST and ensure all identifiers are canonicalized.
///
/// After canonicalizing identifiers, all equivalent identifiers have pointer
/// equality. We allow locals to shadow functions, and we do the Right Thing, in
/// that functions and locals with the same name end up with different canonical
/// pointers.
pub trait CanonicalizeIdentifiers<'a> {
    fn canonicalize_identifiers<'b>(&'b mut self,
                                    functions: &'b HashMap<&'a str, &'a str>,
                                    locals: &'b HashMap<&'a str, &'a str>)
                                    -> error::Result<()>
        where 'a: 'b;
}

impl<'a> CanonicalizeIdentifiers<'a> for Identifier<'a> {
    fn canonicalize_identifiers<'b>(&'b mut self,
                                    functions: &'b HashMap<&'a str, &'a str>,
                                    locals: &'b HashMap<&'a str, &'a str>)
                                    -> error::Result<()>
        where 'a: 'b
    {
        self.0 = locals.get(self.0)
            .or_else(|| functions.get(self.0))
            .ok_or(error::Error::ReferenceToUnknownIdentifier)?;
        Ok(())
    }
}

impl<'a> CanonicalizeIdentifiers<'a> for Expression<'a> {
    fn canonicalize_identifiers<'b>(&'b mut self,
                                    functions: &'b HashMap<&'a str, &'a str>,
                                    locals: &'b HashMap<&'a str, &'a str>)
                                    -> error::Result<()>
        where 'a: 'b
    {
        match *self {
            Expression::Input |
            Expression::Malloc |
            Expression::Integer(_) |
            Expression::Null => {}

            Expression::AddressOf(ref mut ident) |
            Expression::Identifier(ref mut ident) => {
                ident.canonicalize_identifiers(functions, locals)?;
            }

            Expression::Negation(ref mut expr) |
            Expression::Deref(ref mut expr) => {
                expr.canonicalize_identifiers(functions, locals)?;
            }

            Expression::Subtraction(ref mut operands) |
            Expression::Multiplication(ref mut operands) |
            Expression::Division(ref mut operands) |
            Expression::Equal(ref mut operands) |
            Expression::Greater(ref mut operands) |
            Expression::Addition(ref mut operands) => {
                operands.canonicalize_identifiers(functions, locals)?;
            }

            Expression::Call(ref mut ident, ref mut args) => {
                ident.canonicalize_identifiers(functions, locals)?;
                args.canonicalize_identifiers(functions, locals)?;
            }

            Expression::IndirectCall(ref mut func, ref mut args) => {
                func.canonicalize_identifiers(functions, locals)?;
                args.canonicalize_identifiers(functions, locals)?;
            }
        }

        Ok(())
    }
}

impl<'a> CanonicalizeIdentifiers<'a> for Statement<'a> {
    fn canonicalize_identifiers<'b>(&'b mut self,
                                    functions: &'b HashMap<&'a str, &'a str>,
                                    locals: &'b HashMap<&'a str, &'a str>)
                                    -> error::Result<()>
        where 'a: 'b
    {
        match *self {
            Statement::Assignment(ref mut ident, ref mut expr) |
            Statement::DerefAssignment(ref mut ident, ref mut expr) => {
                // These can only be locals, not functions.
                ident.0 = locals.get(ident.0).ok_or(error::Error::ReferenceToUnknownIdentifier)?;
                expr.canonicalize_identifiers(functions, locals)?;
            }
            Statement::Output(ref mut expr) => {
                expr.canonicalize_identifiers(functions, locals)?;
            }
            Statement::If(ref mut condition, ref mut consequent, ref mut alternative) => {
                condition.canonicalize_identifiers(functions, locals)?;
                consequent.canonicalize_identifiers(functions, locals)?;
                alternative.canonicalize_identifiers(functions, locals)?;
            }
            Statement::While(ref mut condition, ref mut statements) => {
                condition.canonicalize_identifiers(functions, locals)?;
                statements.canonicalize_identifiers(functions, locals)?;
            }
        }

        Ok(())
    }
}

impl<'a> CanonicalizeIdentifiers<'a> for Function<'a> {
    fn canonicalize_identifiers<'b>(&'b mut self,
                                    functions: &'b HashMap<&'a str, &'a str>,
                                    _: &'b HashMap<&'a str, &'a str>)
                                    -> error::Result<()>
        where 'a: 'b
    {
        let new_locals = self.arguments
            .iter()
            .chain(self.variables.iter())
            .map(|ident| (ident.0, ident.0));
        let new_locals = HashMap::from_iter(new_locals);

        self.body.canonicalize_identifiers(functions, &new_locals)?;
        self.ret.canonicalize_identifiers(functions, &new_locals)?;

        Ok(())
    }
}

impl<'a> CanonicalizeIdentifiers<'a> for Program<'a> {
    fn canonicalize_identifiers<'b>(&'b mut self,
                                    _: &'b HashMap<&'a str, &'a str>,
                                    _: &'b HashMap<&'a str, &'a str>)
                                    -> error::Result<()>
        where 'a: 'b
    {
        let mut functions = HashMap::with_capacity(self.functions.len());
        for f in &self.functions {
            functions.insert(f.name.0, f.name.0);
        }

        let locals = HashMap::new();

        self.functions.canonicalize_identifiers(&functions, &locals)
    }
}

impl<'a, T> CanonicalizeIdentifiers<'a> for Vec<T>
    where T: CanonicalizeIdentifiers<'a>
{
    fn canonicalize_identifiers<'b>(&'b mut self,
                                    functions: &'b HashMap<&'a str, &'a str>,
                                    locals: &'b HashMap<&'a str, &'a str>)
                                    -> error::Result<()>
        where 'a: 'b
    {
        for x in self.iter_mut() {
            x.canonicalize_identifiers(functions, locals)?;
        }
        Ok(())
    }
}

impl<'a, T> CanonicalizeIdentifiers<'a> for Option<T>
    where T: CanonicalizeIdentifiers<'a>
{
    fn canonicalize_identifiers<'b>(&'b mut self,
                                    functions: &'b HashMap<&'a str, &'a str>,
                                    locals: &'b HashMap<&'a str, &'a str>)
                                    -> error::Result<()>
        where 'a: 'b
    {
        if let Some(ref mut x) = *self {
            x.canonicalize_identifiers(functions, locals)?;
        }
        Ok(())
    }
}

impl<'a, T> CanonicalizeIdentifiers<'a> for Box<[T; 2]>
    where T: CanonicalizeIdentifiers<'a>
{
    fn canonicalize_identifiers<'b>(&'b mut self,
                                    functions: &'b HashMap<&'a str, &'a str>,
                                    locals: &'b HashMap<&'a str, &'a str>)
                                    -> error::Result<()>
        where 'a: 'b
    {
        self[0].canonicalize_identifiers(functions, locals)?;
        self[1].canonicalize_identifiers(functions, locals)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[test]
    fn canonicalize_identifiers() {
        let foo = "foo";
        let bar = "bar";

        let mut functions = HashMap::new();
        functions.insert(foo, foo);

        let mut locals = HashMap::new();
        locals.insert(bar, bar);

        // Canonicalize function strings.

        let foo_string = String::from(foo);
        let mut foo_ident = Identifier(&foo_string);
        assert!(foo_ident.0.as_ptr() != foo.as_ptr(),
                "different pointers before canonicalization");

        assert!(foo_ident.canonicalize_identifiers(&functions, &locals).is_ok());
        assert_eq!(foo_ident.0.as_ptr(),
                   foo.as_ptr(),
                   "same pointers after canonicalization");

        // Canonicalize local strings.

        let bar_string = String::from(bar);
        let mut bar_ident = Identifier(&bar_string);
        assert!(bar_ident.0.as_ptr() != bar.as_ptr(),
                "different pointers before canonicalization");

        assert!(bar_ident.canonicalize_identifiers(&functions, &locals).is_ok());
        assert_eq!(bar_ident.0.as_ptr(),
                   bar.as_ptr(),
                   "same pointers after canonicalization");

        // Locals have priority over functions.

        let foo_local = String::from("foo");
        let foo_local_str = foo_local.as_str();
        assert!(foo_local_str.as_ptr() != foo.as_ptr());

        let mut locals = locals.clone();
        locals.insert(foo_local_str, foo_local_str);

        let yet_another_foo_string = String::from(foo);
        let mut yet_another_foo_ident = Identifier(&yet_another_foo_string);
        assert!(yet_another_foo_ident.0.as_ptr() != foo.as_ptr(),
                "different pointers before canonicalization");
        assert!(yet_another_foo_ident.0.as_ptr() != foo_local_str.as_ptr(),
                "different pointers before canonicalization");

        assert!(yet_another_foo_ident.canonicalize_identifiers(&functions, &locals).is_ok());
        assert!(yet_another_foo_ident.0.as_ptr() != foo.as_ptr());
        assert_eq!(yet_another_foo_ident.0.as_ptr(),
                   foo_local_str.as_ptr(),
                   "same pointers after canonicalization");

        // Unknown identifiers are an error.

        let mut unknown_ident = Identifier("unknown");
        assert_eq!(unknown_ident.canonicalize_identifiers(&functions, &locals),
                   Err(error::Error::ReferenceToUnknownIdentifier));
    }
}
