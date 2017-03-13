use error;
use std::collections::HashMap;
use std::iter::FromIterator;

#[derive(Debug, Clone, PartialEq, Eq)]
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
