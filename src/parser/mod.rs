// lalrpop generated code has many warnings that make clippy unhappy.
#![allow(warnings)]

include!(concat!(env!("OUT_DIR"), "/parser/tip.rs"));

#[cfg(test)]
mod tests {
    use ast;
    use super::*;

    #[test]
    fn integer() {
        assert_eq!(parse_Integer("12"), Ok(12));
        assert!(parse_Integer("zzz").is_err());
    }

    #[test]
    fn identifier() {
        assert_eq!(parse_Identifier("abc"), Ok(ast::Identifier("abc")));
        assert_eq!(
            parse_Identifier("abc_123_lala"),
            Ok(ast::Identifier("abc_123_lala"))
        );
        assert!(parse_Identifier("_foo").is_err());
        assert!(parse_Identifier("1abc").is_err());
    }

    #[test]
    fn expression() {
        assert_eq!(
            parse_Expression("abc"),
            Ok(ast::Expression::Identifier(ast::Identifier("abc")))
        );
        assert_eq!(parse_Expression("123"), Ok(ast::Expression::Integer(123)));
        assert_eq!(parse_Expression("input"), Ok(ast::Expression::Input));
        assert_eq!(parse_Expression("malloc"), Ok(ast::Expression::Malloc));
        assert_eq!(parse_Expression("null"), Ok(ast::Expression::Null));
        assert_eq!(
            parse_Expression("abc == 123"),
            Ok(ast::Expression::Equal(Box::new([
                ast::Expression::Identifier(ast::Identifier("abc")),
                ast::Expression::Integer(123)
            ])))
        );
        assert_eq!(
            parse_Expression("abc > 123"),
            Ok(ast::Expression::Greater(Box::new([
                ast::Expression::Identifier(ast::Identifier("abc")),
                ast::Expression::Integer(123)
            ])))
        );
        assert_eq!(
            parse_Expression("123 * abc + 42"),
            Ok(ast::Expression::Addition(Box::new([
                ast::Expression::Multiplication(Box::new([
                    ast::Expression::Integer(123),
                    ast::Expression::Identifier(ast::Identifier("abc"))
                ])),
                ast::Expression::Integer(42)
            ])))
        );
        assert_eq!(
            parse_Expression("(abc + 123) * -2"),
            Ok(ast::Expression::Multiplication(Box::new([
                ast::Expression::Addition(Box::new([
                    ast::Expression::Identifier(ast::Identifier("abc")),
                    ast::Expression::Integer(123)
                ])),
                ast::Expression::Negation(Box::new(ast::Expression::Integer(2)))
            ])))
        );
        assert_eq!(
            parse_Expression("foo(1, 2, 3)"),
            Ok(ast::Expression::Call(
                ast::Identifier("foo"),
                vec![
                    ast::Expression::Integer(1),
                    ast::Expression::Integer(2),
                    ast::Expression::Integer(3),
                ]
            ))
        );
        assert_eq!(
            parse_Expression("(foo)(1, 2, 3)"),
            Ok(ast::Expression::IndirectCall(
                Box::new(ast::Expression::Identifier(ast::Identifier("foo"))),
                vec![
                    ast::Expression::Integer(1),
                    ast::Expression::Integer(2),
                    ast::Expression::Integer(3),
                ]
            ))
        );
        assert_eq!(
            parse_Expression("&v"),
            Ok(ast::Expression::AddressOf(ast::Identifier("v")))
        );
        assert_eq!(
            parse_Expression("*v == *w"),
            Ok(ast::Expression::Equal(Box::new([
                ast::Expression::Deref(Box::new(ast::Expression::Identifier(ast::Identifier("v")))),
                ast::Expression::Deref(Box::new(ast::Expression::Identifier(ast::Identifier("w"))))
            ])))
        );
    }

    #[test]
    fn statement() {
        assert_eq!(
            parse_Statement("foo = bar;"),
            Ok(ast::Statement::Assignment(
                ast::Identifier("foo"),
                ast::Expression::Identifier(ast::Identifier("bar"))
            ))
        );
        assert_eq!(
            parse_Statement("*foo = bar;"),
            Ok(ast::Statement::DerefAssignment(
                ast::Identifier("foo"),
                ast::Expression::Identifier(ast::Identifier("bar"))
            ))
        );
        assert_eq!(
            parse_Statement("output 123;"),
            Ok(ast::Statement::Output(ast::Expression::Integer(123)))
        );
        assert_eq!(
            parse_Statement("if (1) { output 2; }"),
            Ok(ast::Statement::If(
                ast::Expression::Integer(1),
                vec![ast::Statement::Output(ast::Expression::Integer(2))],
                None
            ))
        );
        assert_eq!(
            parse_Statement("if (1) { output 2; } else { output 3; }"),
            Ok(ast::Statement::If(
                ast::Expression::Integer(1),
                vec![ast::Statement::Output(ast::Expression::Integer(2))],
                Some(vec![ast::Statement::Output(ast::Expression::Integer(3))])
            ))
        );
        assert_eq!(
            parse_Statement("while (input) { output 1; }"),
            Ok(ast::Statement::While(
                ast::Expression::Input,
                vec![ast::Statement::Output(ast::Expression::Integer(1))]
            ))
        );
    }

    #[test]
    fn function() {
        assert_eq!(
            parse_Function("foo(w, x) { var y, z; output 1; return 2; }"),
            Ok(ast::Function {
                name: ast::Identifier("foo"),
                arguments: vec![ast::Identifier("w"), ast::Identifier("x")],
                variables: vec![ast::Identifier("y"), ast::Identifier("z")],
                body: vec![ast::Statement::Output(ast::Expression::Integer(1))],
                ret: ast::Expression::Integer(2),
            })
        );
    }

    #[test]
    fn program() {
        assert!(
            parse_Program("").is_err(),
            "a program has at least one function"
        );
        assert!(parse_Program("foo(w, x) { var y, z; output 1; return 2; }").is_ok());
        assert!(
            parse_Program(
                "
foo(w, x) { var y, z; output 1; return 2; }
bar(x) { var y; output 1; return x; }
"
            ).is_ok()
        );
        assert!(parse_Program("id(x) { return x; }").is_ok());
    }
}
