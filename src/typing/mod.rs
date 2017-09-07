//! Types, inference, and checking.

pub mod constraints;
pub mod ty;

use ast;
use error;
use self::constraints::TypeConstraint;
use self::ty::{Function, Type, TypeVariable};
use std::collections::{HashMap, HashSet};
use std::collections::hash_map::Entry;
use std::io::{self, Write};

/// A reference to a type in the types graph.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct TypeId(usize);

impl From<TypeId> for usize {
    fn from(var: TypeId) -> usize {
        var.0
    }
}

/// A reference to a type variable in the context's types graph.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct TypeVariableId(TypeId);

impl From<TypeVariableId> for usize {
    fn from(var: TypeVariableId) -> usize {
        var.0.into()
    }
}

impl From<TypeVariableId> for TypeId {
    fn from(var: TypeVariableId) -> TypeId {
        var.0
    }
}

/// A reference to a function type.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct FunctionId(usize);

impl From<FunctionId> for usize {
    fn from(var: FunctionId) -> usize {
        var.0
    }
}

/// Common context needed throughout type checking.
#[derive(Debug)]
pub struct Context<'a, 'b>
where
    'a: 'b,
{
    type_var_id_counter: usize,
    ast_types: HashMap<ast::AstNode<'a, 'b>, TypeVariableId>,
    types: Vec<Type>,
    function_types: Vec<Option<Function>>,
    substitutions: HashMap<TypeVariable, TypeId>,
}

impl<'a, 'b> Context<'a, 'b>
where
    'a: 'b,
{
    /// Construct a new `Context`.
    pub fn new() -> Context<'a, 'b> {
        Context {
            type_var_id_counter: 0,
            ast_types: HashMap::new(),
            types: vec![Type::Int],
            function_types: Vec::new(),
            substitutions: HashMap::new(),
        }
    }

    /// Create a fresh type variable.
    pub fn fresh_type_var(&mut self) -> TypeVariableId {
        let id = TypeVariableId(TypeId(self.types.len()));
        let var = TypeVariable::new(self.type_var_id_counter);
        self.type_var_id_counter += 1;
        self.types.push(Type::Variable(var));
        id
    }

    /// Get or create the type variable for the given AST node.
    pub fn type_var_for_node<N>(&mut self, node: N) -> TypeVariableId
    where
        N: Into<ast::AstNode<'a, 'b>>,
    {
        let node = node.into();
        match self.ast_types.entry(node) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                // Really unfortunate, but the borrow checker requires we
                // duplicate `fresh_type_var` inline here.
                let id = TypeVariableId(TypeId(self.types.len()));
                let var = TypeVariable::new(self.type_var_id_counter);
                self.type_var_id_counter += 1;
                self.types.push(Type::Variable(var));
                *entry.insert(id)
            }
        }
    }

    fn take_function(&mut self, id: FunctionId) -> Function {
        let idx: usize = id.into();
        assert!(idx < self.function_types.len());
        self.function_types[idx]
            .take()
            .expect("function should not already be taken")
    }

    fn replace_function(&mut self, id: FunctionId, func: Function) {
        let idx: usize = id.into();
        assert!(idx < self.function_types.len());
        assert!(self.function_types[idx].is_none());
        self.function_types[idx] = Some(func);
    }

    /// Get the (id of the) canonical `Type::Int`.
    ///
    /// Having a single canonical `Type::Int` prevents the many duplicates that
    /// would otherwise occur, saving space.
    pub fn int_type(&self) -> TypeId {
        match self.types[0] {
            Type::Int => TypeId(0),
            otherwise => panic!(
                "TypeId(0) should always be the canonical Type::Int! Found {:?}",
                otherwise
            ),
        }
    }

    /// Insert a new type into the types graph, and get its id. The type must
    /// not be a `Type::Function`, use `insert_function` for those types.
    pub fn insert_type(&mut self, ty: Type) -> TypeId {
        if let Some(func_id) = ty.function() {
            let idx: usize = func_id.into();
            assert!(
                idx < self.function_types.len(),
                "Call insert_function instead of insert_type for function types"
            );
        }

        let id = TypeId(self.types.len());
        self.types.push(ty);
        id
    }

    /// Insert a new function into the types graph, and get its id.
    pub fn insert_function(&mut self, func: Function) -> TypeId {
        let id = FunctionId(self.function_types.len());
        self.function_types.push(Some(func));
        let func_ty = Type::Function(id);
        self.insert_type(func_ty)
    }

    /// Get the type with the given id.
    pub fn get_type(&self, id: TypeId) -> Type {
        let idx: usize = id.into();
        self.types
            .get(idx)
            .expect("should have a type at Type Id's index")
            .clone()
    }

    /// Set the type with the given id.
    pub fn set_type(&mut self, id: TypeId, ty: Type) {
        let idx: usize = id.into();
        let slot = self.types
            .get_mut(idx)
            .expect("should have a type at TypeId's index");
        *slot = ty;
    }

    /// Define a new substitution, replacing all occurrences of `var` with `ty`.
    pub fn extend_substitutions(&mut self, var: TypeVariable, ty: TypeId) {
        let substitutions: Vec<_> = self.substitutions.values().cloned().collect();
        for sub in substitutions {
            self.apply_one_substitution(sub, var, ty)
        }
        self.substitutions.insert(var, ty);
    }

    /// Replace all occurrences of the `old` type variable inside the `within`
    /// type with references to the `new` type.
    fn apply_one_substitution(&mut self, within: TypeId, old: TypeVariable, new: TypeId) {
        match self.get_type(within) {
            Type::Int => return,
            Type::Variable(var) if var != old => return,
            Type::Variable(var) => {
                assert_eq!(var, old);
                let new_ty = self.get_type(new);
                self.set_type(within, new_ty);
            }
            Type::Pointer(id) => {
                self.apply_one_substitution(id, old, new);
            }
            Type::Function(func_id) => {
                let func = self.take_function(func_id);
                for p in func.params() {
                    self.apply_one_substitution(*p, old, new);
                }
                self.apply_one_substitution(func.return_type(), old, new);
                self.replace_function(func_id, func);
            }
        };
    }

    /// Apply the context's substitutions to the given type.
    pub fn apply_all_substitutions(&mut self, within: TypeId) {
        match self.get_type(within) {
            Type::Int => return,
            Type::Variable(var) => if let Some(new_ty_id) = self.substitutions.get(&var).cloned() {
                let new_ty = self.get_type(new_ty_id);
                self.set_type(within, new_ty);
            },
            Type::Pointer(id) => {
                self.apply_all_substitutions(id);
            }
            Type::Function(func_id) => {
                let func = self.take_function(func_id);
                for p in func.params() {
                    self.apply_all_substitutions(*p);
                }
                self.apply_all_substitutions(func.return_type());
                self.replace_function(func_id, func);
            }
        }
    }

    /// Unify the given type constraints.
    pub fn unify<C>(&mut self, constraints: C) -> error::Result<()>
    where
        C: IntoIterator<Item = TypeConstraint>,
    {
        let mut new_constraints = vec![];

        for TypeConstraint(left_id, right_id) in constraints {
            if left_id == right_id {
                continue;
            }

            self.apply_all_substitutions(left_id);
            self.apply_all_substitutions(right_id);

            let left = self.get_type(left_id);
            let right = self.get_type(right_id);

            match (left, right) {
                (Type::Int, Type::Int) => continue,
                (Type::Variable(var), _) if self.occurs(var, right_id) => {
                    return Err(error::Error::CircularTypeConstraints);
                }
                (Type::Variable(var), _) => {
                    self.extend_substitutions(var, right_id);
                }
                (_, Type::Variable(var)) if self.occurs(var, left_id) => {
                    return Err(error::Error::CircularTypeConstraints);
                }
                (_, Type::Variable(var)) => {
                    self.extend_substitutions(var, left_id);
                }
                (Type::Pointer(lhs), Type::Pointer(rhs)) => {
                    new_constraints.push(TypeConstraint::new(lhs, rhs));
                }
                (Type::Function(lhs), Type::Function(rhs)) => {
                    // It's a little unfortunate, but we just clone the
                    // functions out, since we need them to be available for the
                    // occurs check. Although if we *do* hit a taken function in
                    // the occurs check, it seems we definitely have a circular
                    // type. Would be good to take advantage of that in this
                    // code.
                    let lhs_idx: usize = lhs.into();
                    let rhs_idx: usize = rhs.into();
                    let lhs = self.function_types[lhs_idx].clone().unwrap();
                    let rhs = self.function_types[rhs_idx].clone().unwrap();
                    if lhs.params().len() != rhs.params().len() {
                        return Err(error::Error::UnsolvableTypeConstraints);
                    }
                    for (l, r) in lhs.params().iter().zip(rhs.params().iter()) {
                        new_constraints.push(TypeConstraint::new(*l, *r));
                    }
                    new_constraints.push(TypeConstraint::new(lhs.return_type(), rhs.return_type()));
                }
                _ => return Err(error::Error::UnsolvableTypeConstraints),
            }
        }

        if new_constraints.is_empty() {
            Ok(())
        } else {
            self.unify(new_constraints)
        }
    }

    fn occurs(&self, var: TypeVariable, ty: TypeId) -> bool {
        let ty = self.get_type(ty);

        match ty {
            Type::Int => false,
            Type::Pointer(to) => self.occurs(var, to),
            Type::Variable(var2) => var2 == var,
            Type::Function(func_id) => {
                let idx: usize = func_id.into();
                let func = self.function_types[idx].as_ref().unwrap();
                func.params().iter().any(|p| self.occurs(var, *p)) ||
                    self.occurs(var, func.return_type())
            }
        }
    }

    /// Write a nice display of the give type to the given output, following
    /// edges through the types graph (for example, from a function through its
    /// return type).
    pub fn display_type<W: Write>(&self, w: &mut W, ty: TypeId) -> io::Result<()> {
        fn display_type<W: Write>(
            me: &Context,
            w: &mut W,
            ty: TypeId,
            seen: &mut HashSet<TypeId>,
        ) -> io::Result<()> {
            if seen.contains(&ty) {
                return write!(w, "{:?}", ty);
            }
            seen.insert(ty);

            match me.get_type(ty) {
                Type::Int => {
                    write!(w, "int")?;
                }
                Type::Variable(var) => {
                    write!(w, "{}", var)?;
                }
                Type::Pointer(ty) => {
                    write!(w, "&")?;
                    display_type(me, w, ty, seen)?;
                }
                Type::Function(id) => {
                    let idx: usize = id.into();
                    let func = me.function_types[idx].as_ref().unwrap();

                    write!(w, "(")?;
                    let mut need_comma = false;
                    for &t in func.params() {
                        if need_comma {
                            write!(w, ", ")?;
                        }
                        display_type(me, w, t, seen)?;
                        need_comma = true;
                    }
                    write!(w, ") -> ")?;
                    display_type(me, w, func.return_type(), seen)?;
                }
            }

            seen.remove(&ty);
            Ok(())
        }

        let mut seen = HashSet::new();
        display_type(self, w, ty, &mut seen)
    }

    /// Dump all the AST nodes' types to the given output.
    pub fn display_ast_types<W: Write>(&self, w: &mut W) -> io::Result<()> {
        for (ast_node, &ty) in &self.ast_types {
            let addr: *const () = ast_node.into();
            write!(w, "{:p} is {:?}: ", addr, ast_node)?;
            self.display_type(w, ty.into())?;
            write!(w, "\n")?;
        }
        Ok(())
    }

    /// Dump all the type substitutions to the given output.
    pub fn display_substitutions<W: Write>(&self, w: &mut W) -> io::Result<()> {
        for (var, ty) in &self.substitutions {
            write!(w, "{} -> ", var)?;
            self.display_type(w, *ty)?;
            writeln!(w)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ast::{CanonicalizeIdentifiers, DumpAst};
    use error;
    use parser;
    use std::collections::HashMap;
    use typing::Context;
    use typing::constraints::ConstrainTypes;

    fn type_check(source: &'static str) -> error::Result<()> {
        let mut program = Box::new(
            parser::parse_Program(source).expect("source parses as a program"),
        );

        let functions = HashMap::new();
        let locals = HashMap::new();
        program
            .canonicalize_identifiers(&functions, &locals)
            .unwrap();
        program.dump_ast(0);

        let mut ctx = Context::new();
        let mut constraints = vec![];
        program.constrain_types(&mut ctx, &mut |c| { constraints.push(c); });

        ctx.unify(constraints)
    }

    #[test]
    fn poly_id() {
        let source = "
poly(x) {
    return x;
}
";
        assert!(type_check(source).is_ok());
    }

    #[test]
    fn poly_deref() {
        let source = "
poly(x) {
    return *x;
}
";
        assert!(type_check(source).is_ok());
    }

    #[test]
    fn double() {
        let source = "
double(x) {
    return x + x;
}
";
        assert!(type_check(source).is_ok());
    }

    #[test]
    fn add_pointer_and_int() {
        let source = "
f() {
    var p;
    p = malloc;
    output p + 1;
    return 0;
}
";
        assert!(match type_check(source) {
            Err(error::Error::UnsolvableTypeConstraints) => true,
            _ => false,
        });
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
        assert!(match type_check(source) {
            Err(error::Error::CircularTypeConstraints) => true,
            _ => false,
        });
    }
}
