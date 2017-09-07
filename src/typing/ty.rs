use std::fmt;
use super::{FunctionId, TypeId};

/// A bound or unbound type variable.
#[derive(Copy, Clone, Debug, Hash, PartialEq, Eq)]
pub struct TypeVariable(usize);

impl TypeVariable {
    pub fn new(n: usize) -> TypeVariable {
        TypeVariable(n)
    }
}

impl fmt::Display for TypeVariable {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fn write_alpha_digit(f: &mut fmt::Formatter, digit: u8) -> fmt::Result {
            write!(f, "{}", ('a' as u8 + digit) as char)
        }

        fn write_alpha(f: &mut fmt::Formatter, n: usize) -> fmt::Result {
            if n < 26 {
                write_alpha_digit(f, n as u8)
            } else {
                write_alpha(f, n / 26)?;
                write_alpha_digit(f, (n % 26) as u8)
            }
        }

        write!(f, "?")?;
        write_alpha(f, self.0)
    }
}

/// A function type.
///
/// `Function` is split out from `Type` so that `Type` can be `Copy` and is a
/// little more ergonomic to use in most cases.
#[derive(Clone, Debug)]
pub struct Function {
    params: Vec<TypeId>,
    return_type: TypeId,
}

impl Function {
    /// Construct a new `Function` type.
    pub fn new<I, J, T>(params: I, return_type: T) -> Function
    where
        I: IntoIterator<Item = J>,
        J: Into<TypeId>,
        T: Into<TypeId>,
    {
        Function {
            params: params.into_iter().map(|p| p.into()).collect(),
            return_type: return_type.into(),
        }
    }

    /// Get this function's parameter types.
    pub fn params(&self) -> &[TypeId] {
        &self.params[..]
    }

    /// Get this function's return type.
    pub fn return_type(&self) -> TypeId {
        self.return_type
    }
}

/// A type or type variable.
#[derive(Clone, Copy, Debug)]
pub enum Type {
    /// The integer type.
    Int,

    /// A pointer to another type.
    Pointer(TypeId),

    /// A function type.
    Function(FunctionId),

    /// A type variable.
    Variable(TypeVariable),
}

impl Type {
    /// Construct a new pointer type.
    pub fn new_pointer<T>(id: T) -> Type
    where
        T: Into<TypeId>,
    {
        Type::Pointer(id.into())
    }

    /// Get the type pointed to by this pointer type, or `None` if this is not a
    /// pointer type.
    pub fn pointer(&self) -> Option<TypeId> {
        match *self {
            Type::Pointer(ty) => Some(ty),
            _ => None,
        }
    }

    /// Get this function's id, or `None` if this is not a function type.
    pub fn function(&self) -> Option<FunctionId> {
        match *self {
            Type::Function(func) => Some(func),
            _ => None,
        }
    }

    /// Get this type's variable, or `None` if this type is not a type variable.
    pub fn variable(&self) -> Option<TypeVariable> {
        match *self {
            Type::Variable(var) => Some(var),
            _ => None,
        }
    }
}
