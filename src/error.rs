use std::error;
use std::fmt;

/// All the kinds of errors that can occur when compiling TIP.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// Found a reference to an unknown identifier.
    ReferenceToUnknownIdentifier,
    /// Found circular type constraints.
    CircularTypeConstraints,
    /// Found unsolvable type constraints, AKA a type error.
    UnsolvableTypeConstraints,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", error::Error::description(self))
    }
}

impl error::Error for Error {
    fn description(&self) -> &'static str {
        match *self {
            Error::ReferenceToUnknownIdentifier => "found a reference to an unknown identifier",
            Error::CircularTypeConstraints => "found circular type constraints",
            Error::UnsolvableTypeConstraints => {
                "found unsolvable type constraints, AKA a type error"
            }
        }
    }
}

/// A result of `T` or a TIP error.
pub type Result<T> = ::std::result::Result<T, Error>;
