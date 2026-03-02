use thiserror::Error;

/// Errors that can occur during graph triangularization.
#[derive(Error, Debug)]
pub enum TriangularError {
    #[error("Internal error: {0}")]
    InternalError(String),
}
