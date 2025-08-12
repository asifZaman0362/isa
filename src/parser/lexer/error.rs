use thiserror::Error;
#[derive(Error, Debug)]
pub enum LexerErrorKind {
    #[error("unexpected symbol {0}")]
    UnexpectedSymbol(char),
    #[error("expected a valid digit found '{0}' instead")]
    MalformedInteger(char),
}

#[derive(Error, Debug)]
#[error("Invalid syntax at {line}:{col} :: {error_kind:?}")]
pub struct LexerError {
    pub line: usize,
    pub col: usize,
    pub error_kind: LexerErrorKind,
}
