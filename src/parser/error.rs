use super::lexer::{
    TokenKind,
    error::{LexerError, LexerErrorKind},
};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ParserErrorKind {
    #[error(transparent)]
    LexerError(#[from] LexerErrorKind),
    #[error("expected {1:?} but found {0:?} instead")]
    UnexpectedToken(TokenKind, Vec<&'static str>),
    #[error("value out of range ({0}, {1})")]
    OutOfRange(usize, usize),
    #[error("unexpectedly reached end of file")]
    UnexpectedEof,
}

#[derive(Error, Debug)]
#[error("Error parsing at {line}:{col} :: {error_kind:?}")]
pub struct ParserError {
    pub line: usize,
    pub col: usize,
    pub error_kind: ParserErrorKind,
}

impl From<LexerError> for ParserError {
    fn from(value: LexerError) -> Self {
        ParserError {
            line: value.line,
            col: value.col,
            error_kind: ParserErrorKind::LexerError(value.error_kind),
        }
    }
}
