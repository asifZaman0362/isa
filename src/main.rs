use thiserror::Error;
/*
 *
 *  Custom assembly:
 *
 *  labels:
 *  value ::= register | $<hex,dec,bin> | #register
 *  add [register] [value]
 *  sub ...
 *  mul ...
 *  div ...
 *  xor ...
 *  or  ...
 *  and ...
 *  ...
 *  not [register]
 *  cmp [value] [value]
 *  jmp [value]
 *  ...
 *  nop
 *
 *
 */

macro_rules! define_mnemonics {
    ( $( $name:ident ),* ) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum Mnemonic {
            $( $name ),*
        }

        impl Mnemonic {
            pub fn from_str(s: &str) -> Option<Self> {
                match s.to_lowercase().as_str() {
                    $( stringify!($name.to_lowercase()) => Some(Mnemonic::$name), )*
                    _ => None
                }
            }

            pub fn as_str(&self) -> &'static str {
                match self {
                    $( Mnemonic::$name => stringify!($name), )*
                }
            }

            pub fn all() -> &'static [&'static str] {
                &[
                    $( stringify!($name) ),*
                ]
            }
        }
    };
}

define_mnemonics!(
    Add, Sub, Mul, Div, Xor, Or, And, Cmp, Jz, Jmp, Jnz, Load, Store, Exit
);

const TEST: &'static str = r#"
; program start
start:
    load r1, $10 ; load the decimal value 10 into r1
    load r2, r1  ; load the value from r1 into r2
    add r2, r1   ; add r1 and r2 and store the result in r2
    exit
"#;

#[derive(Debug)]
enum ParserErrorKind {
    LexerError(LexerErrorKind),
}

#[derive(Error, Debug)]
struct ParserError {
    line: usize,
    col: usize,
    error_kind: ParserErrorKind,
}

#[derive(Debug)]
enum LexerErrorKind {
    UnexpectedSymbol(char),
    MalformedInteger(char),
}

#[derive(Error, Debug)]
struct LexerError {
    line: usize,
    col: usize,
    error_kind: LexerErrorKind,
}

impl std::fmt::Display for LexerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "Lexer Error at: ({}, {})\nerror: {:?}",
            self.line, self.col, self.error_kind
        ))
    }
}

impl std::fmt::Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "Parser Error at: ({}, {})\nerror: {:?}",
            self.line, self.col, self.error_kind
        ))
    }
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

#[derive(Debug)]
struct Token {
    line: usize,
    col: usize,
    token_kind: TokenKind,
}

#[derive(Debug)]
enum Register {
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    R8,
    R9,
    R10,
    R11,
    R12,
    R13,
    R14,
    R15,
    R16,
    R17,
    R18,
    R19,
    R20,
    R21,
    R22,
    R23,
    R24,
    R25,
    R26,
    R27,
    R28,
    R29,
}

#[derive(Debug)]
enum TokenKind {
    Immediate(u64),
    Address(Register),
    Register(Register),
    Label(String),
    Mnemonic(Mnemonic),
    Comma,
    Colon,
}

fn scan_number(lexeme: &str) -> Result<u64, usize> {
    if let Some(hex) = lexeme.strip_prefix("0x") {
        let mut i = hex.chars().enumerate();
        let _ = loop {
            if let Some((pos, c)) = i.next() {
                if !c.is_numeric() && !"abcdefABCDEF".contains(c) {
                    break Err(pos + 2);
                }
            } else {
                break Ok(());
            }
        }?;
        Ok(u64::from_str_radix(hex, 16).unwrap())
    } else if let Some(bin) = lexeme.strip_prefix("0b") {
        let mut i = bin.chars().enumerate();
        let _ = loop {
            if let Some((pos, c)) = i.next() {
                if !"01".contains(c) {
                    break Err(pos + 2);
                }
            } else {
                break Ok(());
            }
        }?;
        Ok(u64::from_str_radix(bin, 2).unwrap())
    } else {
        let mut i = lexeme.chars().enumerate();
        let _ = loop {
            if let Some((pos, c)) = i.next() {
                if !c.is_numeric() {
                    break Err(pos);
                }
            } else {
                break Ok(());
            }
        }?;
        Ok(u64::from_str_radix(lexeme, 10).unwrap())
    }
}

fn scan_register(lexeme: &str) -> Option<Register> {
    if let Some(r_no) = lexeme.strip_prefix("r") {
        if let Ok(r_no) = r_no.parse::<u8>() {
            match r_no {
                1 => Some(Register::R1),
                2 => Some(Register::R2),
                3 => Some(Register::R3),
                4 => Some(Register::R4),
                5 => Some(Register::R5),
                6 => Some(Register::R6),
                7 => Some(Register::R7),
                8 => Some(Register::R8),
                9 => Some(Register::R9),
                10 => Some(Register::R10),
                11 => Some(Register::R11),
                12 => Some(Register::R12),
                13 => Some(Register::R13),
                14 => Some(Register::R14),
                15 => Some(Register::R15),
                16 => Some(Register::R16),
                17 => Some(Register::R17),
                18 => Some(Register::R18),
                19 => Some(Register::R19),
                20 => Some(Register::R20),
                21 => Some(Register::R21),
                22 => Some(Register::R22),
                23 => Some(Register::R23),
                24 => Some(Register::R24),
                25 => Some(Register::R25),
                26 => Some(Register::R26),
                27 => Some(Register::R27),
                28 => Some(Register::R28),
                29 => Some(Register::R29),
                _ => None,
            }
        } else {
            None
        }
    } else {
        None
    }
}

fn make_token(
    asm: &str,
    start: &mut usize,
    end: &mut usize,
    line: usize,
    _col: usize,
) -> Result<Option<Token>, LexerError> {
    if start == end {
        Ok(None)
    } else {
        let lexeme = &asm[*start..=*end];
        *start = *end;
        let col = _col - lexeme.len();
        if let Some(numeric) = lexeme.strip_prefix("$") {
            scan_number(numeric)
                .map(|num| {
                    Some(Token {
                        line,
                        col,
                        token_kind: TokenKind::Immediate(num),
                    })
                })
                .map_err(|err| LexerError {
                    line,
                    col: _col + err,
                    error_kind: LexerErrorKind::UnexpectedSymbol(lexeme.as_bytes()[err] as char),
                })
        } else {
            Ok(if let Some(reg) = scan_register(lexeme) {
                Some(Token {
                    line,
                    col,
                    token_kind: TokenKind::Register(reg),
                })
            } else if let Some(mnemonic) = Mnemonic::from_str(lexeme) {
                Some(Token {
                    line,
                    col,
                    token_kind: TokenKind::Mnemonic(mnemonic),
                })
            } else {
                Some(Token {
                    line,
                    col,
                    token_kind: TokenKind::Label(lexeme.to_owned()),
                })
            })
        }
    }
}

fn tokenise(asm: &str) -> Result<Vec<Token>, LexerError> {
    let mut token_stream = vec![];
    let mut i = asm.chars();
    let (mut start, mut end) = (0usize, 0usize);
    let (mut line, mut col) = (1usize, 1usize);
    'outer: while let Some(c) = i.next() {
        if c.is_whitespace() {
            if let Some(token) = make_token(asm, &mut start, &mut end, line, col)? {
                token_stream.push(token);
            }
            if c == '\n' {
                line += 1;
                col = 1;
            }
            start += 1;
            end = start;
        } else if c == ';' {
            if let Some(token) = make_token(asm, &mut start, &mut end, line, col)? {
                token_stream.push(token);
            }
            while let Some(c) = i.next() {
                if c == '\n' {
                    line += 1;
                    col = 1;
                    continue 'outer;
                }
            }
        } else if c == ',' {
            if let Some(token) = make_token(asm, &mut start, &mut end, line, col)? {
                token_stream.push(token);
            }
            token_stream.push(Token {
                line,
                col,
                token_kind: TokenKind::Comma,
            });
            start += 1;
            end = start;
        } else if c == ':' {
            if let Some(token) = make_token(asm, &mut start, &mut end, line, col)? {
                token_stream.push(token);
            }
            token_stream.push(Token {
                line,
                col,
                token_kind: TokenKind::Colon,
            });
            start += 1;
            end = start;
        } else if c.is_alphanumeric() {
            end += 1;
        } else {
            return Err(LexerError {
                line,
                col,
                error_kind: LexerErrorKind::UnexpectedSymbol(c),
            });
        }
        col += 1;
    }
    Ok(token_stream)
}

fn parse_assembly(asm: &str) -> Result<Vec<u64>, ParserError> {
    Ok(vec![])
}

#[test]
fn test_lexer() -> Result<(), LexerError> {
    tokenise(TEST).map(|tokens| {
        for token in tokens {
            dbg!(token);
        }
    })
}

fn main() {
    println!("Hello, world!");
}
