use std::collections::HashMap;
use std::env;
use std::io::{Read, Write};

use paste::paste;
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

fn convert_case(lexeme: &str) -> String {
    let mut str = String::from(lexeme.as_bytes()[0] as char).to_ascii_uppercase();
    str.push_str(&lexeme[1..]);
    str
}

macro_rules! define_mnemonics {
    ( $( $name:ident ),* ) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        pub enum Mnemonic {
            $( $name ),*
        }

        impl Mnemonic {
            pub fn try_from_str(s: &str) -> Option<Self> {
                match convert_case(s).as_str() {
                    $( stringify!($name) => Some(Mnemonic::$name), )*
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

impl Mnemonic {
    fn serialiaze(&self) -> u32 {
        use Mnemonic::*;
        match self {
            // Nop
            Nop => 0x0,

            // Control instructions
            Exit => 0x1,
            Ret => 0x2,
            Jmp => 0x3,
            Jz => 0x4,
            Jnz => 0x5,
            Call => 0x6,

            // Arithmetic
            Add => 0x7,
            Sub => 0x8,
            Mul => 0x9,
            Div => 0xA,

            // Logic
            And => 0xB,
            Or => 0xC,
            Not => 0xD,
            Xor => 0xE,
            Cmp => 0xF,

            // Memory
            Load => 0x10,
            Store => 0x11,
        }
    }
}

define_mnemonics!(
    Add, Sub, Mul, Div, Xor, Or, And, Cmp, Jz, Jmp, Jnz, Load, Not, Store, Exit, Nop, Ret, Call
);

macro_rules! enum_with_names {
    ($name:ident { 
        $($variant:ident $( ($type:ty) )*),*
    }) => {
        #[derive(Debug, Clone)]
        enum $name {
            $( $variant $(($type))? ),*
        }

        impl $name {
            const fn to_str(&self) -> &'static str {
                paste! {
                    match self {
                        $( $name::$variant $(([<_ $type:lower>]))? => stringify!($variant) ),*
                    }
                }
            }
        }
    }
}

#[derive(Debug, Error)]
enum ParserErrorKind {
    #[error(transparent)]
    LexerError(#[from] LexerErrorKind),
    #[error("expected {1:?} but found {0:?} instead")]
    UnexpectedToken(TokenKind, Vec<&'static str>),
    #[error("unexpectedly reached end of file")]
    UnexpectedEof,
}

#[derive(Error, Debug)]
#[error("Error parsing at {line}:{col} :: {error_kind:?}")]
struct ParserError {
    line: usize,
    col: usize,
    error_kind: ParserErrorKind,
}

#[derive(Error, Debug)]
enum LexerErrorKind {
    #[error("unexpected symbol {0}")]
    UnexpectedSymbol(char),
    #[error("expected a valid digit found '{0}' instead")]
    MalformedInteger(char),
}

#[derive(Error, Debug)]
#[error("Invalid syntax at {line}:{col} :: {error_kind:?}")]
struct LexerError {
    line: usize,
    col: usize,
    error_kind: LexerErrorKind,
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

#[derive(Debug, Clone, Copy)]
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

enum_with_names!(TokenKind {
    Immediate(u64),
    Register(Register),
    Label(String),
    Mnemonic(Mnemonic),
    Comma,
    Colon,
    Dollar,
    Pound
});

macro_rules! discriminate {
    ( $name:ident ) => {
        paste! {
            const [<$name:upper _T>]: TokenKind = TokenKind::$name;
            const [<$name:upper>] : &'static str = &[<$name:upper _T>].to_str();
        }
    };
    ( $name:ident, $value:expr ) => {
        paste! {
            const [<$name:upper _T>]: &'static TokenKind = &TokenKind::$name($value);
            const [<$name:upper>] : &'static str = &[<$name:upper _T>].to_str();
        }
    }
}

discriminate!(Immediate, 0);
discriminate!(Label, String::new());
discriminate!(Register, Register::R1);
discriminate!(Mnemonic, Mnemonic::Add);
discriminate!(Comma);
discriminate!(Colon);
discriminate!(Dollar);
discriminate!(Pound);


// Words are serialized as a little-endian sequence of bytes
fn serialize_word(word: &u64) -> [u8; 8] {
    let mut bytes = [0; 8];
    bytes
        .iter_mut()
        .enumerate()
        .for_each(|(i, b)| *b = ((*word >> (i * 8)) & 255) as u8);
    bytes
}

fn serialize_half_word(half_word: u32) -> [u8; 4] {
    let mut bytes = [0; 4];
    bytes
        .iter_mut()
        .enumerate()
        .for_each(|(i, b)| *b = ((half_word >> (i * 8)) & 255) as u8);
    bytes
}

fn serialize_u16(arg: u16) -> [u8; 2] {
    let mut bytes = [0; 2];
    bytes
        .iter_mut()
        .enumerate()
        .for_each(|(i, b)| *b = ((arg >> (i * 8)) & 255) as u8);
    bytes
}

fn scan_number(lexeme: &str) -> Result<u64, usize> {
    if let Some(hex) = lexeme.strip_prefix("0x") {
        let mut i = hex.chars().enumerate();
        loop {
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
        loop {
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
        loop {
            if let Some((pos, c)) = i.next() {
                if !c.is_numeric() {
                    break Err(pos);
                }
            } else {
                break Ok(());
            }
        }?;
        Ok(lexeme.parse::<u64>().unwrap())
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
    if end < start {
        Ok(None)
    } else {
        let lexeme = &asm[*start..=*end];
        *start = *end;
        println!("{_col}, {lexeme}");
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
                    error_kind: LexerErrorKind::MalformedInteger(lexeme.as_bytes()[err] as char),
                })
        } else {
            Ok(if let Some(reg) = scan_register(lexeme) {
                Some(Token {
                    line,
                    col,
                    token_kind: TokenKind::Register(reg),
                })
            } else if let Some(mnemonic) = Mnemonic::try_from_str(lexeme) {
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
    let mut i = asm.chars().enumerate();
    let (mut start, mut end) = (0usize, 0usize);
    let (mut line, mut col) = (1usize, 1usize);
    'outer: while let Some((idx, c)) = i.next() {
        if c.is_whitespace() {
            if start != idx
                && let Some(token) = make_token(asm, &mut start, &mut end, line, col)?
            {
                token_stream.push(token);
            }
            if c == '\n' {
                line += 1;
                col = 0;
            }
            start = idx + 1;
            end = idx;
        } else if c == ';' {
            if let Some(token) = make_token(asm, &mut start, &mut end, line, col)? {
                token_stream.push(token);
            }
            for (idx, c) in i.by_ref() {
                if c == '\n' {
                    line += 1;
                    col = 1;
                    start = idx + 1;
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
            start = idx + 1;
            end = idx;
        } else if c == ':' {
            if let Some(token) = make_token(asm, &mut start, &mut end, line, col)? {
                token_stream.push(token);
            }
            token_stream.push(Token {
                line,
                col,
                token_kind: TokenKind::Colon,
            });
            start = idx + 1;
            end = idx;
        } else if c == '$' {
            token_stream.push(Token {
                line,
                col,
                token_kind: TokenKind::Dollar,
            });
            start = idx + 1;
            end = idx;
        } else if c == '#' {
            token_stream.push(Token {
                line,
                col,
                token_kind: TokenKind::Pound,
            });
            start = idx + 1;
            end = idx;
        } else if c.is_alphanumeric() {
            end = idx;
        } else {
            return Err(LexerError {
                line,
                col,
                error_kind: LexerErrorKind::UnexpectedSymbol(c),
            });
        }
        col += 1;
    }
    if let Some(tok) = make_token(asm, &mut start, &mut end, line, col)? {
        token_stream.push(tok);
    }
    Ok(token_stream)
}

fn reg_to_binary(reg: Register) -> u8 {
    match reg {
        Register::R1 => 0,
        Register::R2 => 1,
        Register::R3 => 2,
        Register::R4 => 3,
        Register::R5 => 4,
        Register::R6 => 5,
        Register::R7 => 6,
        Register::R8 => 7,
        Register::R9 => 8,
        Register::R10 => 9,
        Register::R11 => 10,
        Register::R12 => 11,
        Register::R13 => 12,
        Register::R14 => 13,
        Register::R15 => 14,
        Register::R16 => 15,
        Register::R17 => 16,
        Register::R18 => 17,
        Register::R19 => 18,
        Register::R20 => 19,
        Register::R21 => 20,
        Register::R22 => 21,
        Register::R23 => 22,
        Register::R24 => 23,
        Register::R25 => 24,
        Register::R26 => 25,
        Register::R27 => 26,
        Register::R28 => 27,
        Register::R29 => 28,
    }
}

// Replace with a better name dumbass
enum Serialized {
    Empty,
    Pound,
    Comma,
    Dollar,
    Colon,
    Register(u8),
    Immediate([u8; 8]),
}

fn expect_token<I>(
    iter: &mut I,
    expected: &[&'static str],
    sym_table: &HashMap<String, u64>,
) -> Result<Serialized, ParserError>
where
    I: Iterator<Item = Token>,
{
    if let Some(tok) = iter.next() {
        if expected.iter().any(|d| *d == tok.token_kind.to_str()) {
            Ok(match tok.token_kind {
                TokenKind::Immediate(val) => Serialized::Immediate(serialize_word(&val)),
                TokenKind::Register(r) => Serialized::Register(reg_to_binary(r)),
                TokenKind::Comma => Serialized::Comma,
                TokenKind::Colon => Serialized::Colon,
                TokenKind::Pound => Serialized::Pound,
                TokenKind::Dollar => Serialized::Dollar,
                TokenKind::Label(label) => {
                    sym_table.get(&label).map_or(Serialized::Empty, |word| {
                        Serialized::Immediate(serialize_word(word))
                    })
                }
                TokenKind::Mnemonic(_) => unreachable!("shouldn't have to decode mnemonics here!"),
            })
        } else {
            Err(ParserError {
                line: tok.line,
                col: tok.col,
                error_kind: ParserErrorKind::UnexpectedToken(
                    tok.token_kind.to_owned(),
                    Vec::from(expected),
                ),
            })
        }
    } else {
        Err(ParserError {
            line: 0,
            col: 0,
            error_kind: ParserErrorKind::UnexpectedEof,
        })
    }
}

fn parse_instruction<I>(
    mnemonic: Mnemonic,
    iter: &mut I,
    bytes: &mut Vec<u8>,
    sym_table: &HashMap<String, u64>,
) -> Result<(), ParserError>
where
    I: Iterator<Item = Token>,
{
    use Mnemonic::*;
    let mut instruction_half_word = mnemonic.serialiaze();
    match mnemonic {
        Add | Sub | Mul | Xor | Or | Load | Store | Div | And | Cmp => {
            // set op1 mode to 1 (register)
            instruction_half_word |= 1 << 9;
            // get the first operand
            match expect_token(
                iter,
                &[REGISTER],
                sym_table,
            )? {
                Serialized::Register(r) => {
                    // leave the first 13 bits untouched and set op1 at the 13-18th bits
                    instruction_half_word |= (r as u32) << 13;
                }
                _ => unreachable!("expected a register!"),
            };
            // consume the mandatory comma seperating the operands
            expect_token(iter, &[COMMA], sym_table)?;
            // get the second operand
            match expect_token(
                iter,
                &[
                    REGISTER,
                    POUND,
                    DOLLAR
                ],
                sym_table,
            )? {
                Serialized::Register(r) => {
                    // set op2 mode to 1 (register)
                    instruction_half_word |= 1 << 11;
                    // leave the first 18 bits alone and set op2 at the 18-23th bits
                    instruction_half_word |= (r as u32) << 18;
                    // the entire instruction (incl. both operands) fits nicely in the first 24 bits
                    // (the last bit is a pad) of a u32 so we serialize it and write the last
                    // 3 bytes (cause little endian,
                    // meaning the first byte is gonna be all zeroes)
                    bytes.extend_from_slice(&serialize_half_word(instruction_half_word)[1..]);
                }
                Serialized::Pound => {
                    // set op2 mode to 2 (register indirect)
                    instruction_half_word |= 2 << 11;
                    // get second operand
                    match expect_token(
                        iter,
                        &[REGISTER],
                        sym_table,
                    )? {
                        Serialized::Register(r) => {
                            // leave the first 18 bits alone and set op2 at the 18-23th bits
                            instruction_half_word |= (r as u32) << 18;
                            // the entire instruction (incl. both operands) fit nicely in the first 24 bits
                            // of a u32 so we serialize it and write the last 3 bytes (cause little endian,
                            // meaning the first byte is gonna be all zeroes)
                            bytes.extend_from_slice(
                                &serialize_half_word(instruction_half_word)[1..],
                            );
                        }
                        _ => unreachable!("expected a register!"),
                    }
                }
                Serialized::Dollar => {
                    // set op2 mode to 3 (immediate)
                    instruction_half_word |= 3 << 11;
                    // get second operand
                    match expect_token(
                        iter,
                        &[IMMEDIATE],
                        sym_table,
                    )? {
                        Serialized::Immediate(arg) => {
                            // we can't fit the second instruction in a u32 so we pad the 5
                            // remaining bits (18 to 24) with 0 (already 0 so do nothing),
                            // then push the last 3 bytes (again, cause little endian)
                            // of the serialized u32
                            bytes.extend_from_slice(
                                &serialize_half_word(instruction_half_word)[1..],
                            );
                            // then we serialize the 64 bit word into a sequence of bytes
                            // (TODO:
                            // an immediate value doesn't necessarily mean its a 64-bit word
                            // so we should perhaps add a way of distinguishing different width
                            // arguments thus spacing space)
                            bytes.extend_from_slice(&arg);
                        }
                        _ => unreachable!("expected a sequence of bytes!"),
                    }
                }
                _ => unreachable!("expected one of (register, pound sign, dollar sign)!"),
            }
        }
        Jmp | Jnz | Jz | Not | Call => {
            // these instructions only have one argument
            // get the first argument
            match expect_token(
                iter,
                &[
                    REGISTER,
                    POUND,
                    DOLLAR
                ],
                sym_table,
            )? {
                Serialized::Register(r) => {
                    // set op1 mode to 1 (register)
                    instruction_half_word |= 1 << 9;
                    // since these instructions don't have a second argument,
                    // we can write the register into the 11th-16th bits of the u32 (then cast to
                    // u16 cause we only need 16 bits here)
                    instruction_half_word |= (r as u32) << 11;
                    // the entire instruction (incl. both operands) fits nicely into a u16 so we
                    // serialize and write the bytes out
                    bytes.extend_from_slice(&serialize_u16(instruction_half_word as u16));
                }
                Serialized::Pound => {
                    // set op1 mode to 2 (register indirect)
                    instruction_half_word |= 2 << 9;
                    // get second operand
                    match expect_token(
                        iter,
                        &[REGISTER],
                        sym_table,
                    )? {
                        Serialized::Register(r) => {
                            // since these instructions don't have a second argument,
                            // we can write the register into the 11th-16th bits of the u32 (then cast to
                            // u16 cause we only need 16 bits here)
                            instruction_half_word |= (r as u32) << 11;
                            // the entire instruction (incl. both operands) fits nicely into a u16 so we
                            // serialize and write the bytes out
                            bytes.extend_from_slice(&serialize_u16(instruction_half_word as u16));
                        }
                        _ => unreachable!("expected a register!"),
                    }
                }
                Serialized::Dollar => {
                    // set op1 mode to 3 (immediate)
                    instruction_half_word |= 3 << 9;
                    // get actual operand
                    match expect_token(
                        iter,
                        &[IMMEDIATE],
                        sym_table,
                    )? {
                        Serialized::Immediate(arg) => {
                            // the operand is a u64 so we push the first 16 bits (9 for the ins, 2
                            // for the operand mode and the remaining 5 bits as a pad)
                            bytes.extend_from_slice(&serialize_u16(instruction_half_word as u16));
                            // then we serialize the 64 bit word into a sequence of bytes
                            // (TODO:
                            // an immediate value doesn't necessarily mean its a 64-bit word
                            // so we should perhaps add a way of distinguishing different width
                            // arguments thus spacing space)
                            bytes.extend_from_slice(&arg);
                        }
                        _ => unreachable!("expected a sequence of bytes!"),
                    }
                }
                _ => unreachable!("expected one of (register, pound sign, dollar sign)!"),
            }
        }
        Exit | Nop | Ret => {
            // these instructions take no operands so we write out the first 16 bits (9 for the
            // ins and the remaining 7 as a pad)
            bytes.extend_from_slice(&serialize_u16(instruction_half_word as u16));
        }
    }
    Ok(())
}

fn parse_assembly(asm: &str) -> Result<Vec<u8>, ParserError> {
    let mut bytes = Vec::new();
    let mut sym_table = HashMap::<String, u64>::new();
    let tokens = tokenise(asm)?;
    let mut token_iter = tokens.into_iter();
    while let Some(Token {
        line,
        col,
        token_kind,
    }) = token_iter.next()
    {
        match token_kind {
            TokenKind::Label(label) => {
                expect_token(
                    &mut token_iter,
                    &[COLON],
                    &sym_table,
                )
                .map(|_| {
                    sym_table.insert(label, bytes.len() as u64);
                })?;
            }
            TokenKind::Mnemonic(mnemonic) => {
                parse_instruction(mnemonic, &mut token_iter, &mut bytes, &sym_table)?;
            }
            _ => {
                return Err(ParserError {
                    line,
                    col,
                    error_kind: ParserErrorKind::UnexpectedToken(
                        token_kind,
                        vec![
                            LABEL,
                            MNEMONIC
                        ],
                    ),
                });
            }
        }
    }
    Ok(bytes)
}

#[test]
fn test_lexer() -> Result<(), LexerError> {
    const TEST: &'static str = r#"; program start
start:
    load r1, $10 ; load the decimal value 10 into r1
    load r2, r1  ; load the value from r1 into r2
    add r2, r1   ; add r1 and r2 and store the result in r2
    exit
r:
    nop
    add r30, #r1
    ret
"#;
    tokenise(TEST).map(|tokens| {
        for token in tokens {
            dbg!(token);
        }
    })
}

fn main() -> std::io::Result<()> {
    for arg in env::args().skip(1) {
        let mut file = std::fs::File::open(&arg)?;
        let mut buf = String::new();
        file.read_to_string(&mut buf)?;
        match parse_assembly(&buf) {
            Ok(bytes) => {
                let mut outfile = std::fs::File::open(format!("{arg}.out"))?;
                outfile.write_all(bytes.as_slice())?;
            }
            Err(err) => eprintln!("{err}"),
        }
    }
    Ok(())
}
