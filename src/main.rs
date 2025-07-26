use std::collections::HashMap;
use std::env;
use std::io::{Read, Write};

use paste::paste;
use thiserror::Error;

mod instructions;
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
        pub enum MnemonicT {
            $( $name ),*
        }

        impl MnemonicT {
            pub fn try_from_str(s: &str) -> Option<Self> {
                match convert_case(s).as_str() {
                    $( stringify!($name) => Some(MnemonicT::$name), )*
                    _ => None
                }
            }

            pub fn as_str(&self) -> &'static str {
                match self {
                    $( MnemonicT::$name => stringify!($name), )*
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

impl MnemonicT {
    fn serialiaze(&self) -> u32 {
        use MnemonicT::*;
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
        #[derive(Debug, Clone, PartialEq)]
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

#[derive(Debug, Clone, Copy, PartialEq)]
enum RegisterT {
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
    R30,
    R31,
    R32,
}

type StaticStr = &'static str;

enum_with_names!(TokenKind {
    Immediate(u64),
    Register(RegisterT),
    Label(StaticStr),
    Mnemonic(MnemonicT),
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
    };
}

discriminate!(Immediate, 0);
discriminate!(Label, "");
discriminate!(Register, RegisterT::R1);
discriminate!(Mnemonic, MnemonicT::Add);
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

fn scan_register(lexeme: &str) -> Option<RegisterT> {
    if let Some(r_no) = lexeme.strip_prefix("r") {
        if let Ok(r_no) = r_no.parse::<u8>() {
            match r_no {
                1 => Some(RegisterT::R1),
                2 => Some(RegisterT::R2),
                3 => Some(RegisterT::R3),
                4 => Some(RegisterT::R4),
                5 => Some(RegisterT::R5),
                6 => Some(RegisterT::R6),
                7 => Some(RegisterT::R7),
                8 => Some(RegisterT::R8),
                9 => Some(RegisterT::R9),
                10 => Some(RegisterT::R10),
                11 => Some(RegisterT::R11),
                12 => Some(RegisterT::R12),
                13 => Some(RegisterT::R13),
                14 => Some(RegisterT::R14),
                15 => Some(RegisterT::R15),
                16 => Some(RegisterT::R16),
                17 => Some(RegisterT::R17),
                18 => Some(RegisterT::R18),
                19 => Some(RegisterT::R19),
                20 => Some(RegisterT::R20),
                21 => Some(RegisterT::R21),
                22 => Some(RegisterT::R22),
                23 => Some(RegisterT::R23),
                24 => Some(RegisterT::R24),
                25 => Some(RegisterT::R25),
                26 => Some(RegisterT::R26),
                27 => Some(RegisterT::R27),
                28 => Some(RegisterT::R28),
                29 => Some(RegisterT::R29),
                30 => Some(RegisterT::R30),
                31 => Some(RegisterT::R31),
                32 => Some(RegisterT::R32),
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
        let col = _col - lexeme.len();
        if lexeme.starts_with("0x")
            || lexeme.starts_with("0b")
            || lexeme.starts_with(|c: char| c.is_ascii_digit())
        {
            scan_number(lexeme)
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
            } else if let Some(mnemonic) = MnemonicT::try_from_str(lexeme) {
                Some(Token {
                    line,
                    col,
                    token_kind: TokenKind::Mnemonic(mnemonic),
                })
            } else {
                Some(Token {
                    line,
                    col,
                    token_kind: TokenKind::Label(lexeme.to_owned().leak()),
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
            if start != idx
                && let Some(token) = make_token(asm, &mut start, &mut end, line, col)?
            {
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

fn reg_to_binary(reg: RegisterT) -> u8 {
    match reg {
        RegisterT::R1 => 0,
        RegisterT::R2 => 1,
        RegisterT::R3 => 2,
        RegisterT::R4 => 3,
        RegisterT::R5 => 4,
        RegisterT::R6 => 5,
        RegisterT::R7 => 6,
        RegisterT::R8 => 7,
        RegisterT::R9 => 8,
        RegisterT::R10 => 9,
        RegisterT::R11 => 10,
        RegisterT::R12 => 11,
        RegisterT::R13 => 12,
        RegisterT::R14 => 13,
        RegisterT::R15 => 14,
        RegisterT::R16 => 15,
        RegisterT::R17 => 16,
        RegisterT::R18 => 17,
        RegisterT::R19 => 18,
        RegisterT::R20 => 19,
        RegisterT::R21 => 20,
        RegisterT::R22 => 21,
        RegisterT::R23 => 22,
        RegisterT::R24 => 23,
        RegisterT::R25 => 24,
        RegisterT::R26 => 25,
        RegisterT::R27 => 26,
        RegisterT::R28 => 27,
        RegisterT::R29 => 28,
        RegisterT::R30 => 29,
        RegisterT::R31 => 30,
        RegisterT::R32 => 31,
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
    sym_table: &HashMap<&'static str, u64>,
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
    mnemonic: MnemonicT,
    iter: &mut I,
    bytes: &mut Vec<u8>,
    sym_table: &HashMap<&'static str, u64>,
) -> Result<(), ParserError>
where
    I: Iterator<Item = Token>,
{
    use MnemonicT::*;
    let mut instruction_half_word = mnemonic.serialiaze();
    match mnemonic {
        Add | Sub | Mul | Xor | Or | Load | Store | Div | And | Cmp => {
            // set op1 mode to 0 (register)
            // instruction_half_word |= 0 << 9;
            // get the first operand
            match expect_token(iter, &[REGISTER], sym_table)? {
                Serialized::Register(r) => {
                    // leave the first 13 bits untouched and set op1 at the 13-18th bits
                    println!("register {r}");
                    instruction_half_word |= (r as u32) << 13;
                }
                _ => unreachable!("expected a register!"),
            };
            // consume the mandatory comma seperating the operands
            expect_token(iter, &[COMMA], sym_table)?;
            // get the second operand
            match expect_token(iter, &[REGISTER, POUND, DOLLAR], sym_table)? {
                Serialized::Register(r) => {
                    // set op2 mode to 0 (register)
                    // instruction_half_word |= 0 << 11;
                    // leave the first 18 bits alone and set op2 at the 18-23th bits
                    instruction_half_word |= (r as u32) << 18;
                    // the entire instruction (incl. both operands) fits nicely in the first 24 bits
                    // (the last bit is a pad) of a u32 so we serialize it and write the last
                    // 3 bytes (cause little endian,
                    // meaning the first byte is gonna be all zeroes)
                    bytes.extend_from_slice(&serialize_half_word(instruction_half_word)[..3]);
                }
                Serialized::Pound => {
                    // set op2 mode to 1 (register indirect)
                    instruction_half_word |= 1 << 11;
                    // get second operand
                    match expect_token(iter, &[REGISTER], sym_table)? {
                        Serialized::Register(r) => {
                            // leave the first 18 bits alone and set op2 at the 18-23th bits
                            instruction_half_word |= (r as u32) << 18;
                            // the entire instruction (incl. both operands) fit nicely in the first 24 bits
                            // of a u32 so we serialize it and write the last 3 bytes (cause little endian,
                            // meaning the first byte is gonna be all zeroes)
                            bytes.extend_from_slice(
                                &serialize_half_word(instruction_half_word)[..3],
                            );
                        }
                        _ => unreachable!("expected a register!"),
                    }
                }
                Serialized::Dollar => {
                    // set op2 mode to 2 (immediate)
                    instruction_half_word |= 2 << 11;
                    // get second operand
                    match expect_token(iter, &[IMMEDIATE], sym_table)? {
                        Serialized::Immediate(arg) => {
                            // we can't fit the second instruction in a u32 so we pad the 5
                            // remaining bits (18 to 24) with 0 (already 0 so do nothing),
                            // then push the last 3 bytes (again, cause little endian)
                            // of the serialized u32
                            bytes.extend_from_slice(
                                &serialize_half_word(instruction_half_word)[..3],
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
            match expect_token(iter, &[REGISTER, POUND, DOLLAR], sym_table)? {
                Serialized::Register(r) => {
                    // set op1 mode to 0 (register)
                    instruction_half_word |= 0 << 9;
                    // since these instructions don't have a second argument,
                    // we can write the register into the 11th-16th bits of the u32 (then cast to
                    // u16 cause we only need 16 bits here)
                    instruction_half_word |= (r as u32) << 11;
                    // the entire instruction (incl. both operands) fits nicely into a u16 so we
                    // serialize and write the bytes out
                    bytes.extend_from_slice(&serialize_u16(instruction_half_word as u16));
                }
                Serialized::Pound => {
                    // set op1 mode to 1 (register indirect)
                    instruction_half_word |= 1 << 9;
                    // get second operand
                    match expect_token(iter, &[REGISTER], sym_table)? {
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
                    // set op1 mode to 2 (immediate)
                    instruction_half_word |= 2 << 9;
                    // get actual operand
                    match expect_token(iter, &[IMMEDIATE], sym_table)? {
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
    let mut sym_table = HashMap::<&'static str, u64>::new();
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
                expect_token(&mut token_iter, &[COLON], &sym_table).map(|_| {
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
                    error_kind: ParserErrorKind::UnexpectedToken(token_kind, vec![LABEL, MNEMONIC]),
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
    load r1, $0x10 ; load the decimal value 10 into r1
    load r2, $0b1010  ; load the value from r1 into r2
    add r2, r1   ; add r1 and r2 and store the result in r2
    exit
r:
    nop
    add r30, #r1
    ret
"#;
    use MnemonicT::*;
    use RegisterT::*;
    use TokenKind::*;
    assert_eq!(
        tokenise(TEST)?
            .iter()
            .map(|t| t.token_kind.clone())
            .collect::<Vec<_>>(),
        [
            Label("start"),
            Colon,
            Mnemonic(Load),
            Register(R1),
            Comma,
            Dollar,
            Immediate(0x10),
            Mnemonic(Load),
            Register(R2),
            Comma,
            Dollar,
            Immediate(0b1010),
            Mnemonic(Add),
            Register(R2),
            Comma,
            Register(R1),
            Mnemonic(Exit),
            Label("r"),
            Colon,
            Mnemonic(Nop),
            Mnemonic(Add),
            Label("r30"),
            Comma,
            Pound,
            Register(R1),
            Mnemonic(Ret)
        ]
    );
    Ok(())
}

#[test]
fn test_parser() -> Result<(), ParserError> {
    const ASM: &'static str = r#"
        add r1, #r2
        sub r3, $0x2010
        "#;
    assert_eq!(
        parse_assembly(ASM)?,
        [7, 8, 4, 8, 0x50, 0, 0x10, 0x20, 0, 0, 0, 0, 0, 0],
    );
    Ok(())
}

#[derive(Error, Debug)]
enum RuntimeError {
    #[error("segmentation fault")]
    Segfault,
    #[error(transparent)]
    ParserError(#[from] ParserError),
}

#[test]
fn test_execution() -> Result<(), RuntimeError> {
    const ASM: &'static str = r#"
    loop:
    add r1, $0x01
    cmp r1, $0x10
    jnz loop
    store r1, $0x2020
    hlt
    "#;
    Ok(())
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
