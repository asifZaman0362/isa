pub mod error;
pub mod lexer;
use error::*;
use lexer::{
    COLON, DOLLAR, IMMEDIATE, LABEL, MNEMONIC, MnemonicT, POUND, REGISTER, RegisterT, Token,
    TokenKind, tokenise,
};
use std::collections::HashMap;

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
    Immediate(u32),
}

fn expect_token_serialized<I>(
    iter: &mut I,
    expected: &[&'static str],
    sym_table: &HashMap<&'static str, u64>,
) -> Result<Serialized, ParserError>
where
    I: Iterator<Item = Token>,
{
    Ok(match expect_token(iter, expected, sym_table)?.token_kind {
        TokenKind::Immediate(val) => Serialized::Immediate(val),
        TokenKind::Register(r) => Serialized::Register(reg_to_binary(r)),
        TokenKind::Comma => Serialized::Comma,
        TokenKind::Colon => Serialized::Colon,
        TokenKind::Pound => Serialized::Pound,
        TokenKind::Dollar => Serialized::Dollar,
        TokenKind::Label(label) => sym_table.get(&label).map_or(Serialized::Empty, |word| {
            todo!("implement");
        }),
        TokenKind::Mnemonic(_) => unreachable!("shouldn't have to decode mnemonics here!"),
    })
}

fn expect_token<I>(
    iter: &mut I,
    expected: &[&'static str],
    sym_table: &HashMap<&'static str, u64>,
) -> Result<Token, ParserError>
where
    I: Iterator<Item = Token>,
{
    if let Some(tok) = iter.next() {
        if expected.iter().any(|d| *d == tok.token_kind.to_str()) {
            Ok(tok)
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

const INSTRUCTION_TYPE_SIZE: usize = 3;
const NUM_REG: usize = 5;

fn parse_alu_instruction<I>(
    mnemonic: MnemonicT,
    iter: &mut I,
    sym_table: &HashMap<&'static str, u64>,
) -> Result<u32, ParserError>
where
    I: Iterator<Item = Token>,
{
    use lexer::MnemonicT::*;
    const ALU_INSTRUCTION_TYPE: u32 = 1;
    const ALU_INSTRUCTION_TYPE_SIZE: usize = 4;
    const INPUT_MODE_SIZE: usize = 1;
    let mut shift_size: usize = 32 - INSTRUCTION_TYPE_SIZE;
    let mut instruction = ALU_INSTRUCTION_TYPE << shift_size;
    shift_size -= ALU_INSTRUCTION_TYPE_SIZE;
    let dest = match expect_token_serialized(iter, &[REGISTER], sym_table)? {
        Serialized::Register(r) => r,
        _ => unreachable!(),
    };
    instruction |= mnemonic.serialiaze() << shift_size;
    shift_size -= NUM_REG;
    instruction |= (dest as u32) << shift_size;
    if mnemonic != Not {
        shift_size -= NUM_REG;
        match expect_token_serialized(iter, &[REGISTER], sym_table)? {
            Serialized::Register(r) => {
                instruction |= (r as u32) << shift_size;
            }
            _ => unreachable!(),
        };
        shift_size -= INPUT_MODE_SIZE;
        let next = expect_token(iter, &[REGISTER, DOLLAR], sym_table)?;
        match next.token_kind {
            TokenKind::Register(r) => {
                instruction |= 0; // input mode = register
                let r = reg_to_binary(r);
                shift_size -= NUM_REG;
                instruction |= (r as u32) << shift_size;
            }
            TokenKind::Dollar => {
                instruction |= 1; // input mode = immediate
                let next = expect_token(iter, &[IMMEDIATE], sym_table)?;
                match next.token_kind {
                    TokenKind::Immediate(i) => {
                        if i >= (1 << shift_size) {
                            return Err(ParserError {
                                line: next.line,
                                col: next.col,
                                error_kind: ParserErrorKind::OutOfRange(0, (1 << shift_size) - 1),
                            });
                        }
                        instruction |= i;
                    }
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
    } else {
        shift_size -= INPUT_MODE_SIZE;
        let next = expect_token(iter, &[REGISTER, DOLLAR], sym_table)?;
        match next.token_kind {
            TokenKind::Register(r) => {
                let r = reg_to_binary(r);
                shift_size -= NUM_REG;
                instruction |= (r as u32) << shift_size;
            }
            TokenKind::Dollar => {
                instruction |= 1; // input mode = immediate
                let next = expect_token(iter, &[IMMEDIATE], sym_table)?;
                match next.token_kind {
                    TokenKind::Immediate(i) => {
                        if i >= (1 << shift_size) {
                            return Err(ParserError {
                                line: next.line,
                                col: next.col,
                                error_kind: ParserErrorKind::OutOfRange(0, (1 << shift_size) - 1),
                            });
                        }
                        instruction |= i;
                    }
                    _ => unreachable!(),
                }
            }
            _ => unreachable!(),
        }
    }
    Ok(instruction)
}

fn parse_load_store<I>(
    mnemonic: MnemonicT,
    iter: &mut I,
    sym_table: &HashMap<&'static str, u64>,
) -> Result<u32, ParserError>
where
    I: Iterator<Item = Token>,
{
    const LOAD_STORE_INSTRUCTION_TYPE: u32 = 2;
    const LOAD_STORE_INSTRUCTION_TYPE_SIZE: usize = 1;
    let mut shift_size = 32 - INSTRUCTION_TYPE_SIZE;
    let mut instruction = LOAD_STORE_INSTRUCTION_TYPE << shift_size;
    shift_size -= LOAD_STORE_INSTRUCTION_TYPE_SIZE;
    let dest = match expect_token_serialized(iter, &[REGISTER], sym_table)? {
        Serialized::Register(r) => r,
        _ => unreachable!(),
    };
    instruction |= mnemonic.serialiaze() << shift_size;
    shift_size -= NUM_REG;
    instruction |= (dest as u32) << shift_size;
    const ADDR_MODE_SIZE: u32 = 4;
    // indirect
    // indexed
    //
}

fn parse_instruction<I>(
    mnemonic: MnemonicT,
    iter: &mut I,
    sym_table: &HashMap<&'static str, u64>,
) -> Result<u32, ParserError>
where
    I: Iterator<Item = Token>,
{
    use lexer::MnemonicT::*;
    let mut instruction_half_word = mnemonic.serialiaze();
    match mnemonic {
        Load | Store => match expect_token_serialized(iter, &[REGISTER], sym_table)? {
            Serialized::Register(r) => {
                instruction_half_word |= (r as u32) << 13;
            }
            _ => unreachable!(
                "shouldn't see anything other than a register at this point! bug in the expect_token fn?"
            ),
        },
        Add | Sub | Mul | Xor | Or | Div | And | Cmp | Not | AddS | SubS | OrS => {
            return parse_alu_instruction(mnemonic, iter, sym_table);
        }
        Jmp | Jnz | Jz | Call => {
            // these instructions only have one argument
            // get the first argument
            match expect_token_serialized(iter, &[REGISTER, POUND, DOLLAR], sym_table)? {
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
                    match expect_token_serialized(iter, &[REGISTER], sym_table)? {
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
                    match expect_token_serialized(iter, &[IMMEDIATE], sym_table)? {
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

pub fn parse_assembly(asm: &str) -> Result<Vec<u8>, ParserError> {
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
                expect_token_serialized(&mut token_iter, &[COLON], &sym_table).map(|_| {
                    sym_table.insert(label, bytes.len() as u64);
                })?;
            }
            TokenKind::Mnemonic(mnemonic) => {
                bytes.extend_from_slice(&serialize_half_word(parse_instruction(
                    mnemonic,
                    &mut token_iter,
                    &sym_table,
                )?));
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
