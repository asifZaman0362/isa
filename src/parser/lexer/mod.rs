pub mod error;
use crate::{define_mnemonics, discriminate, enum_with_names};
use error::{LexerError, LexerErrorKind};
use paste::paste;

#[derive(Debug)]
pub struct Token {
    pub line: usize,
    pub col: usize,
    pub token_kind: TokenKind,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum RegisterT {
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

pub type StaticStr = &'static str;

define_mnemonics!(
    Add, Sub, Mul, Div, AddS, SubS, Xor, Or, And, Cmp, OrS, Jz, Jmp, Jnz, Load, Not, Store, Exit,
    Nop, Ret, Call
);

enum_with_names!(TokenKind {
    Immediate(u32),
    Register(RegisterT),
    Label(StaticStr),
    Mnemonic(MnemonicT),
    Comma,
    Colon,
    Dollar,
    Pound
});

discriminate!(Immediate, 0);
discriminate!(Label, "");
discriminate!(Register, RegisterT::R1);
discriminate!(Mnemonic, MnemonicT::Add);
discriminate!(Comma);
discriminate!(Colon);
discriminate!(Dollar);
discriminate!(Pound);

impl MnemonicT {
    pub fn serialiaze(&self) -> u32 {
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

            // Arithmetic and Logic
            Add => 0x0,
            Sub => 0x1,
            Mul => 0x2,
            Div => 0x3,
            AddS => 0x4,
            SubS => 0x5,
            And => 0x6,
            Or => 0x7,
            Xor => 0x8,
            Cmp => 0x9,
            OrS => 0xa,
            Not => 0xb,

            // Memory
            Load => 0x0,
            Store => 0x1,
        }
    }
}

fn scan_number(lexeme: &str) -> Result<u32, usize> {
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
        Ok(u32::from_str_radix(hex, 16).unwrap())
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
        Ok(u32::from_str_radix(bin, 2).unwrap())
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
        Ok(lexeme.parse::<u32>().unwrap())
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

pub fn tokenise(asm: &str) -> Result<Vec<Token>, LexerError> {
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
