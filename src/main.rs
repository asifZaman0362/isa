use std::env;
use std::io::{Read, Write};

use thiserror::Error;

mod instructions;
mod macros;
mod parser;

use parser::{error::ParserError, parse_assembly};
/*
 *
 *  Custom assembly:
 *
 *  labels:
 *  value ::= register | $<hex,dec,bin> | #register
 *  add [destination] [register] [value]
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
