const MEM_SIZE: usize = 65_536;

pub struct Memory {
    data: [u8; MEM_SIZE],
}

pub struct Cpu {
    registers: [u64; 32],
    instruction_register: u64,
    stack_pointer: u64,
    program_counter: u64,
    status: u8,
}

use super::{RegisterT, RuntimeError};

enum Addr {
    Immediate(usize),
    Register(u8),
}

pub fn load(addr: Addr, mem: &mut Memory, cpu: &mut Cpu, dest: u8) -> Result<(), RuntimeError> {
    match addr {
        Addr::Immediate(addr) => {}
        Addr::Register(r) => {
            cpu.instruction_register = cpu.registers[r as usize];
            cpu.registers[dest as usize] = mem.data[cpu.instruction_register as usize];
        }
    }
    Ok(())
}
