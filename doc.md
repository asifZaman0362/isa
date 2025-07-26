# Custom Assembly

## Terminology
### Data
1. byte: 8-bits of data
2. half-word: 16-bits of data
3. word: 32-bits of data
4. double-word: 64-bits of data

## Instruction Encoding

All instructions have a fixed 32-bit size
_________________________________________________________________________________________________________________________________
| 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10| 11| 12| 13| 14| 15| 16| 17| 18| 19| 20| 21| 22| 23| 24| 25| 26| 27| 28| 29| 30| 31| 32|
| Iclass|


## Instructions:

### Control
These instructions alter the overall flow of control of the program.

* #### `HLT`:
    Halts execution of the program
* #### `NOP`:
    

### Arithmetic and Logic (0):
These instructions perform arithmetic and logical operations on registers

##### Glossary:

* `<drx>`: Destination register. Must be a valid register name (all sizes allowed).

* `<irx>`: Input register. Must be a valid register name (all sizes allowed).

* `<val>`: Input that resolves to a numerical _value_. Could be a register (any size) or a constant.

The sizes of ALL operands must be the same! These instructions DO NOT implicitly extend or saturate values.

---

* #### `ADD <drx>, <irx>, <val>`:
    Adds the value at `<val>` with `<irx>` and stores the output in `<drx>`
* #### `SUB <drx>, <irx>, <val>`:
    Subtracts the value at `<val>` with `<irx>` and stores the output in `<drx>`
* #### `MUL <drx>, <irx>, <val>`:
    Multiplies the value at `<val>` with `<irx>` and stores the output in `<drx>`
* #### `DIV <drx>, <irx>, <val>`:
    Divides the value at `<val>` with `<irx>` and stores the output in `<drx>`.

    This instruction ignores decimals. See (#floating-point-instructions)[floating point instructions] for more info on how to work with decimals.
* #### `AND <drx>, <irx>, <val>`:
    Performs logical AND on between the value at `<val>` with `<irx>` and stores the output in `<drx>`
* #### `OR <drx>, <irx>, <val>`:
    Performs logical OR on between the value at `<val>` with `<irx>` and stores the output in `<drx>`
* #### `XOR <drx>, <irx>, <val>`:
    Performs logical XOR on between the value at `<val>` with `<irx>` and stores the output in `<drx>`
* #### `NOT <drx>, <val>`:
    Performs logical XOR on between the value at `<val>` and stores the output in `<drx>`


### Load And Store:
These instructions are the only instructions that can directly interact with memory (r/w).
* #### `LOAD <rx>, <addr>`:
    Loads a byte/half-word/word/double-word into a register from a given address.
    `rx`: The register to fetch the data into. The type of register used determines the amount of data fetched from memory, e.g-
    `r#` fetches a double-word, `w#` fetches a word, and so on...
* #### `STORE <rx>, <addr>`:
    Wrties the data from a register into memory at the given address.
    Similarly the `LOAD` instruction, the nature of the argument register determines the amount of data written into memory

