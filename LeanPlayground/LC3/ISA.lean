import LeanPlayground.LC3.Encodable

/-!
# ISA of LC-3 architecture

We define the ***ISA*** (*I*nstruction *S*et *A*rchitecture) of LC-3 architecture.
The original resource of the architecture is found in *Introduction to Computing Systems* by Yale Patt and Sanjay Patel.
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

namespace LC3

/-!
### The second operand of ALU

In the LC-3 architecture, every binary operation (i.e. *ADD*, *AND*, and *XOR* in ALU instruction can take a register and an immediate value as the second operand.
-/

/-- The second operand of binary operations (i.e. *ADD*, *AND*, and *XOR*) is either a register or an immediate value. -/
inductive RHSVal where
| reg : Fin 8 → RHSVal
| imm : Int → RHSVal
deriving DecidableEq, Repr

namespace RHSVal

open Encodable in
instance : Encodable RHSVal Int where
  encode x :=
    match x with
    | .reg i => encode (Sum.inl (β:=Int) i)
    | .imm n => encode (Sum.inr (α:=Fin 8) n)
  decode n :=
    match (decode n : Fin 8 ⊕ Int) with
    | .inl i => .reg i
    | .inr n => .imm n
  decode_encode x := by
    cases x with
    | reg i => simp only [decode_encode]
    | imm n => simp only [decode_encode]

end RHSVal


/-!
### Definition of ISA
-/

/--
The ISA (Instruction Set Architecture) of *LC-3* architecture.
It assumes the following registers in addition to the main registers:
- ***PC*** (*P*rogram *C*ounter) containing the address in the memory of the next instruction to be executed.
- ***PSR*** (*P*rocessor *S*tatus *R*egister) maintaining
  - `n`-flag stands for the last ALU / load operation results in negative;
  - `z`-flag stands for the last ALU / load operation results in zero;
  - `p`-flag stands for the last ALU / load operation results in positive;
  - the execution mode: either `.user` or `.privilege`;
  - the execution priority level.
- ***Saved_SP***
Two ranges in the main memory are used for *stacks*; one for the *User Stack* and the other for the *Supervisor Stack*.
The stack pointers for them are called ***USP*** (User Stack Pointer) and ***SSP*** (Supervisor Stack Pointer) respectively .
  - If `PSR.mode = .user`, then ***USP*** is maintained by one of the registers (e.g. the 6-th in the original LC-3) while ***SSP*** is stored in ***Saved_SP***.
  - If `PSR.mode = .privilege`, then the other way.
-/
inductive ISA where
/--
*Conditional Branch* instruction: `br n z p imm` is the conditional jump to `PC + imm` based on the `n`, `z`, and `p` flags.
It causes `PC ← PC + imm` in either of the following case:
- `n = true` and the `n`-flag is set;
- `z = true` and the `z`-flag is set;
- `p = true` and the `p`-flag is set.
-/
| br (n p z : Bool) (imm : Int) : ISA
/--
*Addition* instruction: `add dr sr1 rhs` causes `dr ← sr1 + rhs`, where `rhs` is either a register `RHSVal.reg sr2` or an immediate value `RHSVal.imm imm`.
The `n`-, `z`-, and `p`-flags should be set properly afterwards.
-/
| add (dr sr1 : Fin 8) (rhs : RHSVal) : ISA
/--
*Load* instruction: `ld dr imm` causes `dr ← mem[PC + imm]`.
If `PSR.mode = .user`, then the instruction gives rise to an ACV exception in the case `PC + imm` lies in the privileged range.
The `n`-, `z`-, and `p`-flags should be set properly afterwards.
-/
| ld (dr : Fin 8) (imm : Int) : ISA
/--
*Store* instruction: `st sr imm` causes `mem[PC + imm] ← sr`.
If `PSR.mode = .user`, then the instruction gives rise to an ACV exception in the case `PC + imm` lies in the privileged range.
-/
| st (sr : Fin 8) (imm : Int) : ISA
/--
*Jump to Subroutine* instruction: `jsr dr (.reg sr)` is equivalent to the following pseudo-code:
```
AUX ← PC;
PC ← sr;
dr ← AUX;
```
`jsr dr (.imm imm)` causes `dr ← PC; PC ← PC + imm`.

* Remark
In the original LC-3, the *JSR* instruction stands for `jsr 7 (.reg sr)` while *JSRR* for `jsr 7 (.imm imm)`.
For both instructions, one cannot specify the destination register since the 7-th register is distinguished to interact with `PC`.
See also the remark in `LC3.ISA.jmp`.
-/
| jsr (dr : Fin 8) : RHSVal → ISA
/--
*Bitwise Logical AND* instruction: `and dr sr1 rhs` causes `dr ← sr1 &&& rhs`, where `rhs` is either a register `RHSVal.reg sr2` or an immediate value `RHSVal.imm imm`.
The `n`-, `z`-, and `p`-flgas are set properly afterwards.
-/
| and (dr sr1 : Fin 8) (rhs : RHSVal) : ISA
/--
*Load Base+offset* instruction: `ldr dr sr imm` causes `dr ← mem[sr + imm]`.
If `PSR.mode = .user`, then the instruction gives rise to an ACV exception in the case `sr + imm` lies in the privileged range.
The `n`-, `z`-, and `p`-flags are set properly afterwards based on the loaded value.
-/
| ldr (dr sr : Fin 8) (imm : Int) : ISA
/--
*Store Base+offset* instruction: `str sr dr imm` causes `mem[dr + imm] ← sr`.
If `PSR.mode = .user`, then the instruction gives rise to an ACV exception in the case `dr + imm` lies in the privileged range.
-/
| str (sr dr : Fin 8) (imm : Int) : ISA
/--
*Return from Trap or Interrupt* instruction: `rti spr` is equivalent to the following pseudo-code:
```
if PSR.mode == .user then
  throw PRIVILEGE_MODE_EXCEPTION;

PC ← mem[spr];
spr ← spr + 1;
PSR ← mem[spr];
AUX ← spr + 1;
if PSR.mode == .user then
  spr ← Saved_SP;
  Saved_SP ← AUX;
else
  spr ← AUX;
```
The instruction assumes that the `spr` is the register containing the supervisor stack pointer with the following stack structure:
```
──────────────
|   . . .    |
──────────────
| Caller PC  | <- spr
──────────────
| Caller PSR |
──────────────
|   . . .    |
──────────────
| Stack Base |
──────────────
```
-/
| rti (spr : Fin 8) : ISA
/--
*Bitwise Logical XOR* instruction: `not dr sr1 rhs` causes `dr ← sr1 ^^^ rhs`, where `rhs` is either a register `RHSVal.reg sr2` or an immediate value `RHSVal.imm imm`.
The `n`-, `z`-, and `p`-flags are set property aftterwards.

* Remark
In the original LC-3 has *NOT* instruction instead of the XOR-operation.
In fact, one can think of it as `xor dr sr (.imm (-1))`.
-/
| xor (dr sr1 : Fin 8) (rhs : RHSVal) : ISA
/--
*Load Indirect* instruction: `ldi dr imm` causes `dr ← mem[mem[PC + imm]]`.
If `PSR.mode = .privilege`, then the instruction gives rise to an ACV exception in the case either of `PC + imm` or `mem[PC + imm]` lies in the privileged range.
The `n`-, `z`-, and `p`-flags should be set properly afterwards.
-/
| ldi (dr : Fin 8) (imm : Int) : ISA
/--
*Store Indirect* instruction: `sti sr imm` causes `mem[mem[PC + imm]] ← sr`.
If `PSR.mode = .privilege`, then the instruction gives rise to an ACV exception in the case either of `PC + imm` or `mem[PC + imm]` lies in the privileged range.
-/
| sti (sr : Fin 8) (imm : Int) : ISA
/--
*Jump* instruction: `jmp sr` causes `PC ← sr`.

* Remark
 In the original LC-3, `jmp 7` is especially denoted by *RET* and called *Return from Subroutine* instruction since the 7-th register is distinguished to interact with `PC`.
 See also the remark in `LC3.ISA.jsr`.
-/
| jmp (sr : Fin 8) : ISA
/--
The instruction for the *reserved* opcode (`0b1101`).
-/
| reserved (n : Int) : ISA
/--
*Load Effective Address* instruction: `lea dr imm` causes `dr ← PC + imm`.
-/
| lea (dr : Fin 8) (imm : Int) : ISA
/--
*System Call* instruction: `trap spr tv` is equivalent to the following pseudo-code:
```
AUX ← PSR;
if PSR.mode = .user
  swap (Saved_SP, spr);
  PSR.mode ← .privilege;
spr ← spr - 1;
mem[spr] ← AUX;
spr ← spr - 1;
mem[spr] ← PC;
PC ← mem[tv];
```
The memory range where `tv` can point to is called **Trap Vector Table**, and the actual execution codes stored there are implementation-defined.
-/
| trap (spr : Fin 8) (tv : Int) : ISA
deriving DecidableEq, Repr

namespace ISA

open Encodable in
instance : Encodable ISA Int where
  encode instr :=
    match instr with
    | br p z n imm => encode ((0x0 : Fin 16), (encode (p, z, n, imm) : Int))
    | add dr sr1 rhs => encode ((0x1 : Fin 16), (encode (dr, sr1, rhs) : Int))
    | ld dr imm => encode ((0x2 : Fin 16), (encode (dr, imm) : Int))
    | st sr imm => encode ((0x3 : Fin 16), (encode (sr, imm) : Int))
    | jsr dr rhs => encode ((0x4 : Fin 16), (encode (dr, rhs) : Int))
    | and dr sp1 rhs => encode ((0x5 : Fin 16), (encode (dr, sp1, rhs) : Int))
    | ldr dr sr imm => encode ((0x6 : Fin 16), (encode (dr, sr, imm) : Int))
    | str sr dr imm => encode ((0x7 : Fin 16), (encode (sr, dr, imm) : Int))
    | rti spr => encode ((0x8 : Fin 16), (encode spr : Int))
    | xor dr sr1 rhs => encode ((0x9 : Fin 16), (encode (dr, sr1, rhs) : Int))
    | ldi dr imm => encode ((0xA : Fin 16), (encode (dr, imm) : Int))
    | sti sr imm => encode ((0xB : Fin 16), (encode (sr, imm) : Int))
    | jmp sr => encode ((0xC : Fin 16), (encode sr : Int))
    | reserved n => encode ((0xD : Fin 16), (encode n : Int))
    | lea dr imm => encode ((0xE : Fin 16), (encode (dr, imm) : Int))
    | trap spr tv => encode ((0xF : Fin 16), (encode (spr, tv) : Int))
  decode n :=
    match decode (α:=Fin 16 × Int) n with
    | (0x0, n) => let (p,z,n,imm) := decode n; .br p z n imm
    | (0x1, n) => let (dr, sr1, rhs) := decode n; .add dr sr1 rhs
    | (0x2, n) => let (dr, imm) := decode n; .ld dr imm
    | (0x3, n) => let (sr, imm) := decode n; .st sr imm
    | (0x4, n) => let (dr, rhs) := decode n; .jsr dr rhs
    | (0x5, n) => let (dr, sr1, rhs) := decode n; .and dr sr1 rhs
    | (0x6, n) => let (dr, sr, imm) := decode n; .ldr dr sr imm
    | (0x7, n) => let (sr, dr, imm) := decode n; .str sr dr imm
    | (0x8, n) => .rti <| decode n
    | (0x9, n) => let (dr, s1, rhs) := decode n; .xor dr s1 rhs
    | (0xA, n) => let (dr, imm) := decode n; .ldi dr imm
    | (0xB, n) => let (sr, imm) := decode n; .sti sr imm
    | (0xC, n) => .jmp <| decode n
    | (0xD, n) => .reserved <| decode n
    | (0xE, n) => let (dr, imm) := decode n; .lea dr imm
    | (0xF, n) => let (spr,tv) := decode n; .trap spr tv
    | (⟨_+16, h⟩, _) =>
      have := Nat.lt_of_add_lt_add_right h
      nomatch this
  decode_encode instr := by
    cases instr <;> simp only [decode_encode]

/--
*DO NOTHING* instruction.
It is implemented as `br false false false 0`.
Note that encoding this instruction into `Int` results in `0`; see `LC3.ISA.encode_none`.
-/
def none : ISA :=
  .br false false false 0

open Encodable in
theorem encode_none : (encode ISA.none : Int) = 0 := by
  decide

/--
*Bitwise Complement* instruction: `not dr sr` causes `dr ← ~~~sr`.

* Remark
Although the original LC-3 ISA has *NOT* as its 16 instructions, our version define it as a special case *XOR* as `not dr sr := xor dr sr (.imm (-1))`.
-/
def not (dr sr : Fin 8) : ISA :=
  .xor dr sr (.imm (-1))

end ISA


end LC3
