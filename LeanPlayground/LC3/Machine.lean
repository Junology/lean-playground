import Std.Data.HashMap

import LeanPlayground.Data.Int.Bit
import LeanPlayground.LC3.Encodable
import LeanPlayground.LC3.ISA
import LeanPlayground.LC3.Memory

/-!
# A model of a machine for LC-3 ISA
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

namespace LC3

/-!
### Processor Status
-/

inductive ExecMode where
| user
| privilege
deriving DecidableEq, Repr

instance : Encodable ExecMode (Fin 2) where
  encode x := match x with | .user => 0 | .privilege => 1
  decode n := match n with | 0 => .user | 1 => .privilege
  decode_encode x := by cases x <;> rfl

structure ProcessorStatus where
  (n z p : Bool)
  (prio : Nat)
  (mode : ExecMode)
deriving DecidableEq, Repr

open Encodable in
instance : Encodable ProcessorStatus Int where
  encode ps :=
    encode (cond ps.n (1 : Fin 2) 0, cond ps.z (1 : Fin 2) 0, cond ps.p (1 : Fin 2) 0, (encode ps.mode : Fin 2), ps.prio)
  decode n :=
    let (n, z, p, mode, prio) : Fin 2 × Fin 2 × Fin 2 × Fin 2 × Nat :=
      decode n
    {
      n := n == 1
      z := z == 1
      p := p == 1
      mode := decode mode
      prio := prio
    }
  decode_encode ps := by
    simp only [decode_encode]
    rcases ps with ⟨n,z,p,prio,mode⟩
    cases n <;> cases z <;> cases p <;> rfl

/-!
### Definition of the machine
-/

structure Machine where
  /-- Processor Status Register -/
  psr : ProcessorStatus
  /-- Instruction Register -/
  ir : ISA
  /-- Program Counter -/
  pc : Address
  /-- Machine Address Register -/
  mar : Address
  /-- Machine Data Register -/
  mdr : Int
  /-- Registers -/
  reg : Array Int
  reg_size_eq : reg.size = 8
  /-- Saved Stack pointer register -/
  sspr : Address
  /-- Memory space -/
  mem : Memory
deriving Repr

namespace Machine

protected def toFormat (m : Machine) : Std.Format :=
  let body : List Std.Format := [
    f!"psr := {repr m.psr}",
    f!"ir := {repr m.ir}",
    f!"pc := {repr m.pc}",
    f!"mar := {repr m.mar}",
    f!"mdr := {m.mdr.toHexDigits}",
    f!"reg := {m.reg.map Int.toHexDigits}",
    f!"mem := {m.mem.toFormat}",
  ]
  Std.Format.bracket "{" (Std.Format.joinSep body ("," ++ Std.Format.line)) "}"

def init : Machine where
  psr := ⟨false, true, false, 0, .privilege⟩
  ir := .br false false false 0
  pc := .privMem 0
  mar := .privMem 0
  mdr := default
  reg := Array.mkArray 8 default
  reg_size_eq := rfl
  sspr := .userStack 0
  mem := ∅

instance : Inhabited Machine :=
  ⟨init⟩

@[inline]
def getReg (m : @& Machine) (i : Fin 8) : Int :=
  m.reg[i.1]'(m.reg_size_eq.symm ▸ i.2)

@[inline]
def setReg (m : Machine) (i : Fin 8) (n : Int) : Machine :=
  {m with
    reg := m.reg.set (i.cast m.reg_size_eq.symm) n
    reg_size_eq := by
      simp only [Array.size_set]
      exact m.reg_size_eq
  }

@[inline]
def getMem (m : @& Machine) (addr : Address) : Int :=
  m.mem[addr]

@[inline]
def setMem (m : Machine) (addr : Address) (n : Int) : Machine :=
  {m with
    mem := m.mem.set addr n
  }

/-- `m.getDevice i` returns the memory in the `i`-th device as `Std.HashMap Int Int` -/
def getDevice (m : @& Machine) (i : Nat) : Std.HashMap Int Int :=
  ∅ |> m.mem.fold fun x k n =>
    if k.deviceID? = .some i then
      x.insert k.val n
    else
      x

/--
Set the *Conditional Code* (i.e. `p`-, `z`-, and `n`-flags) properly depending on the given value.
-/
@[inline]
def setCC (m : Machine) (x : Int) : Machine :=
  {m with
    psr := {m.psr with
      p := decide (x > 0)
      z := decide (x = 0)
      n := decide (x < 0)
    }
  }


/-!
### The instruction cycle

The instruction cycle consists of the following phases:
1. FETCH
2. DECODE
3. EVALUATE ADDRESS
4. FETCH OPERANDS
5. EXECUTE
6. STORE RESULT
-/

open Encodable in
/--
The ***FETCH*** phase in the instruction cycle.
It goes as follows:
```
MAR ← PC;
PC ← PC + 1;
MDR ← mem[MAR];
IR ← MDR;
```
-/
def fetch (m : Machine) : Machine :=
  let m := {m with mar := m.pc}
  let m := {m with pc := m.pc + (1 : Int)}
  let m := {m with mdr := m.getMem m.mar}
  {m with ir := decode m.mdr}

/--
The ***DECODE*** phase in the instruction cycle.
The phase examines `IR` to determine what the architecture is to do.
Although it is an important phase for physical machines, we just skip it as implementing just a logical model.
-/
def decode (m : Machine) : Machine :=
  m

/--
The ***EVALUATE ADDRESS*** phase in the instruction cycle.
The phase computes `reg + offset` for those instructions who requires it.
- *BR*, *LD*, *ST*, *JSR* (with offset value), *LDI*, *STI*: `PC + offset`
- *LDR*: `sr + offset`
- *STR*: `dr + offset`
Note that the last two cases requires decoding the content of the register into `Address`.
-/
def evalAddress (m : Machine) : Machine :=
  match m.ir with
  | .br _ _ _ imm => {m with mar := m.pc + imm}
  | .add .. => m
  | .ld _ imm => {m with mar := m.pc + imm}
  | .st _ imm => {m with mar := m.pc + imm}
  | .jsr _ (.reg _) => m
  | .jsr _ (.imm imm) => {m with mar := m.pc + imm}
  | .and .. => m
  | .ldr _ sr imm =>
    {m with mar := (Encodable.decode (m.getReg sr) : Address) + imm}
  | .str _ dr imm =>
    {m with mar := (Encodable.decode (m.getReg dr) : Address) + imm}
  | .rti _ => m
  | .xor .. => m
  | .ldi _ imm => {m with mar := m.pc + imm}
  | .sti _ imm => {m with mar := m.pc + imm}
  | .jmp _ => m
  | .reserved _ => m
  | .lea _ imm => {m with mar := m.pc + imm}
  | .trap .. => m

/--
The ***FETCH OPERANDS*** phase in the instruction cycle.
It is only needed for *LOAD XXX* instructions; i.e. *LD*, *LDR*, *LDI*.
More precisely, the phase causes `MDR ← mem[MAR]` for *LD* and *LDR* while `MDR ← mem[mem[MAR]]` for *LDI*.
The phase may give rise to the ACV exception if `m.psr.mode = .user` and if the memory location lies in the privileged range.
-/
def fetchOp (m : Machine) : Option Machine :=
  match m.ir with
  | .ld .. | .ldr .. =>
    if m.psr.mode == .user && m.mar.isPrivilege then
      .none
    else
      .some {m with mdr := m.getMem m.mar}
  | .ldi .. =>
    if m.psr.mode == .user && m.mar.isPrivilege then
      .none
    else
      let aux : Address := Encodable.decode <| m.getMem m.mar
      if m.psr.mode == .user && aux.isPrivilege then
        .none
      else
        .some {m with mdr := m.getMem aux}
  | _ => .some m

/--
The ***EXECUTE*** phase in the instruction cycle, where the instruction is actually executed.
Except for *TRAP* and *RTI* instructions, in this phase, the instruction does not directly interact with the machine's main memory and uses `MAR` and `MDR` register instead.
The data movement between those registers and the memory is carried out in ***FETCH OPERANDS*** and ***STORE RESULT*** phases: see `LC3.Machine.fetchOp` and `LC3.Machine.storeResult`.
-/
def execute (m : Machine) : Option Machine :=
  match m.ir with
  | .br n z p _ =>
    if n && m.psr.n || z && m.psr.z || p && m.psr.p then
      .some {m with pc := m.mar}
    else
      .some m
  | .add dr sr1 rhs =>
    let op2 := match rhs with | .reg i => m.getReg i | .imm n => n
    let result := m.getReg sr1 + op2
    let m := m.setReg dr result
    .some <| m.setCC result
  | .ld dr _ =>
    let result := m.mdr
    let m := m.setReg dr result
    .some <| m.setCC result
  | .st sr _ =>
    .some {m with mdr := m.getReg sr}
  | .jsr dr (.reg sr) =>
    let aux : Int := Encodable.encode m.pc
    let m := {m with
      pc := Encodable.decode <| m.getReg sr
    }
    .some <| m.setReg dr aux
  | .jsr dr (.imm _) =>
    let m := m.setReg dr <| Encodable.encode m.pc
    .some {m with pc := m.mar}
  | .and dr sr1 rhs =>
    let op2 := match rhs with | .reg i => m.getReg i | .imm n => n
    let result := m.getReg sr1 &&& op2
    let m := m.setReg dr result
    .some <| m.setCC result
  | .ldr dr _ _ =>
    let result := m.mdr
    let m := m.setReg dr result
    .some <| m.setCC result
  | .str sr _ _ =>
    .some {m with mdr := m.getReg sr}
  | .rti spr =>
    if m.psr.mode = .user then
      .none
    else
      let sp : Address := Encodable.decode <| m.getReg spr
      let m := {m with
        psr := Encodable.decode <| m.getMem (sp + (1 : Int))
        pc := Encodable.decode <| m.getMem sp
      }
      let aux := sp + (2 : Int)
      match m.psr.mode with
      | .user =>
        let m := m.setReg spr <| Encodable.encode m.sspr
        .some <| {m with sspr := aux}
      | .privilege =>
        .some <| m.setReg spr <| Encodable.encode aux
  | .xor dr sr1 rhs =>
    let op2 := match rhs with | .reg i => m.getReg i | .imm n => n
    let result := m.getReg sr1 ^^^ op2
    let m := m.setReg dr result
    .some <| m.setCC result
  | .ldi dr _ =>
    let result := m.mdr
    let m := m.setReg dr result
    .some <| m.setCC result
  | .sti sr _ =>
    .some {m with mdr := m.getReg sr}
  | .jmp sr =>
    .some {m with pc := Encodable.decode <| m.getReg sr}
  | .reserved _ => m
  | .lea dr _ =>
    let result : Int := Encodable.encode m.mar
    let m := m.setReg dr result
    .some <| m.setCC result
  | .trap .. =>
    panic! "*TRAP* instruction has not been implemented yet."

/--
The ***STORE RESULT*** phase in the instruction cycle.
It is only needed for *STORE XXX* instructions; i.e. *ST*, *STR*, *STI*.
More precisely, the phase causes `mem[MAR] ← MDR` for *ST* and *STR* while `mem[mem[MAR]] ← MDR` for *STI*.
The phase may give rise to the ACV exception if `m.psr.mode = .user` and if the memory location lies in the privileged range.
-/
def storeResult (m : Machine) : Option Machine :=
  match m.ir with
  | .st .. | .str .. =>
    if m.psr.mode == .user && m.mar.isPrivilege then
      .none
    else
      m.setMem m.mar m.mdr
  | .sti .. =>
    if m.psr.mode == .user && m.mar.isPrivilege then
      .none
    else
      let aux : Address := Encodable.decode <| m.getMem m.mar
      if m.psr.mode == .user && aux.isPrivilege then
        .none
      else
        m.setMem aux m.mdr
  | _ => m

end Machine

#eval Machine.init |>.fetch
end LC3
