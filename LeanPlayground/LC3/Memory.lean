import Std.Data.HashMap

import LeanPlayground.Data.Int.Bit
import LeanPlayground.LC3.Encodable

/-!
# Structure of the memory of LC-3

In the original ***LC-3*** architecture, the main memory is divided into the following five categories (see Section A.1 of *Introduction to Computing Systems* by Yale Patt and Sanjay Patel):

- Trap Vector Table
- Interrupt Vector Table
- Privileged Memory
- Supervisor Stack
- Unprivileged Memory
- User Stack
- Device Register Addresses

As a logical model, our model instead has six separated memory areas from the beginning corresponding to the above categories except *Interrupt Vector Table*.
In addition, for the simplicity, we expand devices into the memory so that they are accessed in completely the same way as the other areas of the memory.
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

universe u

namespace LC3

/-!
### Memory addressing
-/

inductive Address where
| trapvec (n : Int) : Address
| privMem (n : Int) : Address
| privStack (n : Int) : Address
| userMem (n : Int) : Address
| userStack (n : Int) : Address
| device (i : Nat) (n : Int) : Address
deriving DecidableEq, Repr, Hashable

namespace Address

open Encodable in
instance : Encodable Address Int where
  encode addr :=
    match addr with
    | .trapvec n => encode ((0 : Fin 6), n)
    | .privMem n => encode ((1 : Fin 6), n)
    | .privStack n => encode ((2 : Fin 6), n)
    | .userMem n => encode ((3 : Fin 6), n)
    | .userStack n => encode ((4 : Fin 6), n)
    | .device i n => encode ((5 : Fin 6), (encode (i, n) : Int))
  decode n :=
    match (decode n : Fin 6 × Int) with
    | (0, n) => .trapvec n
    | (1, n) => .privMem n
    | (2, n) => .privStack n
    | (3, n) => .userMem n
    | (4, n) => .userStack n
    | (5, n) => let (i,n) := (decode n : Nat × Int); .device i n
  decode_encode addr := by
    cases addr <;> simp only [decode_encode]

@[inline]
def isUser (addr : @& Address) : Bool :=
  match addr with
  | .trapvec _ | privMem _ | privStack _ => false
  | .userMem _ | .userStack _ | .device _ _ => true

@[inline]
def isPrivilege (addr : @& Address) : Bool :=
  match addr with
  | .trapvec _ | privMem _ | privStack _ => true
  | .userMem _ | .userStack _ | .device _ _ => false

@[inline]
def deviceID? (addr : @& Address) : Option Nat :=
  match addr with
  | .device i _ => .some i
  | _           => .none

@[inline]
def val (addr : @& Address) : Int :=
  match addr with
  | .trapvec n => n
  | .privMem n => n
  | .privStack n => n
  | .userMem n => n
  | .userStack n => n
  | .device _ n => n

@[inline]
def map (f : Int → Int) : Address → Address
| .trapvec n => .trapvec <| f n
| .privMem n => .privMem <| f n
| .privStack n => .privStack <| f n
| .userMem n => .userMem <| f n
| .userStack n => .userStack <| f n
| .device i n => .device i <| f n

instance : HAdd Address Int Address where
  hAdd addr n := addr.map (· + n)

end Address


/-!
### Structure of the memory
-/

/-- The memory structure of the LC-3 machine model -/
structure Memory where
  val : Std.HashMap Address Int

namespace Memory

instance : EmptyCollection Memory :=
  ⟨⟨∅⟩⟩

instance : GetElem Memory Address Int (fun _ _ => True) where
  getElem mem k _ := mem.val[k].getD default

@[inline]
protected def set (mem : Memory) (addr : Address) (n : Int) : Memory :=
  ⟨mem.val.insert addr n⟩

@[inline]
protected def fold {α : Type u} (mem : @& Memory) (f : α → Address → Int → α) (init : α) : α :=
  mem.val.fold f init

protected def toFormat (x : Memory) : Std.Format :=
  let entries : List Std.Format :=
    [] |> x.fold fun fs a b =>
      fs ++ [Std.Format.text s!"{repr a} ↦ {b.toHexDigits}"]
  Std.Format.joinSep entries ("," ++ Std.Format.line) |>.sbracket

instance : Repr Memory where
  reprPrec x _ := x.toFormat

/-- `m.getDevice i` returns the memory in the `i`-th device as `Std.HashMap Int Int` -/
def getDevice (mem : @& Memory) (i : Nat) : Std.HashMap Int Int :=
  ∅ |> mem.fold fun x k n =>
    if k.deviceID? = .some i then
      x.insert k.val n
    else
      x

def setDevice (mem : Memory) (i : Nat) (data : Array Int) : Memory :=
  Id.run <| do
    let mut result := mem
    for h : j in [0:data.size] do
      result := result.set (.device i (.ofNat j)) data[j]
    return result

end Memory

end LC3
