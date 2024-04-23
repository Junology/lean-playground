import Std.Data.Array.Basic
import Std.Data.Array.Lemmas
import Std.Data.List.Basic

set_option autoImplicit false

universe u v

variable {α : Type u} [Add α]

def test1 (x : Array α) (i : Nat) (_ : i < x.size) : Array α :=
  let rec @[specialize] loop (x : Array α) (k : Nat) (hik : i < k) : Array α :=
    if hk : k < x.size then
      loop (x.modify k (· + x[i]'(trans hik hk :))) (k+1) (.step hik)
    else
      x
  termination_by x.size - k
  loop x (i+1) .refl

def test2 (x : Array α) (i : Nat) (hi : i < x.size) : Array α :=
  let rec @[specialize] loop (x : Array α) (a : @& α) (k : Nat) : Array α :=
    if hk : k < x.size then
      loop (x.modify k (· + a)) a (k+1)
    else
      x
  termination_by x.size - k
  loop x (x[i]'hi) (i+1)

def test2' (x : Array α) (i : Nat) (hi : i < x.size) : Array α :=
  let rec @[specialize] loop (x : Array α) (a : α) (k : Nat) : Array α :=
    if hk : k < x.size then
      loop (x.modify k (· + a)) a (k+1)
    else
      x
  termination_by x.size - k
  loop x (x[i]'hi) (i+1)

def test3 (x : Array α) (i : Nat) (_ : i < x.size) : Array α :=
  Id.run <| do
    let n := x.size
    let mut x : Subtype (fun x => x.size = n) := ⟨x, rfl⟩
    for hk : k in [i+1 : n] do
      have : k < x.1.size := x.2.symm ▸ hk.2
      have : i < x.1.size := Nat.lt_trans hk.1 this
      x := {
        val := x.1.modify k (· + x.1[i])
        property := by simp [x.2]
      }
    return x

def test4 (x : Array α) (i : Nat) (_ : i < x.size) : Array α :=
  Id.run <| do
    let n := x.size
    let a := x[i]
    let mut x : Subtype (fun x => x.size = n) := ⟨x, rfl⟩
    for hk : k in [i+1 : n] do
      have : k < x.1.size := x.2.symm ▸ hk.2
      have : i < x.1.size := Nat.lt_trans hk.1 this
      x := {
        val := x.1.modify k (· + a)
        property := by simp [x.2]
      }
    return x

def testArray : Array Nat :=
  Array.ofFn fun (i : Fin 0x100) => 2^i.1

unsafe def runTest (f : (x : Array Nat) → (i : Nat) → i < x.size → Array Nat) (n : Nat) : IO Nat := do
  let start ← IO.monoNanosNow
  n.forM fun _ => do
    IO.sleep 0
    let mut x := testArray
    for i in [0 : x.size] do
      x := f x i lcProof
  let stop ← IO.monoNanosNow
  return (stop - start) / n

unsafe def main : IO Unit :=
  let fs := #[test1 (α:=Nat), test2, test2', test3, test4]
  let is := List.ofFn <| id (α := Fin fs.size)
  do
    let stdout ← IO.getStdout
    stdout.putStrLn s!"Benchmark on {fs.size} functions"
    let mut ns := Array.mkArray fs.size (0 : Nat)
    for k in [0 : fs.size] do
      IO.sleep 1
      for i in is.rotate k do
        let n ← runTest (fs[i]) 10
        ns := ns.modify i (· + n)
    is.forM fun i => do
      stdout.putStrLn s!"#{i}: {ns[i]! / fs.size}"
