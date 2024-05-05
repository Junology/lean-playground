import Std.Tactic.Basic

/-!
# Integers as infinite bit sequences

-/

namespace Nat

theorem testBit_le {n i : Nat} (h : n ≤ i) : n.testBit i = false := by
  refine testBit_lt_two_pow ?_
  refine Nat.lt_of_lt_of_le (m:=2^n) ?_ ?_
  . show n < 2^n
    induction n with
    | zero => exact .refl
    | succ n IH =>
      specialize IH <| Nat.le_of_lt h
      rewrite [Nat.succ_eq_add_one, Nat.pow_succ, Nat.mul_two]
      refine Nat.add_lt_add_of_lt_of_le IH ?_
      exact Nat.le_trans n.succ_pos IH
  . exact Nat.pow_le_pow_right Nat.two_pos h

end Nat

namespace Int

/--
`Int.testBit x i` returns whether the `(i+1)`-st least sigfinicant bit of `x` is set or unset when `x : Int` is regarded as a 2-adic integer via `Int ⊆ ℤ₂`.
For example, we have `-42 = ~~~41 = ⋯111010110` so
```lean
#eval Int.testBit (-42) <$> [0,1,2,3,4,5,6,7,8]
/- [false, true, true, false, true, false, true, true, true] -/
```
This function has already defined in `Mathlib`.
-/
protected def testBit (x : Int) (i : Nat) : Bool :=
  match x with
  | .ofNat n => n.testBit i
  | -[n+1] => ! n.testBit i

/--
`Int.natBitwise f m n` applies a bit operation `f : Bool → Bool → Bool` to each pair of bits in `m n : Nat`.
In contrast to `Nat.bitwise`, it does not require `f false false = false`.
-/
def natBitwise (f : Bool → Bool → Bool) (m n : Nat) : Int :=
  bif f false false then
    -[Nat.bitwise (fun x y => ! f x y) m n +1]
  else
    .ofNat <| Nat.bitwise f m n

/--
Apply a bitwise operation regarding `Int` as a subring of the 2-adic integer ring ℤ₂.
In contrast to `Nat.bitwise`, `Int.bitwise` literally applies `f : Bool → Bool → Bool` to *all* the bits in the infinite sequence.
-/
protected def bitwise (f : Bool → Bool → Bool) (x y : Int) : Int :=
  match x, y with
  | .ofNat m, .ofNat n => Int.natBitwise f m n
  | .ofNat m, -[n+1]   => Int.natBitwise (fun a b => f a (!b)) m n
  | -[m+1],   .ofNat n => Int.natBitwise (fun a b => f (!a) b) m n
  | -[m+1],   -[n+1]   => Int.natBitwise (fun a b => f (!a) (!b)) m n

theorem testBit_zero (x : Int) : x.testBit 0 = decide (x % 2 = 1) := by
  match x with
  | .ofNat n =>
    have : Int.ofNat n % 2 = 1 ↔ n % 2 = 1 := by
      conv => lhs; change Int.ofNat (n % 2) = Int.ofNat 1
      exact Int.ofNat_inj
    simp only [this, Int.testBit]
    exact n.testBit_zero
  | -[n+1] =>
    rewrite [Int.mod_def']
    dsimp only [Int.testBit, Int.emod, natAbs]
    have : (n % 2).succ ≤ 2 :=
      show n % 2 < 2 from Nat.mod_lt n (by decide)
    rewrite [Int.subNatNat_of_le this, Nat.succ_sub_succ 1]
    rewrite [n.testBit_zero, ←decide_not]
    apply decide_eq_decide.mpr
    conv =>
      rhs; change @Nat.cast _ _ (1-n%2) = @Nat.cast Int _ 1
      rewrite [Int.ofNat_inj (m:=1-n%2) (n:=1)]
      rewrite [Nat.sub_eq_iff_eq_add' (Nat.le_of_succ_le_succ this)]
      rewrite [Nat.succ_inj']
    cases n.mod_two_eq_zero_or_one with
    | inl h => rewrite [h]; decide
    | inr h => rewrite [h]; decide

theorem testBit_succ (x : Int) (i : Nat) : x.testBit (i+1) = (x / 2).testBit i := by
  match x with
  | .ofNat n =>
    conv => rhs; arg 1; change .ofNat (n/2)
    dsimp only [Int.testBit]
    exact n.testBit_succ i
  | -[n+1] =>
    conv => rhs; arg 1; change -[n/2+1]
    dsimp only [Int.testBit]
    apply congrArg Bool.not
    exact n.testBit_succ i

theorem eq_of_testBit_eq {x y : Int} (h : ∀ i, x.testBit i = y.testBit i) : x = y := by
  match x, y with
  | .ofNat m, .ofNat n =>
    dsimp only [Int.testBit] at h
    refine Int.ofNat_inj.mpr ?_
    exact Nat.eq_of_testBit_eq h
  | .ofNat m, -[n+1] =>
    exfalso
    dsimp only [Int.testBit] at h
    specialize h (m+n)
    conv at h =>
      rewrite [Nat.testBit_le (m.le_add_right n)]
      rewrite [Nat.testBit_le (n.le_add_left m)]
    nomatch h
  | -[m+1], .ofNat n =>
    exfalso
    dsimp only [Int.testBit] at h
    specialize h (m+n)
    conv at h =>
      rewrite [Nat.testBit_le (m.le_add_right n)]
      rewrite [Nat.testBit_le (n.le_add_left m)]
    nomatch h
  | -[m+1], -[n+1] =>
    simp only [Int.testBit, Bool.not_inj_iff] at h
    refine Int.negSucc_inj.mpr ?_
    exact Nat.eq_of_testBit_eq h

theorem testBit_not (x : Int) (i : Nat) : x.not.testBit i = ! x.testBit i := by
  cases x <;> dsimp only [Complement.complement, Int.not, Int.testBit]
  rw [Bool.not_not]

theorem testBit_complement (x : Int) (i : Nat) : (~~~x).testBit i = ! x.testBit i :=
  x.testBit_not i

theorem testBit_natBitwise {f : Bool → Bool → Bool} (m n i : Nat) : (natBitwise f m n).testBit i = f (m.testBit i) (n.testBit i) := by
  cases hf : f false false with
  | false =>
    simp only [natBitwise, hf, cond, Int.testBit]
    exact Nat.testBit_bitwise hf ..
  | true =>
    apply Bool.not_inj
    simp only [natBitwise, hf, cond, Int.testBit, Bool.not_not]
    refine Nat.testBit_bitwise ?_ ..
    rewrite [hf]; rfl

theorem testBit_mul_two_succ (x : Int) (i : Nat) : (x * 2).testBit (i+1) = x.testBit i := by
  rewrite [testBit_succ]
  conv => lhs; arg 1; equals x =>
    refine Int.mul_ediv_cancel x ?_
    decide

/--
TODO: efficient implementation in terms of `Nat.land`.
-/
protected def and (x y : Int) : Int :=
  x.bitwise and y

instance : AndOp Int :=
  ⟨Int.and⟩

/--
TODO: efficient implementation in terms of `Nat.lor`.
-/
protected def or (x y : Int) : Int :=
  x.bitwise or y

instance : OrOp Int :=
  ⟨Int.or⟩

/--
TODO: efficient implementation in terms of `Nat.xor`.
-/
protected def xor (x y : Int) : Int :=
  x.bitwise xor y

instance : Xor Int :=
  ⟨Int.xor⟩

end Int
