import Std.Tactic.Basic

import LeanPlayground.Data.Nat.Pairing

/-!
# Encoding data into numerals

We define a type class `Encodable α ν` asserting that `α` is encoded into `ν`.
More precisely, it has the following methods:

- `Encodable.encode : α → ν`
- `Encodable.decode : ν → α`
- `Encodable.decode_encode : ∀ (a : α), decode (encode a) = a`

## Remark

The method `Encodable.decode` is a total function just for the simplicity.
As a result, one cannot write instances for empty types such as `Fin 0` unless the encoded type `ν` is empty.
One can of course define a version with a decoder as a partial function if necessary.
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

/-!
### Preliminaries
-/

namespace Prod

universe u₁ u₂ v₁ v₂

theorem map_fst {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂} (f : α₁ → α₂) (g : β₁ → β₂) (p : α₁ × β₁) : (p.map f g).fst = f p.fst :=
  rfl

theorem map_snd {α₁ : Type u₁} {α₂ : Type u₂} {β₁ : Type v₁} {β₂ : Type v₂} (f : α₁ → α₂) (g : β₁ → β₂) (p : α₁ × β₁) : (p.map f g).snd = g p.snd :=
  rfl


end Prod

namespace Nat

protected class Positive (n : Nat) : Prop where
  positive : n > 0

instance succ_positive (n : Nat) : Nat.Positive (n+1) where
  positive := n.succ_pos

namespace Positive

protected theorem ne_zero {n : Nat} [Nat.Positive n] : n ≠ 0 :=
  Nat.ne_of_gt Positive.positive

end Positive

end Nat

namespace Int

theorem negSucc_lt_ofNat (m n : Nat) : -[m+1] < ↑(n : Nat) := by
  show (Int.ofNat n - (-[m+1] + 1)).NonNeg
  conv => arg 1; equals .ofNat (n+m) =>
    rewrite [Int.negSucc_eq, Int.neg_add, Int.neg_add_cancel_right, Int.sub_neg]
    rfl
  exact .mk (n+m)

theorem toNat_lt' {a : Int} {n : Nat} (h : n > 0) : a.toNat < n ↔ a < ↑(n : Nat) := by
  match a with
  | .ofNat k => simp
  | -[k+1] =>
    simp only [Int.toNat, iff_true_left h]
    exact negSucc_lt_ofNat k n

--theorem emod_ofNat_lt (a : Int) {n : Nat} (h : n > 0) : a % ↑n < n := by
  --sorry

@[inline]
protected def pair (a b : Int) : Int :=
  let rec tonat (a : Int) : Nat :=
    match a with
    | .ofNat n => 2*n
    | -[n+1]   => 2*n+1
  match a with
  | .ofNat m => .ofNat <| Nat.pair m (tonat b)
  | -[m+1]   => -[Nat.pair m (tonat b)+1]

protected def unpair (a : Int) : Int × Int :=
  let rec fromnat (n : Nat) : Int :=
    if n % 2 = 0 then .ofNat (n/2) else -[n/2+1]
  match a with
  | .ofNat n => Prod.map ofNat fromnat <| Nat.unpair n
  | -[n+1] => Prod.map negSucc fromnat <| Nat.unpair n

theorem unpair_pair (a b : Int) : Int.unpair (Int.pair a b) = (a,b) := by
  cases a <;> cases b <;> rename_i m n
    <;> all_goals refine Prod.ext ?_ ?_
    <;> dsimp [Int.pair, pair.tonat, Int.unpair]
    <;> simp only [Prod.map_fst, Prod.map_snd, Nat.unpair_pair]
    <;> try rfl
  all_goals
    unfold unpair.fromnat
    simp only [Nat.mul_mod_right 2 n, Nat.mul_add_mod 2 n 1, if_true, if_false]
    simp only [Nat.mul_div_right n Nat.two_pos, Nat.mul_add_div Nat.two_pos]
    rfl

end Int


/-!
### Definition
-/

namespace LC3

universe u v

class Encodable (α : Type u) (ν : Type v) where
  encode : α → ν
  decode : ν → α
  decode_encode : ∀ (a : α), decode (encode a) = a

namespace Encodable

/-!
### Basic declarations
-/

/-- Every type can be trivially encoded into itself with `id` -/
protected instance (priority:=high) instId (α : Type u) : Encodable α α where
  encode := id
  decode := id
  decode_encode _ := rfl


/-!
### Encoding into `Nat`
-/

section Nat

variable {α : Type u} {β : Type v} [Encodable α Nat] [Encodable β Nat]

protected instance instFinNat (n : Nat) [Nat.Positive n] : Encodable (Fin n) Nat where
  encode := Fin.val
  decode k := ⟨k % n, k.mod_lt Nat.Positive.positive⟩
  decode_encode i := Fin.eq_of_val_eq <| i.1.mod_eq_of_lt i.2

protected instance instFinProdNat (n : Nat) [Nat.Positive n] : Encodable (Fin n × α) Nat where
  encode x := x.1.1 + n * encode x.2
  decode k := (⟨k % n, k.mod_lt Nat.Positive.positive⟩, decode (k / n))
  decode_encode x := by
    refine Prod.ext (Fin.eq_of_val_eq ?_) ?_
    . show (x.1.1 + n * encode x.2) % n = x.1.1
      rewrite [Nat.add_mul_mod_self_left]
      exact x.1.1.mod_eq_of_lt x.1.2
    . show decode ((x.1.1 + n * encode x.2) / n) = x.2
      rewrite [Nat.add_mul_div_left x.1.1 _ Nat.Positive.positive]
      rewrite [Nat.div_eq_of_lt x.1.2, Nat.zero_add]
      exact decode_encode x.2

attribute [irreducible] Encodable.decode in
protected instance instBoolProdNat : Encodable (Bool × α) Nat where
  encode x := encode (Fin.mk (n:=2) x.1.toNat x.fst.toNat_lt, x.2)
  decode p := Prod.map (· == 1) id <| (decode p : Fin 2 × α)
  decode_encode x := by
    rcases x with ⟨b, a⟩
    simp only [Prod.map, decode_encode, id]
    refine Prod.ext ?_ rfl
    simp only
    cases b <;> dsimp [Bool.toNat] <;> decide

protected instance instSumNat : Encodable (α ⊕ β) Nat where
  encode p :=
    match p with
    | .inl a => 2 * encode a
    | .inr b => 1 + 2 * encode b
  decode k :=
    if k % 2 = 0 then
      .inl <| decode (k/2)
    else
      .inr <| decode (k/2)
  decode_encode p := by
    match p with
    | .inl a =>
      simp only [Nat.mul_mod_right, ite_true, Nat.mul_div_right _ Nat.two_pos]
      exact congrArg Sum.inl <| decode_encode a
    | .inr b =>
      simp only [Nat.add_mul_mod_self_left, ite_false, Nat.add_mul_div_left 1 _ Nat.two_pos, Nat.div_eq_of_lt (Nat.succ_lt_succ Nat.one_pos), Nat.zero_add]
      exact congrArg Sum.inr <| decode_encode b

open Int in
protected instance instIntNat : Encodable Int Nat where
  encode k :=
    match k with
    | .ofNat n => 2 * n
    | -[n+1] => 1 + 2 * n
  decode n :=
    if n % 2 = 0 then
      .ofNat (n/2)
    else
      -[n/2+1]
  decode_encode k := by
    match k with
    | .ofNat n =>
      simp only [Nat.mul_mod_right, ite_true, Nat.mul_div_right _ Nat.two_pos]
    | -[n+1] =>
      simp only [Nat.add_mul_mod_self_left, ite_false]
      rewrite [Nat.add_mul_div_left 1 _ Nat.two_pos, Nat.add_comm]
      rfl

protected instance instCharNat : Encodable Char Nat where
  encode c := c.toNat
  decode n := Char.ofNat n
  decode_encode c := by
    rcases c with ⟨⟨c,hlt⟩, hvalid⟩
    dsimp only [Char.ofNat, Char.toNat, Char.ofNatAux]
    dsimp [UInt32.isValidChar, UInt32.toNat] at hvalid ⊢
    simp only [Int.toNat_ofNat, dif_pos hvalid]

protected instance (priority:=low) instProdNat : Encodable (α × β) Nat where
  encode x := Nat.pair (encode x.1) (encode x.2)
  decode n := Prod.map decode decode n.unpair
  decode_encode x := by
    simp only [Nat.unpair_pair]
    simp only [Prod.map, decode_encode]

end Nat


/-!
### Encoding into `Int`
-/

section Int

variable {α : Type u} {β : Type v} [Encodable α Int] [Encodable β Int]

protected instance (priority:=low+1) instOfNatInt (α : Type u) [Encodable α Nat] : Encodable α Int where
  encode a := ↑(encode a : Nat)
  decode k := decode k.toNat
  decode_encode a := by
    simp only [Int.toNat_ofNat]
    exact decode_encode a

attribute [irreducible] Encodable.decode in
protected instance (priority:=high+1) instFinProdInt (n : Nat) [Nat.Positive n] : Encodable (Fin n × α) Int where
  encode p := p.1.1 + n * encode p.2
  decode k :=
    have := by
      refine Int.toNat_lt' Nat.Positive.positive |>.mpr ?_
      refine Int.emod_lt_of_pos k ?_
      exact Int.ofNat_pos.mpr Nat.Positive.positive
    (⟨Int.toNat (k % n), this⟩, decode (k / n))
  decode_encode x :=
    match x with
    | (i,a) => by
      refine Prod.ext (Fin.eq_of_val_eq ?_) ?_
      . show Int.toNat ((i.val + n * (encode a : Int)) % n) = i.val
        rewrite [Int.add_mul_emod_self_left i.val n _]
        exact i.val.mod_eq_of_lt i.isLt
      . show decode ((i.val + n * (encode a : Int)) / n) = a
        have : ↑(n : Nat) ≠ (0 : Int) := by
          intro h; rcases h with ⟨rfl⟩; nomatch i
        rewrite [Int.mul_comm ↑n _, Int.add_mul_ediv_right _ _ this]
        rewrite [← Int.ofNat_ediv, i.val.div_eq_of_lt i.isLt]
        simp_arith
        exact decode_encode a

attribute [irreducible] Encodable.decode in
protected instance instBoolProdInt : Encodable (Bool × α) Int where
  encode x := encode (Fin.mk (n:=2) x.1.toNat x.fst.toNat_lt, x.2)
  decode p := Prod.map (· == 1) id <| (decode p : Fin 2 × α)
  decode_encode x := by
    rcases x with ⟨b, a⟩
    simp only [Prod.map, decode_encode, id]
    refine Prod.ext ?_ rfl
    simp only
    cases b <;> dsimp [Bool.toNat] <;> decide

open Int in
attribute [irreducible] Encodable.decode in
protected instance (priority:=low+1) instProdInt : Encodable (α × β) Int where
  encode x :=
    match (encode x.1 : Int) with
    | .ofNat n => .ofNat <| encode (n, (encode x.2 : Int))
    | -[n+1] => -[encode (n, (encode x.2 : Int))+1]
  decode k :=
    match k with
    | .ofNat n => Prod.map (decode ∘ Int.ofNat) decode <| (decode n : Nat × Int)
    | -[n+1] => Prod.map (decode ∘ Int.negSucc) decode <| (decode n : Nat × Int)
  decode_encode x := by
    rcases x with ⟨a,b⟩
    simp only
    cases h : (encode a : Int)
    all_goals
      simp only [decode_encode, Prod.map, Function.comp]
      rw [← h, decode_encode]

end Int


/-
# Test codes
-/
/-- info: 267 -/
#guard_msgs in
#eval (encode ((3 : Fin 8), (1 : Fin 8), (4 : Nat)) : Int)

/-- info: (3, 1, 4) -/
#guard_msgs in
#eval (decode 267 : Fin 8 × Fin 8 × Nat)

/-- info: -83 -/
#guard_msgs in
#eval (encode (true, -42) : Int)

/-- info: (true, -42) -/
#guard_msgs in
#eval (decode (-83) : Bool × Int)

end Encodable

end LC3
