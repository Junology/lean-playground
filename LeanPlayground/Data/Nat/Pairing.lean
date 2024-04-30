/-!
# Pairing of `Nat`

In this file, we prove a famous fact that the product `Nat × Nat` is isomorphic to `Nat`.
In particular, we construct functions `pair : Nat → Nat → Nat` and `unpair : Nat → Nat × Nat` and prove that they are mutually inverses.

## Remark

The results are also found in `Mathlib.Data.Nat.Paring`.
We aim at providing a different approach which does not use `Classical.choice` and `Nat.sqrt`.
-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

namespace Nat

/-!
### Declarations about triangular numbers
-/

/-- Triangular number -/
@[inline]
def triangle (n : Nat) : Nat :=
  n * (n+1) / 2

@[simp]
theorem triangle_zero : triangle 0 = 0 := rfl

@[simp]
theorem triangle_succ (n : Nat) : triangle (n+1) = triangle n + n + 1 := by
  rewrite [Nat.add_assoc]
  unfold triangle
  rw [← Nat.add_mul_div_left _ _ Nat.two_pos, ← Nat.add_mul, Nat.mul_comm]

theorem triangle_lt {m n : Nat} (h : m < n) : triangle m < triangle n := by
  induction h with
  | refl =>
    rewrite [triangle_succ, Nat.add_assoc]
    exact Nat.lt_add_of_pos_right m.succ_pos
  | step hle IH =>
    rename_i n
    rewrite [triangle_succ, Nat.add_assoc]
    exact Nat.lt_add_right (n+1) IH

theorem triangle_le {m n : Nat} (h : m ≤ n) : triangle m ≤ triangle n :=
  match Nat.lt_or_eq_of_le h with
  | .inl hlt => Nat.le_of_lt <| triangle_lt hlt
  | .inr heq => Nat.le_of_eq <| congrArg triangle heq


/-!
### The pairing function `Nat.pair`
-/

/--
`Nat.pair m n` encodes a pair of `m n : Nat` into a single natural number.
See also a recursive version `Nat.pair'` and comparison `Nat.pair'_eq_pair`.
-/
@[inline]
def pair (m n : Nat) : Nat :=
  triangle (m+n) + m

@[simp]
theorem pair_zero_zero : pair 0 0 = 0 := rfl

@[simp]
theorem pair_zero_succ (n : Nat) : pair 0 (n+1) = pair n 0 + 1 := by
  unfold pair
  simp only [Nat.add_zero, Nat.zero_add, triangle_succ]

@[simp]
theorem pair_succ_left (m n : Nat) : pair (m+1) n = pair m (n+1) + 1 := by
  unfold pair
  rewrite [Nat.add_assoc _ m 1]
  simp only [Nat.succ_add, Nat.add_succ]

theorem pair_eq_zero_left {m n : Nat} (h : pair m n = 0) : m = 0 := by
  unfold pair at h
  exact (Nat.add_eq_zero_iff.mp h).2

theorem pair_eq_zero_right {m n : Nat} (h : pair m n = 0) : n = 0 := by
  cases pair_eq_zero_left h
  cases n with
  | zero => rfl
  | succ n => rewrite [pair_zero_succ] at h; nomatch h

/--
An induction principle of `Nat.pair`.
Although `Nat.pair` is defined in an algebraic way, this shows that it is also defined recursively with the following cases:
- `Nat.pair 0 0`
- `Nat.pair 0 (n+1)`
- `Nat.pair (m+1) n`
This recursive version is found as `Nat.pair'` with comparison `Nat.pair'_eq_pair`.
-/
theorem pair_induction_on
  {motive : Nat → Nat → Nat → Prop}
  (m n : Nat)
  (zero_zero : motive 0 0 0)
  (zero_succ : ∀ n k, motive n 0 k → motive 0 (n+1) (k+1))
  (succ_left : ∀ m n k, motive m (n+1) k → motive (m+1) n (k+1)) :
  motive m n (pair m n) := by
  generalize hk : pair m n = k
  induction k generalizing m n with
  | zero =>
    cases pair_eq_zero_left hk
    cases pair_eq_zero_right hk
    exact zero_zero
  | succ k IH =>
    match m, n with
    | 0, 0 => rewrite [pair_zero_zero] at hk; nomatch hk
    | 0, n+1 =>
      rewrite [pair_zero_succ, Nat.add_one] at hk
      cases Nat.succ.inj hk
      exact zero_succ n _ <| IH n 0 rfl
    | m+1, n =>
      rewrite [pair_succ_left, Nat.add_one] at hk
      cases Nat.succ.inj hk
      exact succ_left m n _ <| IH m (n+1) rfl

/-- A recursive version of `Nat.pair`. -/
def pair' (m n : Nat) : Nat :=
  match m, n with
  | 0, 0 => 0
  | 0, n+1 => pair' n 0 + 1
  | m+1, n => pair' m (n+1) + 1
termination_by (m+n, m)
decreasing_by
  all_goals simp_wf
  . exact Prod.Lex.left _ _ n.lt_succ_self
  . rewrite [Nat.add_succ, Nat.succ_add]
    exact Prod.Lex.right _ m.lt_succ_self

/-- Comparison of `Nat.pair` and `Nat.pair'` -/
theorem pair'_eq_pair (m n : Nat) : pair' m n = pair m n := by
  apply pair_induction_on m n
  . show pair' 0 0 = 0; rfl
  . intro n k IH; unfold pair'; exact congrArg (·+1) IH
  . intro m n k IH; unfold pair'; exact congrArg (·+1) IH


/-!
### The unparing function `Nat.unpair`
-/

/- The *unparing* function of `Nat` that distributes a single number into a pair -/
@[inline]
def unpair (n : Nat) : Nat × Nat :=
  let rec loop (n i : Nat) : Nat × Nat :=
    if h : i < n then
      have : n - i - 1 < n :=
        show n - i - 1 + 1 ≤ n from
        Nat.sub_add_cancel (Nat.sub_pos_of_lt h) ▸ n.sub_le i
      loop (n-i-1) (i+1)
    else
      (n, i-n)
  termination_by n
  loop n 0

theorem unpair.loop_add_triangle (n i k : Nat) : unpair.loop (n + triangle (i+k) - triangle i) i = unpair.loop n (i+k) := by
  induction k generalizing i n with
  | zero => rw [Nat.add_zero, Nat.add_sub_cancel]
  | succ k IH =>
    simp only [Nat.succ_eq_add_one, ← Nat.add_assoc]
    have : i < n + triangle (i+k+1) - triangle i := by
      apply Nat.lt_of_sub_pos
      rewrite [Nat.sub_sub]
      apply Nat.sub_pos_of_lt
      show triangle i + i + 1 ≤ n + triangle (i+k+1)
      refine Nat.le_trans ?_ (Nat.le_add_left _ n)
      rewrite [← triangle_succ]
      exact triangle_le <| Nat.succ_le_succ <| i.le_add_right k
    conv =>
      lhs; unfold loop; simp only [dif_pos this, Nat.sub_sub]
      rewrite [← triangle_succ i]
    specialize IH n (i+1)
    simp only [Nat.succ_add, Nat.succ_eq_add_one] at IH
    rw [IH]

theorem unpair_add_triangle (n i : Nat) : unpair (n + triangle i) = unpair.loop n i := by
  have := unpair.loop_add_triangle n 0 i
  simp only [Nat.zero_add, triangle_zero, Nat.sub_zero] at this
  exact this

theorem unpair_zero : unpair 0 = (0,0) :=
  rfl

theorem unpair_of_le {n i : Nat} (h : n ≤ i) : unpair (n + triangle i) = (n,i-n) := by
  rewrite [unpair_add_triangle]
  unfold unpair.loop
  simp only [dif_neg <| Nat.not_lt_of_ge h]

/-- A one-step recursive version of `Nat.unpair` -/
def unpair' : Nat → Nat × Nat
| 0 => (0,0)
| k+1 =>
  let (m,n) := unpair' k
  match n with
  | 0 => (0, m+1)
  | n+1 => (m+1,n)

/-- The induction principle coming equipped with the recursive definition of `Nat.unpair'` -/
theorem unpair'_induction_on
  {motive : Nat → Nat × Nat → Prop}
  (k : Nat)
  (zero : motive 0 (0,0))
  (succ_zero : ∀ k m, motive k (m, 0) → motive (k+1) (0, m+1))
  (succ_succ : ∀ k m n, motive k (m, n+1) → motive (k+1) (m+1,n)) :
  motive k (unpair' k) := by
  induction k with
  | zero => exact zero
  | succ k IH =>
    dsimp only [unpair']
    rcases h : unpair' k with ⟨m,n⟩; simp only []
    rewrite [h] at IH
    match n with
    | 0 => exact succ_zero k m IH
    | n+1 => exact succ_succ k m n IH


/-!
### The main results
-/

theorem unpair_pair (m n : Nat) : unpair (pair m n) = (m,n) := by
  unfold pair
  rewrite [Nat.add_comm _ m, unpair_add_triangle m (m+n)]
  unfold unpair.loop
  have : ¬ (m+n < m) := Nat.not_lt_of_ge <| m.le_add_right n
  simp only [dif_neg this]
  rw [Nat.add_comm m n, Nat.add_sub_cancel]

theorem pair_unpair' (n : Nat) : pair (unpair' n).1 (unpair' n).2 = n := by
  apply unpair'_induction_on (motive:=fun k x => pair x.1 x.2 = k)
  . show pair 0 0 = 0; rfl
  . show ∀ k m, pair m 0 = k → pair 0 (m+1) = k+1
    simp only [pair_zero_succ]
    intro _ _; exact congrArg Nat.succ
  . show ∀ k m n, pair m (n+1) = k → pair (m+1) n = k+1
    simp only [pair_succ_left]
    intro _ _ _; exact congrArg Nat.succ

theorem unpair'_eq_unpair (n : Nat) : unpair' n = unpair n := by
  rcases h : unpair' n with ⟨i,j⟩
  have := congrArg (fun x => pair x.1 x.2) h
  simp only [pair_unpair'] at this
  cases this
  exact (unpair_pair i j).symm

theorem pair_unpair (n : Nat) : pair (unpair n).1 (unpair n).2 = n := by
  simp only [← unpair'_eq_unpair]
  exact pair_unpair' n

end Nat
