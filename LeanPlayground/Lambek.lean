
/-!
# Lambek calculus

-/

-- Disable auto-binding of unbounded variables
set_option autoImplicit false

universe u

/-!
## Auxiliary declarations
-/

namespace List

variable {α : Type u}

theorem append_single_append_eq_single {l₁ l₂ : List α} {a b : α} (h : l₁ ++ [a] ++ l₂ = [b]) : l₁ = [] ∧ a = b ∧ l₂ = [] := by
  have : l₁ = [] := by
    cases l₁ with
    | nil => rfl
    | cons a' l' => simp at h
  cases this; simp at h ⊢
  exact h

theorem append_single_append_eq_append {l₁ l₂ l₁' l₂' : List α} {a : α} (h : l₁ ++ [a] ++ l₂ = l₁' ++ l₂') : ∃ l', (l₁ ++ [a] ++ l' = l₁' ∧ l₂ = l' ++ l₂') ∨ (l₁ = l₁' ++ l' ∧ l' ++ [a] ++ l₂ = l₂') := by
  induction l₁' generalizing l₁ l₂ with
  | nil =>
    exists l₁; exact Or.inr ⟨rfl,h⟩
  | cons b l₁' IH =>
    cases l₁ with
    | nil =>
      cases h; exists l₁'; exact Or.inl ⟨rfl,rfl⟩
    | cons c l₁ =>
      rewrite [cons_append, cons_append, cons_append, cons.injEq] at h
      cases h.1
      have ⟨l',hl'⟩ := IH h.2; clear IH h
      cases hl' with
      | inl hl' =>
        exists l'; refine Or.inl ⟨?_, hl'.2⟩
        simp only [cons_append, hl'.1]
      | inr hl' =>
        cases hl'.1; cases hl'.2; clear hl'
        simp only [cons_append, append_assoc, singleton_append, cons.injEq, true_and, append_cancel_left_eq, append_cancel_right_eq]
        exists l'; refine Or.inr ⟨rfl, rfl⟩

def accumNat (f : α → Nat) (l : List α) : Nat :=
  l.foldl (fun b a => b + f a) 0

@[simp]
theorem accumNat_nil {f : α → Nat} : accumNat f [] = 0 := rfl

@[simp]
theorem accumNat_single {f : α → Nat} {a : α} : accumNat f [a] = f a :=
  Nat.zero_add (f a)

@[simp]
theorem accumNat_cons {f : α → Nat} {a : α} {l : List α} : accumNat f (a :: l) = f a + accumNat f l := by
  unfold accumNat
  rewrite [foldl_cons, Nat.add_comm 0]
  generalize f a = b; generalize 0 = b'
  induction l generalizing b' with
  | nil => rfl
  | cons a l IH =>
    unfold foldl
    rewrite [Nat.add_assoc b b']
    exact IH (b' + f a)

theorem accumNat_append {f : α → Nat} {l₁ l₂ : List α} : accumNat f (l₁ ++ l₂) = accumNat f l₁ + accumNat f l₂ := by
  induction l₁ with
  | nil => rw [nil_append, accumNat_nil, Nat.zero_add]
  | cons a l₁ IH =>
    simp only [cons_append, accumNat_cons, Nat.add_assoc]
    exact congrArg (f a + ·) IH

end List


/-!
## Main declarations on Lambek calculus
-/

namespace Lambek

/--
In Lambek calculus, given a set `α` of ***primitives***, a ***type*** is generated by the following rules:

* a primitive is a type;
* if `X` and `Y` are types, then so are `X * Y`, `X / Y`, and `X ∖ Y`.

By definition, a type can be regarded as a binaryu tree each of whose nodes is labeled by one of the three operations.
-/
inductive Tp (α : Type u) : Type u where
| prim : α → Tp α
| conc : Tp α → Tp α → Tp α
| pref : Tp α → Tp α → Tp α
| suff : Tp α → Tp α → Tp α

namespace Tp

instance Tp.mul (α : Type u) : Mul (Tp α) := ⟨Tp.conc⟩
instance Tp.sdiff (α : Type u) : SDiff (Tp α) := ⟨Tp.pref⟩
instance Tp.div (α : Type u) : Div (Tp α) := ⟨Tp.suff⟩

variable {α : Type u}

/--
The number of binary operators (i.e. `*`, `/`, and `\`) in a type.
-/
def nops : Tp α → Nat
| .prim _ => 0
| .conc l r => l.nops + r.nops + 1
| .pref l r => l.nops + r.nops + 1
| .suff l r => l.nops + r.nops + 1

theorem nops_lt_pref_left (x y : Tp α) : x.nops < (x \ y).nops := by
  simp only [nops]; omega

theorem nops_lt_pref_right (x y : Tp α) : y.nops < (x \ y).nops := by
  simp only [nops]; omega

theorem nops_lt_suff_left (x y : Tp α) : x.nops < (x / y).nops := by
  simp only [nops]; omega

theorem nops_lt_suff_right (x y : Tp α) : y.nops < (x / y).nops := by
  simp only [nops]; omega

theorem nops_lt_conc_left (x y : Tp α) : x.nops < (x * y).nops := by
  simp only [nops]; omega

theorem nops_lt_conc_right (x y : Tp α) : y.nops < (x * y).nops := by
  simp only [nops]; omega

end Tp

/--
The deduction rules for Lambek calculus.

* The inductive generator does not contain the ***CUT*** rule since it is a theorem; see `Deducible.cut`.
* The ***ID*** rule is restricted to the case of primitives since the general case is a theorem; see `Deducible.refl`.
-/
inductive Deducible {α : Type u} : List (Tp α) → Tp α → Prop where
| id_prim (a : α) : Deducible [.prim a] (.prim a)
| pref_t {x y : Tp α} {c : List (Tp α)} : Deducible (x :: c) y → Deducible c (x \ y)
| pref_s (x y : Tp α) {z : Tp α} (c₁ c₂ c₃ : List (Tp α)) : Deducible c₂ x → Deducible (c₁ ++ [y] ++ c₃) z → Deducible (c₁ ++ c₂ ++ [x \ y] ++ c₃) z
| suff_t {x y : Tp α} {c : List (Tp α)} : Deducible (c ++ [x]) y → Deducible c (y / x)
| suff_s (x y : Tp α) {z : Tp α} (c₁ c₂ c₃ : List (Tp α)) : Deducible c₂ x → Deducible (c₁ ++ [y] ++ c₃) z → Deducible (c₁ ++ [y / x] ++ c₂ ++ c₃) z
| conc_t {x y : Tp α} (c₁ c₂ : List (Tp α)) : Deducible c₁ x → Deducible c₂ y → Deducible (c₁ ++ c₂) (x * y)
| conc_s (x y : Tp α) {z : Tp α} (c₁ c₂ : List (Tp α)) : Deducible (c₁ ++ [x,y] ++ c₂) z → Deducible (c₁ ++ [x*y] ++ c₂) z
--| cut {x y : Tp α} {c₁ c₂ c₃ : List (Tp α)} : Deducible c₂ x → Deducible (c₁ ++ [x] ++ c₃) y → Deducible (c₁ ++ c₂ ++ c₃) y

/--
`[x₁,…,xₙ] ⊩ x` asserts that it is deducible in the Lambek calculus.
The infix priority is determined in comparison with `∧` (prio:=35) and `∨` (prio:=30).
-/
scoped infix:25 " ⊩ " => Deducible


namespace Deducible

variable {α : Type u}

/-!
### Proof of the general ***ID*** rule

One can deduce the general ***ID*** rule from the version restricted to primitives.
-/

/--
The general version of ***ID*** rule; if `x` is a type, then `x ⊩ x` is derivable by a proof only with ***ID*** on primitives and without ***CUT***.
-/
protected theorem id (x : Tp α) : [x] ⊩ x := by
  induction x with
  | prim a => exact .id_prim a
  | conc l r IHl IHr =>
    exact .conc_s l r [] [] <| .conc_t [l] [r] IHl IHr
  | pref l r IHl IHr =>
    exact .pref_t <| .pref_s l r [] [l] [] IHl IHr
  | suff l r IHl IHr =>
    exact .suff_t <| .suff_s r l [] [r] [] IHr IHl


/-!
###  Proof of the ***CUT*** rule

We aim at the ***CUT*** rule.
-/

/--
The induction principle used in the proof of the `CUT` rule, that is the rule
```
cx ⊩ x   cy₁ ++ [x] ++ cy₂ ⊩ y
────────────────────────────────
    cy₁ ++ cx ++ cy₂ ⊩ y
```
We set the goal of the induction proof to be
```lean
let motive : Tp α → Tp α → List (Tp α) → List (Tp α) → Prop :=
  fun x y cx cy =>
    ∀ cy₁ cy₂, cy = cy₁ ++ [x] ++ cy₂ →
      cy₁ ++ cx ++ cy₂ ⊩ y
```
The induction principle for `motive x y cx cy` is based on the lexicographical combination of the following three induction principles in this order:

1. the structural induction on `x`;
2. the induction on the number of binary operators in `cx`;
3. the structural induction on the proof tree of `cy ⊩ y`.

The main difficulty is that, since `x` and `cy` are related in our goal `motive` above, the destruction of `x` may mess up induction steps, which prevents the third induction from being independent of the other two.
We hence need to deal with this interference by splitting the problem into the following cases.

* The ***ID*** rules (2 rules), i.e.
```lean
id_any : motive (.prim a) y [.prim a] cy
any_id : motive x (.prim a) cx [.prim a]
```

* The rules on the *source* `cx` (3 rules), e.g.
```lean
motive x y (cx₁ ++ [t] ++ cx₂) cy →
  motive x y (cx₁ ++ cs ++ [s \ t] ++ cx₂) cy
```

* The rules on the *target* `y` (3 rules), e.g.
```lean
motive x y cx (z :: cy) →
  motive x (z \ y) cx cy
```

* The interference cases (3 × 3 rules)
-/
theorem cut.induction_on
  {motive : Tp α → Tp α → List (Tp α) → List (Tp α) → Prop}
  {x y : Tp α} {cx cy : List (Tp α)} (hx : cx ⊩ x) (hy : cy ⊩ y)
  (id_any : (a : α) → (y : Tp α) → (c : List (Tp α)) → c ⊩ y → motive (.prim a) y [.prim a] c)
  (pref_s_any : (s t x y : Tp α) → (cs cx₁ cx₂ cy : List (Tp α)) → cs ⊩ s → cx₁ ++ [t] ++ cx₂ ⊩ x → cy ⊩ y → motive x y (cx₁ ++ [t] ++ cx₂) cy → motive x y (cx₁ ++ cs ++ [s \ t] ++ cx₂) cy)
  (suff_s_any : (s t x y : Tp α) → (ct cx₁ cx₂ cy : List (Tp α)) → ct ⊩ t → cx₁ ++ [s] ++ cx₂ ⊩ x → cy ⊩ y → motive x y (cx₁ ++ [s] ++ cx₂) cy → motive x y (cx₁ ++ [s / t] ++ ct ++ cx₂) cy)
  (conc_s_any : (s t x y : Tp α) → (cx₁ cx₂ cy : List (Tp α)) → cx₁ ++ [s,t] ++ cx₂ ⊩ x → cy ⊩ y → motive x y (cx₁ ++ [s,t] ++ cx₂) cy → motive x y (cx₁ ++ [s * t] ++ cx₂) cy)
  (any_id : (x : Tp α) → (a : α) → (c : List (Tp α)) → c ⊩ x → motive x (.prim a) c [.prim a])
  (any_pref_t : (x t y : Tp α) → (cx cy : List (Tp α)) → cx ⊩ x → t :: cy ⊩ y → motive x y cx (t :: cy) → motive x (t \ y) cx cy)
  (any_suff_t : (x y t : Tp α) → (cx cy : List (Tp α)) → cx ⊩ x → cy ++ [t] ⊩ y → motive x y cx (cy ++ [t]) → motive x (y / t) cx cy)
  (any_conc_t : (x y z : Tp α) → (cx cy cz : List (Tp α)) → cx ⊩ x → cy ⊩ y → cz ⊩ z → motive x y cx cy → motive x z cx cz → motive x (y * z) cx (cy ++ cz))
  (pref_t_pref_s : (t x w z y : Tp α) → (cx cw cy₁ cy₂ : List (Tp α)) → t :: cx ⊩ x → cw ⊩ w → cy₁ ++ [z] ++ cy₂ ⊩ y → (∀ ct cy, ct ⊩ t → cy ⊩ y → motive t y ct cy) → motive x y (t :: cx) (cy₁ ++ [z] ++ cy₂) → motive (t \ x) w cx cw → motive (t \ x) y cx (cy₁ ++ [z] ++ cy₂) → motive (t \ x) y cx (cy₁ ++ cw ++ [w \ z] ++ cy₂))
  (pref_t_suff_s : (t x w z y : Tp α) → (cx cz cy₁ cy₂ : List (Tp α)) → t :: cx ⊩ x → cz ⊩ z → cy₁ ++ [w] ++ cy₂ ⊩ y → motive (t \ x) z cx cz → motive (t \ x) y cx (cy₁ ++ [w] ++ cy₂) → motive (t \ x) y cx (cy₁ ++ [w / z] ++ cz ++ cy₂))
  (pref_t_conc_s : (t x w z y : Tp α) → (cx cy₁ cy₂ : List (Tp α)) → t :: cx ⊩ x → cy₁ ++ [w,z] ++ cy₂ ⊩ y → motive (t \ x) y cx (cy₁ ++ [w,z] ++ cy₂) → motive (t \ x) y cx (cy₁ ++ [w * z] ++ cy₂))
  (suff_t_pref_s : (x t w z y : Tp α) → (cx cw cy₁ cy₂ : List (Tp α)) → cx ++ [t] ⊩ x → cw ⊩ w → cy₁ ++ [z] ++ cy₂ ⊩ y → motive (x / t) w cx cw → motive (x / t) y cx (cy₁ ++ [z] ++ cy₂) → motive (x / t) y cx (cy₁ ++ cw ++ [w \ z] ++ cy₂))
  (suff_t_suff_s : (x t w z y : Tp α) → (cx cz cy₁ cy₂ : List (Tp α)) → cx ++ [t] ⊩ x → cz ⊩ z → cy₁ ++ [w] ++ cy₂ ⊩ y → (∀ ct cy, ct ⊩ t → cy ⊩ y → motive t y ct cy) → motive x y (cx ++ [t]) (cy₁ ++ [w] ++ cy₂) → motive (x / t) z cx cz → motive (x / t) y cx (cy₁ ++ [w] ++ cy₂) → motive (x / t) y cx (cy₁ ++ [w / z] ++ cz ++ cy₂))
  (suff_t_conc_s : (x t w z y : Tp α) → (cx cy₁ cy₂ : List (Tp α)) → cx ++ [t] ⊩ x → cy₁ ++ [w, z] ++ cy₂ ⊩ y → motive (x / t) y cx (cy₁ ++ [w, z] ++ cy₂) → motive (x / t) y cx (cy₁ ++ [w * z] ++ cy₂))
  (conc_t_pref_s : (x₁ x₂ w z y : Tp α) → (cx₁ cx₂ cw cy₁ cy₂ : List (Tp α)) → cx₁ ⊩ x₁ → cx₂ ⊩ x₂ → cw ⊩ w → cy₁ ++ [z] ++ cy₂ ⊩ y → motive (x₁ * x₂) w (cx₁ ++ cx₂) cw → motive (x₁ * x₂) y (cx₁ ++ cx₂) (cy₁ ++ [z] ++ cy₂) → motive (x₁ * x₂) y (cx₁ ++ cx₂) (cy₁ ++ cw ++ [w \ z] ++ cy₂))
  (conc_t_suff_s : (x₁ x₂ z w y : Tp α) → (cx₁ cx₂ cw cy₁ cy₂ : List (Tp α)) → cx₁ ⊩ x₁ → cx₂ ⊩ x₂ → cw ⊩ w → cy₁ ++ [z] ++ cy₂ ⊩ y → motive (x₁ * x₂) w (cx₁ ++ cx₂) cw → motive (x₁ * x₂) y (cx₁ ++ cx₂) (cy₁ ++ [z] ++ cy₂) → motive (x₁ * x₂) y (cx₁ ++ cx₂) (cy₁ ++ [z / w] ++ cw ++ cy₂))
  (conc_t_conc_s : (x₁ x₂ w z y : Tp α) → (cx₁ cx₂ cy₁ cy₂ : List (Tp α)) → cx₁ ⊩ x₁ → cx₂ ⊩ x₂ → cy₁ ++ [w, z] ++ cy₂ ⊩ y → (∀ t ct, ct ⊩ t → motive x₁ t cx₁ ct) → (∀ t ct, ct ⊩ t → motive x₂ t cx₂ ct) → motive (x₁ * x₂) y (cx₁ ++ cx₂) (cy₁ ++ [w,z] ++ cy₂) → motive (x₁ * x₂) y (cx₁ ++ cx₂) (cy₁ ++ [w*z] ++ cy₂))
  : motive x y cx cy := by
  generalize hn : x.nops = n
  induction n using Nat.strongInductionOn generalizing x y cx cy
  rename_i n IHx; cases hn
  generalize hn : cx.accumNat Tp.nops = n
  induction n using Nat.strongInductionOn generalizing cx y cy
  rename_i n IHcx'; cases hn
  have IHcx : ∀ {y : Tp α} (cx' : List (Tp α)) {cy : List (Tp α)}, cx' ⊩ x → cy ⊩ y → cx'.accumNat Tp.nops < cx.accumNat Tp.nops → motive x y cx' cy :=
    @fun y cx' cy hx hy h => IHcx' (cx'.accumNat Tp.nops) h hx hy rfl
  clear IHcx'
  cases hx with
  | id_prim a =>
    exact id_any a y cy hy
  | @pref_s s t x cx₁ cs cx₂ hs hx =>
    refine pref_s_any s t x y cs cx₁ cx₂ cy hs hx hy (IHcx _ hx hy ?_)
    simp only [List.accumNat_append, List.accumNat_single, Tp.nops]
    omega
  | @suff_s s t x cx₁ cs cx₂ ht hx =>
    refine suff_s_any t s x y cs cx₁ cx₂ cy ht hx hy (IHcx _ hx hy ?_)
    simp only [List.accumNat_append, List.accumNat_single, Tp.nops]
    omega
  | @conc_s s t x cx₁ cx₂ hx =>
    refine conc_s_any s t x y cx₁ cx₂ cy hx hy (IHcx _ hx hy ?_)
    simp only [List.accumNat_append, List.accumNat_cons, List.accumNat_nil, Tp.nops]
    omega
  | @pref_t t x cx hx =>
    have IHt : ∀ y ct cy, ct ⊩ t → cy ⊩ y → motive t y ct cy :=
      fun y ct cy ht hy => IHx t.nops (Tp.nops_lt_pref_left ..) ht hy rfl
    induction hy with
    | id_prim a => exact any_id _ a cx (.pref_t hx)
    | @pref_t z y cy hy IHy =>
      exact any_pref_t _ z y cx cy (.pref_t hx) hy IHy
    | @suff_t z y cy hy IHy =>
      exact any_suff_t _ y z cx cy (.pref_t hx) hy IHy
    | @conc_t y z cy cz hy hz IHy IHz =>
      exact any_conc_t _ y z cx cy cz (.pref_t hx) hy hz IHy IHz
    | @pref_s w z y cy₁ cw cy₂ hw hy IHw IHy =>
      refine pref_t_pref_s t x w z y cx cw cy₁ cy₂ hx hw hy (IHt y) ?_ IHw IHy
      exact IHx x.nops (Tp.nops_lt_pref_right ..) hx hy rfl
    | @suff_s w z y cy₁ cw cy₂ hw hy IHw IHy =>
      exact pref_t_suff_s t x z w y cx cw cy₁ cy₂ hx hw hy IHw IHy
    | @conc_s z w y cy₁ cy₂ hy IHy =>
      exact pref_t_conc_s t x z w y cx cy₁ cy₂ hx hy IHy
  | @suff_t t x cx hx =>
    have IHt : ∀ y ct cy, ct ⊩ t → cy ⊩ y → motive t y ct cy :=
      fun y ct cy ht hy => IHx t.nops (Tp.nops_lt_suff_right ..) ht hy rfl
    induction hy with
    | id_prim a => exact any_id _ a cx (.suff_t hx)
    | @pref_t z y cy hy IHy =>
      exact any_pref_t _ z y cx cy (.suff_t hx) hy IHy
    | @suff_t z y cy hy IHy =>
      exact any_suff_t _ y z cx cy (.suff_t hx) hy IHy
    | @conc_t y z cy cz hy hz IHy IHz =>
      exact any_conc_t _ y z cx cy cz (.suff_t hx) hy hz IHy IHz
    | @pref_s w z y cy₁ cw cy₂ hw hy IHw IHy =>
      exact suff_t_pref_s x t w z y cx cw cy₁ cy₂ hx hw hy IHw IHy
    | @suff_s w z y cy₁ cw cy₂ hw hy IHw IHy =>
      refine suff_t_suff_s x t z w y cx cw cy₁ cy₂ hx hw hy (IHt y) ?_ IHw IHy
      exact IHx x.nops (Tp.nops_lt_suff_left ..) hx hy rfl
    | @conc_s z w y cy₁ cy₂ hy IHy =>
      exact suff_t_conc_s x t z w y cx cy₁ cy₂ hx hy IHy
  | @conc_t t x ct cx ht hx =>
    induction hy with
    | id_prim a => exact any_id _ a _ (.conc_t ct cx ht hx)
    | @pref_t z y cy hy IHy =>
      exact any_pref_t _ z y _ cy (.conc_t ct cx ht hx) hy IHy
    | @suff_t z y cy hy IHy =>
      exact any_suff_t _ y z _ cy (.conc_t ct cx ht hx) hy IHy
    | @conc_t y z cy cz hy hz IHy IHz =>
      exact any_conc_t _ y z _ cy cz (.conc_t ct cx ht hx) hy hz IHy IHz
    | @pref_s w z y cy₁ cw cy₂ hw hy IHw IHy =>
      exact conc_t_pref_s t x w z y ct cx cw cy₁ cy₂ ht hx hw hy IHw IHy
    | @suff_s w z y cy₁ cw cy₂ hw hy IHw IHy =>
      exact conc_t_suff_s t x z w y ct cx cw cy₁ cy₂ ht hx hw hy IHw IHy
    | @conc_s z w y cy₁ cy₂ hy IHy =>
      refine conc_t_conc_s t x z w y ct cx cy₁ cy₂ ht hx hy ?_ ?_ IHy
      . intro w cw hw
        exact IHx t.nops (by simp only [Tp.nops]; omega) ht hw rfl
      . intro z cz hz
        exact IHx x.nops (by simp only [Tp.nops]; omega) hx hz rfl

/--
The proof of the ***CUT*** rule; i.e.
```
cx ⊩ x   cy₁ ++ [x] ++ cy₂ ⊩ y
────────────────────────────────
    cy₁ ++ cx ++ cy₂ ⊩ y
```
We use the induction principle `cut.induction` with
```lean
let motive x y cx cy :=
  ∀ cy₁ cy₂, cy = cy₁ ++ [x] ++ cy₂ →
    cy₁ ++ cx ++ cy₂ ⊩ y
```
-/
theorem cut {x y : Tp α} {c : List (Tp α)} (c₁ c₂ : List (Tp α)) (hx : c ⊩ x) (hy : (c₁ ++ [x] ++ c₂) ⊩ y) : (c₁ ++ c ++ c₂) ⊩ y := by
  apply cut.induction_on
    (motive:=fun x y cx cy =>
      ∀ cy₁ cy₂, cy = cy₁ ++ [x] ++ cy₂ → cy₁ ++ cx ++ cy₂ ⊩ y
    )
    hx hy
  rotate_right; rfl
  all_goals (clear hx hy x y c c₁ c₂)
  case id_any =>
    rintro a y _ hy cy₁ cy₂ rfl; exact hy
  case pref_s_any =>
    rintro s t x y cs cx₁ cx₂ _ hs _ hy IH cy₁ cy₂ rfl
    specialize IH cy₁ cy₂ rfl
    simp only [List.append_assoc] at IH ⊢
    generalize cx₂ ++ cy₂ = c₂ at IH ⊢
    simp only [←List.append_assoc] at IH ⊢
    exact .pref_s s t (cy₁ ++ cx₁) cs c₂ hs IH
  case suff_s_any =>
    rintro s t x y cs cx₁ cx₂ _ hs _ hy IH cy₁ cy₂ rfl
    specialize IH cy₁ cy₂ rfl
    simp only [List.append_assoc] at IH ⊢
    generalize cx₂ ++ cy₂ = c₂ at IH ⊢
    simp only [←List.append_assoc] at IH ⊢
    exact .suff_s t s (cy₁ ++ cx₁) cs c₂ hs IH
  case conc_s_any =>
    rintro s t x y cx₁ cx₂ _ _ hy IH cy₁ cy₂ rfl
    specialize IH cy₁ cy₂ rfl
    simp only [List.append_assoc] at IH ⊢
    generalize cx₂ ++ cy₂ = c₂ at IH ⊢
    simp only [←List.append_assoc] at IH ⊢
    exact .conc_s s t (cy₁ ++ cx₁) c₂ IH
  case any_id =>
    intro x a cx hx _ _ h
    rcases List.append_single_append_eq_single h.symm with ⟨rfl,⟨rfl,rfl⟩⟩
    simp only [List.append_nil, List.nil_append]
    exact hx
  case any_pref_t =>
    rintro x t y cx _ _ hy IH cy₁ cy₂ rfl
    exact .pref_t <| IH (t :: cy₁) cy₂ rfl
  case any_suff_t =>
    rintro x t y cx _ _ hy IH cy₁ cy₂ rfl
    refine .suff_t <| List.append_assoc .. ▸ IH cy₁ (cy₂ ++ [y]) ?_
    simp only [List.append_assoc]
  case any_conc_t =>
    intro x y z cx cy cz _ hy hz IHy IHz c₁ c₂ hc
    rcases List.append_single_append_eq_append hc.symm with ⟨c, (hc | hc)⟩
    all_goals (rcases hc with ⟨rfl, rfl⟩; clear hc)
    . simp only [← List.append_assoc]
      exact .conc_t _ _ (IHy c₁ c rfl) hz
    . have := Deducible.conc_t _ _ hy (IHz c c₂ rfl)
      simp only [← List.append_assoc] at this
      exact this
  case pref_t_pref_s =>
    intro t x w z y cx cw cy₁ cy₂ _ hw hy IHt IHy IHw' IHy' cy₁' cy₂' hc
    rcases List.append_single_append_eq_append hc.symm with ⟨c, (⟨hc,hcy₂⟩ | ⟨rfl,rfl⟩)⟩
    rcases List.append_single_append_eq_append hc with ⟨c', (⟨hc,hc'⟩ | ⟨rfl,htz⟩)⟩
    rcases List.append_single_append_eq_append hc with ⟨c'', (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩
    all_goals repeat clear hc
    . cases hc'; cases hcy₂
      simp only [← List.append_assoc]
      refine .pref_s w z (cy₁' ++ cx ++ c'') cw cy₂ hw ?_
      specialize IHy' cy₁' (c'' ++ [z] ++ cy₂)
      simp only [← List.append_assoc, true_implies] at IHy'
      exact IHy'
    . cases hc'; cases hcy₂
      simp only [← List.append_assoc]
      iterate 2 rewrite [List.append_assoc cy₁]
      exact .pref_s w z cy₁ (c'' ++ cx ++ c') cy₂ (IHw' c'' c' rfl) hy
    . rcases List.append_single_append_eq_single htz with ⟨rfl,⟨rfl,rfl⟩,rfl⟩
      simp only [List.append_nil, List.nil_append] at *
      cases hcy₂; clear htz
      specialize IHy cy₁ cy₂ rfl
      rewrite [List.append_assoc _ _ cy₂]
      apply IHt _ _ hw IHy
      simp only [List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
    . rewrite [List.append_assoc, List.append_assoc]
      refine .pref_s w z cy₁ cw _ hw ?_
      simp only [← List.append_assoc]
      apply IHy'; simp only [List.append_assoc]
  case pref_t_suff_s =>
    intro t x w z y cx cz cy₁ cy₂ _ hz hy IHz IHy cy₁' cy₂' hc
    rcases List.append_single_append_eq_append hc.symm with ⟨c, (⟨hc,hcy₂⟩ | ⟨rfl,rfl⟩)⟩
    rcases List.append_single_append_eq_append hc with ⟨c', (⟨hc,hc'⟩ | ⟨rfl,rfl⟩)⟩
    rcases List.append_single_append_eq_append hc with ⟨c'', (⟨rfl,rfl⟩ | ⟨rfl,htz'⟩)⟩
    all_goals repeat clear hc
    . cases hcy₂; cases hc'
      specialize IHy cy₁' (c'' ++ [w] ++ cy₂)
      simp only [← List.append_assoc, true_implies] at IHy ⊢
      refine .suff_s z w _ cz cy₂ hz IHy
    . nomatch List.append_single_append_eq_single htz'
    . cases hcy₂
      specialize IHz c' c rfl
      rewrite [← List.append_assoc, List.append_assoc _ _ c, List.append_assoc _ _ (cx ++ c), ←List.append_assoc c']
      refine .suff_s z w cy₁ _ cy₂ IHz hy
    . rewrite [List.append_assoc, List.append_assoc, ← List.append_assoc c]
      specialize IHy (cy₁ ++ [w] ++ c) cy₂'
      refine .suff_s z w cy₁ cz (c ++ cx ++ cy₂') hz ?_
      simp only [← List.append_assoc, true_implies] at IHy ⊢
      exact IHy
  case pref_t_conc_s =>
    intro t x w z y cx cy₁ cy₂ _ hy IHy cy₁' cy₂' hc
    rcases List.append_single_append_eq_append hc with ⟨c, (⟨hc,hcy₂⟩ | ⟨rfl,rfl⟩)⟩
    rcases List.append_single_append_eq_append hc with ⟨c', (⟨rfl,rfl⟩ | ⟨rfl,htz⟩)⟩
    all_goals repeat clear hc
    . cases hcy₂
      specialize IHy (cy₁ ++ [w,z] ++ c') cy₂'
      rewrite [List.append_assoc, List.append_assoc]
      refine .conc_s w z  cy₁ _ ?_
      simp only [List.append_assoc, true_implies] at IHy ⊢
      exact IHy
    . nomatch (List.append_single_append_eq_single htz).2.1
    . specialize IHy cy₁' (c ++ [w,z] ++ cy₂)
      simp only [← List.append_assoc, true_implies] at IHy ⊢
      exact .conc_s w z _ _ IHy
  case suff_t_pref_s =>
    intro x t w z y cx cw cy₁ cy₂ _ hw hy IHw IHy cy₁' cy₂' hc
    rcases List.append_single_append_eq_append hc.symm with ⟨c, (⟨hc,hcy₂⟩ | ⟨rfl,rfl⟩)⟩
    rcases List.append_single_append_eq_append hc with ⟨c', (⟨hc,hc'⟩ | ⟨rfl,htz⟩)⟩
    rcases List.append_single_append_eq_append hc with ⟨c'', (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩
    all_goals repeat clear hc
    . cases hcy₂; cases hc'
      specialize IHy cy₁' (c'' ++ [z] ++ cy₂)
      simp only [← List.append_assoc, true_implies] at IHy ⊢
      refine .pref_s w z _ cw cy₂ hw IHy
    . cases hcy₂; cases hc'
      have := Deducible.pref_s w z cy₁ _ cy₂ (IHw c'' c' rfl) hy
      simp only [← List.append_assoc] at this ⊢
      exact this
    . nomatch (List.append_single_append_eq_single htz).2.1
    . specialize IHy (cy₁ ++ [z] ++ c) cy₂'
      simp only [List.append_assoc (_ ++ _), true_implies] at IHy
      simp only [List.append_assoc (_ ++ _ ++ _)]
      exact .pref_s w z _ cw _ hw IHy
  case suff_t_suff_s =>
    intro x t w z y cx cz cy₁ cy₂ _ hz hy IHt IHy IHz IHy' cy₁' cy₂' hc
    rcases List.append_single_append_eq_append hc.symm with ⟨c, (⟨hc,hcy₂⟩ | ⟨rfl,rfl⟩)⟩
    rcases List.append_single_append_eq_append hc with ⟨c', (⟨hc,hc'⟩ | ⟨rfl,rfl⟩)⟩
    rcases List.append_single_append_eq_append hc with ⟨c'', (⟨rfl,rfl⟩ | ⟨rfl,htz⟩)⟩
    all_goals repeat clear hc
    . cases hcy₂; cases hc'
      specialize IHy' cy₁' (c'' ++ [w] ++ cy₂)
      simp only [← List.append_assoc, true_implies] at IHy'
      have := Deducible.suff_s z w _ cz cy₂ hz IHy'
      simp only [← List.append_assoc]
      exact this
    . cases hcy₂; cases hc'
      rcases List.append_single_append_eq_single htz with ⟨rfl,⟨rfl,rfl⟩,rfl⟩
      clear htz; simp only [List.append_nil, List.nil_append] at *
      specialize IHt cz _ hz (IHy cy₁ cy₂ rfl) (cy₁ ++ cx) cy₂
      simp only [← List.append_assoc, true_implies] at IHt ⊢
      exact IHt
    . cases hcy₂
      specialize IHz c' c rfl
      have := Deducible.suff_s z w cy₁ _ cy₂ IHz hy
      simp only [← List.append_assoc] at this ⊢
      exact this
    . specialize IHy' (cy₁ ++ [w] ++ c) cy₂' (by simp only [List.append_assoc])
      simp only [List.append_assoc (_ ++ _)] at IHy'
      have := Deducible.suff_s z w cy₁ _ _ hz IHy'
      simp only [← List.append_assoc] at this
      exact this
  case suff_t_conc_s =>
    intro x t w z y cx cy₁ cy₂ _ hy IHy cy₁' cy₂' hc
    rcases List.append_single_append_eq_append hc.symm with ⟨c, (⟨hc,hcy₂⟩ | ⟨rfl,rfl⟩)⟩
    rcases List.append_single_append_eq_append hc with ⟨c', (⟨rfl,rfl⟩ | ⟨rfl,hxt⟩)⟩
    all_goals repeat clear hc
    . cases hcy₂
      specialize IHy cy₁' (c' ++ [w, z] ++ cy₂)
      simp only [← List.append_assoc, true_implies] at IHy ⊢
      exact .conc_s w z _ cy₂ IHy
    . nomatch (List.append_single_append_eq_single hxt).2.1
    . specialize IHy (cy₁ ++ [w,z] ++ c) cy₂'
      simp only [List.append_assoc (_ ++ _), true_implies] at IHy ⊢
      exact .conc_s w z cy₁ _ IHy
  case conc_t_pref_s =>
    intro x₁ x₂ w z y cx₁ cx₂ cw cy₁ cy₂ _ _ hw hy IHw IHy cy₁' cy₂' hc
    rcases List.append_single_append_eq_append hc.symm with ⟨c, (⟨hc,hcy₂⟩ | ⟨rfl,rfl⟩)⟩
    rcases List.append_single_append_eq_append hc with ⟨c', (⟨hc,hc'⟩ | ⟨rfl,hwz⟩)⟩
    rcases List.append_single_append_eq_append hc with ⟨c'', (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)⟩
    all_goals repeat clear hc
    . cases hcy₂; cases hc'
      specialize IHy cy₁' (c'' ++ [z] ++ cy₂)
      simp only [← List.append_assoc, true_implies] at IHy ⊢
      exact .pref_s w z _ cw cy₂ hw IHy
    . cases hcy₂; cases hc'
      specialize IHw c'' c' rfl
      have := Deducible.pref_s w z cy₁ _ cy₂ IHw hy
      simp only [← List.append_assoc] at this ⊢
      exact this
    . nomatch (List.append_single_append_eq_single hwz).2.1
    . specialize IHy (cy₁ ++ [z] ++ c) cy₂'
      simp only [List.append_assoc (_ ++ _), true_implies] at IHy
      have := Deducible.pref_s w z cy₁ cw _ hw IHy
      simp only [← List.append_assoc] at this ⊢
      exact this
  case conc_t_suff_s =>
    intro x₁ x₂ z w y cx₁ cx₂ cw cy₁ cy₂ _ _ hw hy IHw IHy cy₁' cy₂' hc
    rcases List.append_single_append_eq_append hc.symm with ⟨c, (⟨hc,hcy₂⟩ | ⟨rfl,rfl⟩)⟩
    rcases List.append_single_append_eq_append hc with ⟨c', (⟨hc,hc'⟩ | ⟨rfl,rfl⟩)⟩
    rcases List.append_single_append_eq_append hc with ⟨c'', (⟨rfl,rfl⟩ | ⟨rfl,hzw⟩)⟩
    all_goals repeat clear hc
    . cases hcy₂; cases hc'
      specialize IHy cy₁' (c'' ++ [z] ++ cy₂)
      simp only [← List.append_assoc, true_implies] at IHy ⊢
      exact .suff_s w z _ cw _ hw IHy
    . nomatch (List.append_single_append_eq_single hzw).2.1
    . cases hcy₂
      specialize IHw c' c rfl
      have := Deducible.suff_s w z cy₁ _ cy₂ IHw hy
      simp only [← List.append_assoc] at this ⊢
      exact this
    . specialize IHy (cy₁ ++ [z] ++ c) cy₂'
      simp only [List.append_assoc (_ ++ _), true_implies] at IHy
      have := Deducible.suff_s w z cy₁ cw _ hw IHy
      simp only [← List.append_assoc] at this ⊢
      exact this
  case conc_t_conc_s =>
    intro x₁ x₂ w z y cx₁ cx₂ cy₁ cy₂ _ _ hy IH₁ IH₂ IHy cy₁' cy₂' hc
    rcases List.append_single_append_eq_append hc with ⟨c, (⟨hc,hcy₂⟩ | ⟨rfl,rfl⟩)⟩
    rcases List.append_single_append_eq_append hc with ⟨c', (⟨rfl,rfl⟩ | ⟨rfl,hwz⟩)⟩
    all_goals repeat clear hc
    . cases hcy₂
      specialize IHy (cy₁ ++ [w,z] ++ c') cy₂'
      simp only [List.append_assoc (_ ++ _), true_implies] at IHy ⊢
      exact .conc_s w z cy₁ _ IHy
    . cases hcy₂
      rcases List.append_single_append_eq_single hwz with ⟨rfl,⟨rfl,rfl⟩,rfl⟩
      clear hwz; simp only [List.nil_append, List.append_nil] at *
      rewrite [show [x₁,x₂] = [x₁] ++ [x₂] by rfl] at hy
      simp only [← List.append_assoc] at hy
      specialize IH₂ y _ hy (cy₁' ++ [x₁]) cy₂' rfl
      rewrite [List.append_assoc] at IH₂
      specialize IH₁ y _ IH₂ cy₁' (cx₂ ++ cy₂') rfl
      simp only [← List.append_assoc] at IH₁ ⊢
      exact IH₁
    . specialize IHy cy₁' (c ++ [w,z] ++ cy₂)
      simp only [← List.append_assoc, true_implies] at IHy ⊢
      exact .conc_s w z _ cy₂ IHy

end Deducible


/-!
### Examples
-/

example {α : Type u} (x y : Tp α) : [x] ⊩ ((y / x) \ y) := by
  refine .pref_t ?_
  exact .suff_s x y [] [x] [] (.id x) (.id y)

example {α : Type u} (a : α) (y : Tp α) : [y, y \ .prim a] ⊩ .prim a := by
  exact .pref_s y (.prim a) [] [y] [] (.id y) (.id_prim a)

end Lambek