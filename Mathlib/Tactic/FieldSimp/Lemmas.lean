/-
Copyright (c) 2025 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Arend Mellendijk, Michael Rothgang
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Field.Power

/-! # Lemmas for the field_simp tactic

-/

open List

section zpow'
variable {α : Type*}

section
variable [GroupWithZero α]

open Classical in
noncomputable def zpow' (a : α) (n : ℤ) : α :=
  if a = 0 ∧ n = 0 then 0 else a ^ n

theorem zpow'_add (a : α) (m n : ℤ) :
    zpow' a (m + n) = zpow' a m * zpow' a n := by
  by_cases ha : a = 0
  · simp [zpow', ha]
    by_cases hn : n = 0
    · simp +contextual [hn, zero_zpow]
    · simp +contextual [hn, zero_zpow]
  · simp [zpow', ha, zpow_add₀]

theorem zpow'_of_ne_zero_right (a : α) (n : ℤ) (hn : n ≠ 0) : zpow' a n = a ^ n := by
  simp [zpow', hn]

@[simp]
lemma zero_zpow' (n : ℤ) : zpow' (0 : α) n = 0 := by
  simp +contextual only [zpow', true_and, ite_eq_left_iff]
  intro hn
  exact zero_zpow n hn

lemma zpow'_eq_zero_iff (a : α) (n : ℤ) : zpow' a n = 0 ↔ a = 0 := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [zpow']
  · simp [zpow', zpow_eq_zero_iff hn]
    tauto

@[simp]
lemma one_zpow' (n : ℤ) : zpow' (1 : α) n = 1 := by
  simp [zpow']

@[simp]
lemma zpow'_one (a : α) : zpow' a 1 = a := by
  simp [zpow']

lemma zpow'_zero_eq_div (a : α) : zpow' a 0 = a / a := by
  simp [zpow']
  by_cases h : a = 0
  · simp [h]
  · simp [h]

lemma zpow'_zero_of_ne_zero {a : α} (ha : a ≠ 0) : zpow' a 0 = 1 := by simp [zpow', ha]

lemma zpow'_neg (a : α) (n : ℤ) : zpow' a (-n) = (zpow' a n)⁻¹ := by
  simp +contextual [zpow', apply_ite]
  split_ifs with h
  · tauto
  · tauto

lemma zpow'_mul (a : α) (m n : ℤ) : zpow' a (m * n) = zpow' (zpow' a m) n := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hn : n = 0
  · rw [hn]
    simp [zpow', ha, zpow_ne_zero ]
  by_cases hm : m = 0
  · rw [hm]
    simp [zpow', ha]
  simp [zpow', ha, hm, hn]
  exact zpow_mul a m n

lemma zpow'_ofNat (a : α) {n : ℕ} (hn : n ≠ 0) : zpow' a n = a ^ n := by
  rw [zpow'_of_ne_zero_right]
  · simp
  exact_mod_cast hn

end

lemma mul_zpow' [CommGroupWithZero α] (n : ℤ) (a b : α) :
    zpow' (a * b) n = zpow' a n * zpow' b n := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  simp [zpow', ha, hb]
  exact mul_zpow a b n

end zpow'

namespace List
variable {M : Type*}

def prod' {M : Type*} [Mul M] [One M] : List M → M := foldr (fun a t ↦ t * a) 1

@[simp]
theorem prod'_cons [Mul M] [One M] {a} {l : List M} : (a :: l).prod' = l.prod' * a := rfl

@[simp]
theorem prod'_nil [Mul M] [One M] : (([] : List M)).prod' = 1 := rfl

-- generalize library `List.prod_inv`
theorem prod'_inv₀ {K : Type*} [DivisionCommMonoid K] :
    ∀ (L : List K), L.prod'⁻¹ = (map (fun x ↦ x⁻¹) L).prod'
  | [] => by simp
  | x :: xs => by simp [mul_comm, prod'_inv₀ xs]

theorem prod'_hom {M : Type*} {N : Type*} [Monoid M] [Monoid N] (l : List M) {F : Type*}
    [FunLike F M N] [MonoidHomClass F M N] (f : F) : (map f l).prod' = f l.prod' := by
  simp only [prod', foldr_map, ← map_one f]
  exact l.foldr_hom f (fun x y => (map_mul f y x).symm)

theorem _root_.map_list_prod' {M : Type*} {N : Type*} [Monoid M] [Monoid N] {F : Type*}
    [FunLike F M N] [MonoidHomClass F M N] (f : F) (l : List M) :
    f l.prod' = (map (⇑f) l).prod' :=
  (l.prod'_hom f).symm

-- in the library somewhere?
theorem prod'_zpow' {β : Type*} [CommGroupWithZero β] {r : ℤ} {l : List β} :
    zpow' l.prod' r = (map (fun x ↦ zpow' x r) l).prod' :=
  let fr : β →* β := ⟨⟨fun b ↦ zpow' b r, one_zpow' r⟩, (mul_zpow' r)⟩
  map_list_prod' fr l

-- Do we need the ℕ exponent at all?
-- in the library somewhere?
theorem _root_.List.prod'_pow {β : Type*} [CommMonoid β] {r : ℕ} {l : List β} :
    l.prod' ^ r = (map (fun x ↦ x ^ r) l).prod' :=
  let fr : β →* β := ⟨⟨fun b ↦ b ^ r, one_pow r⟩, (mul_pow · · r)⟩
  map_list_prod' fr l

end List

namespace Mathlib.Tactic.FieldSimp

theorem subst_add00 {M : Type*} [Semiring M] {x₁ x₂ x₁' x₂' X₁ X₂ X₁' X₂' a y : M}
    (h₁ : x₁ = X₁) (h₂ : x₂ = X₂)
    (h₁' : a * X₁' = X₁) (h₂' : a * X₂' = X₂)
    (h₁'' : X₁' = x₁') (h₂'' : X₂' = x₂')
    (H_atom : x₁' + x₂' = y) :
    x₁ + x₂ = a * y := by
  subst h₁ h₂ h₁' h₂' h₁'' h₂'' H_atom
  simp [mul_add]

theorem subst_add01 {M : Type*} [Field M] {x₁ x₂ x₁' x₂' X₁ X₂ X₁' X₂' a y : M}
    (h₁ : x₁ = X₁) (h₂ : x₂ = -X₂)
    (h₁' : a * X₁' = X₁) (h₂' : a * X₂' = X₂)
    (h₁'' : X₁' = x₁') (h₂'' : X₂' = x₂')
    (H_atom : x₁' + -x₂' = y) :
    x₁ + x₂ = a * y := by
  subst h₁ h₂ h₁' h₂' h₁'' h₂'' H_atom
  simp [mul_add, mul_neg]

theorem subst_add10 {M : Type*} [Field M] {x₁ x₂ x₁' x₂' X₁ X₂ X₁' X₂' a y : M}
    (h₁ : x₁ = -X₁) (h₂ : x₂ = X₂)
    (h₁' : a * X₁' = X₁) (h₂' : a * X₂' = X₂)
    (h₁'' : X₁' = x₁') (h₂'' : X₂' = x₂')
    (H_atom : -x₁' + x₂' = y) :
    x₁ + x₂ = a * y := by
  subst h₁ h₂ h₁' h₂' h₁'' h₂'' H_atom
  simp [mul_add, mul_neg]

theorem subst_add11 {M : Type*} [Field M] {x₁ x₂ x₁' x₂' X₁ X₂ X₁' X₂' a y : M}
    (h₁ : x₁ = -X₁) (h₂ : x₂ = -X₂)
    (h₁' : a * X₁' = X₁) (h₂' : a * X₂' = X₂)
    (h₁'' : X₁' = x₁') (h₂'' : X₂' = x₂')
    (H_atom : -x₁' + -x₂' = y) :
    x₁ + x₂ = a * y := by
  subst h₁ h₂ h₁' h₂' h₁'' h₂'' H_atom
  simp [mul_add, mul_neg]

theorem subst_sub00 {M : Type*} [Ring M] {x₁ x₂ x₁' x₂' X₁ X₂ X₁' X₂' a y : M}
    (h₁ : x₁ = X₁) (h₂ : x₂ = X₂)
    (h₁' : a * X₁' = X₁) (h₂' : a * X₂' = X₂)
    (h₁'' : X₁' = x₁') (h₂'' : X₂' = x₂')
    (H_atom : x₁' - x₂' = y) :
    x₁ - x₂ = a * y := by
  subst h₁ h₂ h₁' h₂' h₁'' h₂'' H_atom
  simp [mul_sub]

theorem subst_sub01 {M : Type*} [Field M] {x₁ x₂ x₁' x₂' X₁ X₂ X₁' X₂' a y : M}
    (h₁ : x₁ = X₁) (h₂ : x₂ = -X₂)
    (h₁' : a * X₁' = X₁) (h₂' : a * X₂' = X₂)
    (h₁'' : X₁' = x₁') (h₂'' : X₂' = x₂')
    (H_atom : x₁' - -x₂' = y) :
    x₁ - x₂ = a * y := by
  subst h₁ h₂ h₁' h₂' h₁'' h₂'' H_atom
  simp [mul_add]

theorem subst_sub10 {M : Type*} [Field M] {x₁ x₂ x₁' x₂' X₁ X₂ X₁' X₂' a y : M}
    (h₁ : x₁ = -X₁) (h₂ : x₂ = X₂)
    (h₁' : a * X₁' = X₁) (h₂' : a * X₂' = X₂)
    (h₁'' : X₁' = x₁') (h₂'' : X₂' = x₂')
    (H_atom : -x₁' - x₂' = y) :
    x₁ - x₂ = a * y := by
  subst h₁ h₂ h₁' h₂' h₁'' h₂'' H_atom
  simp [mul_sub]

theorem subst_sub11 {M : Type*} [Field M] {x₁ x₂ x₁' x₂' X₁ X₂ X₁' X₂' a y : M}
    (h₁ : x₁ = -X₁) (h₂ : x₂ = -X₂)
    (h₁' : a * X₁' = X₁) (h₂' : a * X₂' = X₂)
    (h₁'' : X₁' = x₁') (h₂'' : X₂' = x₂')
    (H_atom : -x₁' - -x₂' = y) :
    x₁ - x₂ = a * y := by
  subst h₁ h₂ h₁' h₂' h₁'' h₂'' H_atom
  simp [mul_add]

theorem subst_neg {M : Type*} [Field M] {x negOne X X' : M}
    (pf : x = X)
    (pf_negOne : -1 = negOne)
    (pf' : X * negOne = X') :
    -x = X' := by
  rw [pf, ← pf', ← pf_negOne]
  rw [mul_neg, mul_one]

theorem eq_div_of_eq_one_of_subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1)
    (hn : l_n = n) :
    l = n := by
  rw [h, hn, div_one]

theorem eq_div_of_eq_one_of_subst' {M : Type*} [DivInvOneMonoid M] {l l_d d : M} (h : l = 1 / l_d)
    (hn : l_d = d) :
    l = d⁻¹ := by
  rw [h, hn, one_div]

theorem eq_div_of_subst {M : Type*} [Div M] {l l_n l_d n d : M} (h : l = l_n / l_d) (hn : l_n = n)
    (hd : l_d = d) :
    l = n / d := by
  rw [h, hn, hd]

theorem eq_of_eq_mul {M : Type*} [Mul M] {x₁ x₂ x₁' x₂' X₁ X₁' X₂ X₂' d : M}
    (h₁ : x₁ = X₁) (h₂ : x₂ = X₂) (h₁' : d * X₁' = X₁) (h₂' : d * X₂' = X₂)
    (h₁'' : X₁' = x₁') (h₂'' : X₂' = x₂') (h : x₁' = x₂') :
    x₁ = x₂ := by
  rw [h₁, h₂, ← h₁', ← h₂', h₁'', h₂'', h]

theorem eq_eq_cancel_eq00 {M : Type*} [CancelMonoidWithZero M] {e₁ e₂ f₁ f₂ l₁ l₂ l₁' l₂' L : M}
    (h₁ : e₁ = l₁) (h₂ : e₂ = l₂)
    (h₁' : l₁' = f₁) (h₂' : l₂' = f₂)
    (HL : L ≠ 0)
    (H₁ : L * l₁' = l₁) (H₂ : L * l₂' = l₂) :
    (e₁ = e₂) = (f₁ = f₂) := by
  subst h₁ h₂ h₁' h₂' H₁ H₂
  rw [mul_right_inj' HL]

theorem eq_eq_cancel_eq01 {M : Type*} [Field M] {e₁ e₂ f₁ f₂ l₁ l₂ l₁' l₂' L : M}
    (h₁ : e₁ = l₁) (h₂ : e₂ = -l₂)
    (h₁' : l₁' = f₁) (h₂' : l₂' = f₂)
    (HL : L ≠ 0)
    (H₁ : L * l₁' = l₁) (H₂ : L * l₂' = l₂) :
    (e₁ = e₂) = (f₁ = -f₂) := by
  subst h₁ h₂ h₁' h₂' H₁ H₂
  rw [← mul_neg]
  rw [mul_right_inj' HL]

theorem eq_eq_cancel_eq10 {M : Type*} [Field M] {e₁ e₂ f₁ f₂ l₁ l₂ l₁' l₂' L : M}
    (h₁ : e₁ = -l₁) (h₂ : e₂ = l₂)
    (h₁' : l₁' = f₁) (h₂' : l₂' = f₂)
    (HL : L ≠ 0)
    (H₁ : L * l₁' = l₁) (H₂ : L * l₂' = l₂) :
    (e₁ = e₂) = (-f₁ = f₂) := by
  subst h₁ h₂ h₁' h₂' H₁ H₂
  rw [← mul_neg]
  rw [mul_right_inj' HL]

theorem eq_eq_cancel_eq11 {M : Type*} [Field M] {e₁ e₂ f₁ f₂ l₁ l₂ l₁' l₂' L : M}
    (h₁ : e₁ = -l₁) (h₂ : e₂ = -l₂)
    (h₁' : l₁' = f₁) (h₂' : l₂' = f₂)
    (HL : L ≠ 0)
    (H₁ : L * l₁' = l₁) (H₂ : L * l₂' = l₂) :
    (e₁ = e₂) = (-f₁ = -f₂) := by
  subst h₁ h₂ h₁' h₂' H₁ H₂
  rw [← mul_neg, ← mul_neg]
  rw [mul_right_inj' HL]

/-! ### Theory of lists of pairs (exponent, atom)

This section contains the lemmas which are orchestrated by the `field_simp` tactic
to prove goals in fields.  The basic object which these lemmas concern is `NF M`, a type synonym
for a list of ordered pairs in `ℤ × M`, where typically `M` is a field.
-/

/-- Basic theoretical "normal form" object of the `field_simp` tactic: a type
synonym for a list of ordered pairs in `ℤ × M`, where typically `M` is a field.  This is the
form to which the tactics reduce field expressions. -/
def NF (M : Type*) := List (ℤ × M)

namespace NF
variable {M : Type*}

/-- Augment a `FieldSimp.NF M` object `l`, i.e. a list of pairs in `ℤ × M`, by prepending another
pair `p : ℤ × M`. -/
@[match_pattern]
def cons (p : ℤ × M) (l : NF M) : NF M := p :: l

@[inherit_doc cons] infixl:100 " ::ᵣ " => cons

/-- Evaluate a `FieldSimp.NF M` object `l`, i.e. a list of pairs in `ℤ × M`, to an element of `M`,
by forming the "multiplicative linear combination" it specifies: raise each `M` term to the power of
the corresponding `ℤ` term, then multiply them all together. -/
noncomputable def eval [GroupWithZero M] (l : NF M) : M :=
  (l.map (fun (⟨r, x⟩ : ℤ × M) ↦ zpow' x r)).prod'

@[simp] theorem eval_cons [GroupWithZero M] (p : ℤ × M) (l : NF M) :
    (p ::ᵣ l).eval = l.eval * zpow' p.2 p.1 := by
  unfold eval cons
  rw [List.map_cons]
  rw [List.prod'_cons]

theorem cons_ne_zero [GroupWithZero M] (r : ℤ) {x : M} (hx : x ≠ 0) {l : NF M} (hl : l.eval ≠ 0) :
    ((r, x) ::ᵣ l).eval ≠ 0 := by
  rw [eval_cons]
  apply mul_ne_zero hl
  simp [zpow'_eq_zero_iff, hx]

theorem atom_eq_eval [GroupWithZero M] (x : M) : x = NF.eval [(1, x)] := by simp [eval]

variable (M) in
theorem one_eq_eval [GroupWithZero M] : (1:M) = NF.eval (M := M) [] := rfl

theorem mul_eq_eval₁ [CommGroupWithZero M] (a₁ : ℤ × M) {a₂ : ℤ × M} {l₁ l₂ l : NF M}
    (h : l₁.eval * (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval * (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, mul_assoc]
  congr! 1
  rw [mul_comm, mul_assoc]

theorem mul_eq_eval₂ [CommGroupWithZero M] (r₁ r₂ : ℤ) (x : M) {l₁ l₂ l : NF M}
    (h : l₁.eval * l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval * ((r₂, x) ::ᵣ l₂).eval = ((r₁ + r₂, x) ::ᵣ l).eval := by
  simp [zpow'_add, ← h]
  rw [mul_assoc, mul_comm (zpow' _ _), mul_assoc, mul_comm (zpow' _ _), mul_assoc]

theorem mul_eq_eval₃ [GroupWithZero M] {a₁ : ℤ × M} (a₂ : ℤ × M) {l₁ l₂ l : NF M}
    (h : (a₁ ::ᵣ l₁).eval * l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval * (a₂ ::ᵣ l₂).eval = (a₂ ::ᵣ l).eval := by
  simp [← h]
  simp only [mul_assoc]

theorem mul_eq_eval00 [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
    (hx₂ : x₂ = l₂.eval) (h : l₁.eval * l₂.eval = l.eval) :
    x₁ * x₂ = l.eval := by
  rw [hx₁, hx₂, h]

theorem mul_eq_eval01 [DivisionRing M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
    (hx₂ : x₂ = -l₂.eval) (h : l₁.eval * l₂.eval = l.eval) :
    x₁ * x₂ = -l.eval := by
  rw [hx₁, hx₂, ← h, mul_neg]

theorem mul_eq_eval10 [DivisionRing M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = -l₁.eval)
    (hx₂ : x₂ = l₂.eval) (h : l₁.eval * l₂.eval = l.eval) :
    x₁ * x₂ = -l.eval := by
  rw [hx₁, hx₂, ← h, neg_mul]

theorem mul_eq_eval11 [DivisionRing M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = -l₁.eval)
    (hx₂ : x₂ = -l₂.eval) (h : l₁.eval * l₂.eval = l.eval) :
    x₁ * x₂ = l.eval := by
  rw [hx₁, hx₂, ← h, neg_mul_neg]

theorem div_eq_eval₁ [CommGroupWithZero M] (a₁ : ℤ × M) {a₂ : ℤ × M} {l₁ l₂ l : NF M}
    (h : l₁.eval / (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval / (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, div_eq_mul_inv, mul_assoc]
  congr! 1
  rw [mul_comm]

theorem div_eq_eval₂ [CommGroupWithZero M] (r₁ r₂ : ℤ) (x : M) {l₁ l₂ l : NF M}
    (h : l₁.eval / l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval / ((r₂, x) ::ᵣ l₂).eval = ((r₁ - r₂, x) ::ᵣ l).eval := by
  simp only [← h, eval_cons, div_eq_mul_inv, mul_inv, ← zpow'_neg, mul_assoc]
  congr! 1
  rw [mul_comm, mul_assoc]
  nth_rewrite 2 [mul_comm]
  rw [← zpow'_add, ← sub_eq_add_neg]

theorem div_eq_eval₃ [CommGroupWithZero M] {a₁ : ℤ × M} (a₂ : ℤ × M) {l₁ l₂ l : NF M}
    (h : (a₁ ::ᵣ l₁).eval / l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval / (a₂ ::ᵣ l₂).eval = ((-a₂.1, a₂.2) ::ᵣ l).eval := by
  simp only [eval_cons, ← h, zpow'_neg, div_eq_mul_inv, mul_inv, mul_assoc]

theorem div_eq_eval00 [GroupWithZero M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
    (hx₂ : x₂ = l₂.eval) (h : l₁.eval / l₂.eval = l.eval) :
    x₁ / x₂ = l.eval := by
  rw [hx₁, hx₂, h]

theorem div_eq_eval01 [DivisionRing M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
    (hx₂ : x₂ = -l₂.eval) (h : l₁.eval / l₂.eval = l.eval) :
    x₁ / x₂ = -l.eval := by
  rw [hx₁, hx₂, ←h, div_neg]

theorem div_eq_eval10 [DivisionRing M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = -l₁.eval)
    (hx₂ : x₂ = l₂.eval) (h : l₁.eval / l₂.eval = l.eval) :
    x₁ / x₂ = -l.eval := by
  rw [hx₁, hx₂, ←h, neg_div]

theorem div_eq_eval11 [DivisionRing M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = -l₁.eval)
    (hx₂ : x₂ = -l₂.eval) (h : l₁.eval / l₂.eval = l.eval) :
    x₁ / x₂ = l.eval := by
  rw [hx₁, hx₂, ←h, neg_div_neg_eq]

theorem eval_mul_eval_cons [GroupWithZero M] (n : ℤ) (e : M) {L l l' : NF M}
    (h : L.eval * l.eval = l'.eval) :
    L.eval * ((n, e) ::ᵣ l).eval = ((n, e) ::ᵣ l').eval := by
  rw [eval_cons, eval_cons, ← h, mul_assoc]

theorem eval_mul_eval_cons_zero [GroupWithZero M] {e : M} {L l l' l₀ : NF M}
    (h : L.eval * l.eval = l'.eval) (h' : ((0, e) ::ᵣ l).eval = l₀.eval) :
    L.eval * l₀.eval = ((0, e) ::ᵣ l').eval := by
  rw [← eval_mul_eval_cons 0 e h, h']

theorem eval_cons_mul_eval [CommGroupWithZero M] (n : ℤ) (e : M) {L l l' : NF M}
    (h : L.eval * l.eval = l'.eval) :
    ((n, e) ::ᵣ L).eval * l.eval = ((n, e) ::ᵣ l').eval := by
  rw [eval_cons, eval_cons, ← h, mul_assoc, mul_assoc]
  congr! 1
  rw [mul_comm]

theorem eval_cons_mul_eval_cons_neg [CommGroupWithZero M] (n : ℤ) {e : M} (he : e ≠ 0)
    {L l l' : NF M} (h : L.eval * l.eval = l'.eval) :
    ((n, e) ::ᵣ L).eval * ((-n, e) ::ᵣ l).eval = l'.eval := by
  rw [mul_eq_eval₂ n (-n) e h]
  simp [zpow'_zero_of_ne_zero he]

theorem cons_eq_div_of_eq_div [CommGroupWithZero M] (n : ℤ) (e : M) {t t_n t_d : NF M}
    (h : t.eval = t_n.eval / t_d.eval) :
    ((n, e) ::ᵣ t).eval = ((n, e) ::ᵣ t_n).eval / t_d.eval := by
  simp only [eval_cons, h, div_eq_mul_inv]
  rw [mul_comm, ← mul_assoc, mul_comm _ t_n.eval]

theorem cons_eq_div_of_eq_div' [CommGroupWithZero M] (n : ℤ) (e : M) {t t_n t_d : NF M}
    (h : t.eval = t_n.eval / t_d.eval) :
    ((-n, e) ::ᵣ t).eval = t_n.eval / ((n, e) ::ᵣ t_d).eval := by
  simp only [eval_cons, h, zpow'_neg, div_eq_mul_inv, mul_inv]
  rw [← mul_assoc, mul_comm]

theorem cons_zero_eq_div_of_eq_div [CommGroupWithZero M] (e : M) {t t_n t_d : NF M}
    (h : t.eval = t_n.eval / t_d.eval) :
    ((0, e) ::ᵣ t).eval = ((1, e) ::ᵣ t_n).eval / ((1, e) ::ᵣ t_d).eval := by
  simp only [eval_cons, h, div_eq_mul_inv, mul_inv, mul_assoc]
  congr! 1
  rw [← mul_assoc, mul_comm (zpow' e 1), mul_assoc]
  congr! 1
  rw [← zpow'_neg, ← zpow'_add]
  congr

instance : Inv (NF M) where
  inv l := l.map fun (a, x) ↦ (-a, x)

-- generalize library `List.prod_inv`
theorem _root_.List.prod_inv₀ {K : Type*} [DivisionCommMonoid K] :
    ∀ (L : List K), L.prod⁻¹ = (map (fun x ↦ x⁻¹) L).prod
  | [] => by simp
  | x :: xs => by simp [mul_comm, prod_inv₀ xs]

theorem eval_inv [CommGroupWithZero M] (l : NF M) : (l⁻¹).eval = l.eval⁻¹ := by
  simp only [NF.eval, List.map_map, List.prod'_inv₀, NF.instInv]
  congr
  ext p
  simp [zpow'_neg]

theorem one_div_eq_eval [CommGroupWithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval := by
  simp [eval_inv]

theorem inv_eq_eval0 [CommGroupWithZero M] {l : NF M} {x : M} (h : x = l.eval) :
    x⁻¹ = (l⁻¹).eval := by
  rw [h, eval_inv]

theorem inv_eq_eval1 [Field M] {l : NF M} {x : M} (h : x = -l.eval) :
    x⁻¹ = -(l⁻¹).eval := by
  rw [h, eval_inv, inv_neg]

instance : Pow (NF M) ℤ where
  pow l r := l.map fun (a, x) ↦ (r * a, x)

@[simp] theorem zpow_apply (r : ℤ) (l : NF M) : l ^ r = l.map fun (a, x) ↦ (r * a, x) :=
  rfl

-- in the library somewhere?
theorem _root_.List.prod_zpow {β : Type*} [DivisionCommMonoid β] {r : ℤ} {l : List β} :
    l.prod ^ r = (map (fun x ↦ x ^ r) l).prod :=
  let fr : β →* β := ⟨⟨fun b ↦ b ^ r, one_zpow r⟩, (mul_zpow · · r)⟩
  map_list_prod fr l

theorem eval_zpow' [CommGroupWithZero M] (l : NF M) (r : ℤ) :
    (l ^ r).eval = zpow' l.eval r := by
  unfold NF.eval at ⊢
  simp only [List.prod'_zpow', map_map, NF.zpow_apply]
  congr
  ext p
  simp [← zpow'_mul, mul_comm]

theorem zpow_eq_eval [CommGroupWithZero M] {l : NF M} {r : ℤ} (hr : r ≠ 0) {x : M}
    (hx : x = l.eval) :
    x ^ r = (l ^ r).eval := by
  rw [← zpow'_of_ne_zero_right x r hr, eval_zpow', hx]

theorem zpow_eq_eval_of_eq_neg [Field M] {l : NF M} {r : ℤ} (hr : r ≠ 0) (hr' : Even r)
    {x : M} (hx : x = -l.eval) :
    x ^ r = (l ^ r).eval := by
  rw [eval_zpow', zpow'_of_ne_zero_right _ r hr, hx]
  trans ((-1) * l.eval) ^ r
  · simp
  rw [mul_zpow, hr'.neg_one_zpow]
  simp

theorem zpow_eq_eval_of_eq_neg' [Field M] {l : NF M} {r : ℤ} (hr' : ¬ Even r) {x : M}
    (hx : x = -l.eval) :
    x ^ r = -(l ^ r).eval := by
  rw [Int.not_even_iff_odd] at hr'
  have hr : r ≠ 0 := by rintro rfl; contradiction
  rw [eval_zpow', zpow'_of_ne_zero_right _ r hr, hx]
  trans ((-1) * l.eval) ^ r
  · simp
  rw [mul_zpow, hr'.neg_one_zpow]
  simp

theorem zpow_zero_eq_eval [GroupWithZero M] (x : M) : x ^ (0:ℤ) = NF.eval [] := by
  rw [zpow_zero, one_eq_eval]

instance : Pow (NF M) ℕ where
  pow l r := l.map fun (a, x) ↦ (r * a, x)

@[simp] theorem pow_apply (r : ℕ) (l : NF M) : l ^ r = l.map fun (a, x) ↦ (r * a, x) :=
  rfl

-- in the library somewhere?
theorem _root_.List.prod_pow {β : Type*} [CommMonoid β] {r : ℕ} {l : List β} :
    l.prod ^ r = (map (fun x ↦ x ^ r) l).prod :=
  let fr : β →* β := ⟨⟨fun b ↦ b ^ r, one_pow r⟩, (mul_pow · · r)⟩
  map_list_prod fr l

theorem eval_pow [CommGroupWithZero M] (l : NF M) (r : ℕ) : (l ^ r).eval = zpow' l.eval r :=
  eval_zpow' l r

theorem pow_eq_eval [CommGroupWithZero M] {l : NF M} {r : ℕ} (hr : r ≠ 0) {x : M}
    (hx : x = l.eval) :
    x ^ r = (l ^ r).eval := by
  rw [eval_pow, hx]
  rw [zpow'_ofNat _ hr]

theorem pow_eq_eval_of_eq_neg [Field M] {l : NF M} {r : ℕ} (hr : r ≠ 0) (hr' : Even r)
    {x : M} (hx : x = -l.eval) :
    x ^ r = (l ^ r).eval := by
  rw [eval_pow, hx]
  rw [zpow'_ofNat _ hr]
  trans ((-1) * l.eval) ^ r
  · simp
  rw [mul_pow, hr'.neg_one_pow]
  simp

theorem pow_eq_eval_of_eq_neg' [Field M] {l : NF M} {r : ℕ} (hr' : ¬ Even r) {x : M}
    (hx : x = -l.eval) :
    x ^ r = -(l ^ r).eval := by
  have hr : r ≠ 0 := by rintro rfl; contradiction
  rw [eval_pow, hx]
  rw [zpow'_ofNat _ hr]
  trans ((-1) * l.eval) ^ r
  · simp
  rw [mul_pow, neg_one_pow_eq_ite, if_neg hr']
  simp

theorem pow_zero_eq_eval [GroupWithZero M] (x : M) : x ^ (0:ℕ) = NF.eval [] := by
  rw [pow_zero, one_eq_eval]

theorem eval_cons_of_pow_eq_zero [GroupWithZero M] {r : ℤ} (hr : r = 0) {x : M} (hx : x ≠ 0)
    (l : NF M) :
    ((r, x) ::ᵣ l).eval = NF.eval l := by
  simp [hr, zpow'_zero_of_ne_zero hx]

theorem eval_cons_eq_eval_of_eq_of_eq [GroupWithZero M] (r : ℤ) (x : M) {t t' l' : NF M}
    (h : NF.eval t = NF.eval t') (h' : ((r, x) ::ᵣ t').eval = NF.eval l') :
    ((r, x) ::ᵣ t).eval = NF.eval l' := by
  rw [← h', eval_cons, eval_cons, h]

end NF

end Mathlib.Tactic.FieldSimp
