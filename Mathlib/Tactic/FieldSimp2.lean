/-
Copyright (c) 2024 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic.Positivity.Core
import Mathlib.Util.AtomM


/-! # A tactic for clearing denominators in fields

-/

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic List

section zpow'
variable {α : Type*} [Semifield α]

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

@[simp]
lemma zero_zpow' (n : ℤ) : zpow' (0 : α) n = 0 := by
  simp +contextual only [zpow', true_and, ite_eq_left_iff]
  intro hn
  exact zero_zpow n hn

@[simp]
lemma one_zpow' (n : ℤ) : zpow' (1 : α) n = 1 := by
  simp [zpow']

lemma mul_zpow' (n : ℤ) (a b : α) : zpow' (a * b) n = zpow' a n * zpow' b n := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  simp [zpow', ha, hb]
  exact mul_zpow a b n

@[simp]
lemma zpow'_one (a : α) : zpow' a 1 = a := by
  simp [zpow']

lemma zpow'_neg (a : α) (n : ℤ) : zpow' a (-n) = (zpow' a n)⁻¹ := by
  simp +contextual [zpow', apply_ite]
  split_ifs with h
  · tauto
  · tauto

-- example {n : ℕ} (hn : n = 0) (a b c : ℤ) : (if n^n = 1 ∧ 0 = 0 then a else b) = c := by
--   simp  [hn]
--   sorry

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
theorem prod'_zpow' {β : Type*} [Semifield β] {r : ℤ} {l : List β} :
    zpow' l.prod' r = (map (fun x ↦ zpow' x r) l).prod' :=
  let fr : β →* β := ⟨⟨fun b ↦ zpow' b r, one_zpow' r⟩, (mul_zpow' r)⟩
  map_list_prod' fr l

-- Do we need the ℕ exponenet at all?
-- in the library somewhere?
theorem _root_.List.prod'_pow {β : Type*} [CommMonoid β] {r : ℕ} {l : List β} :
    l.prod' ^ r = (map (fun x ↦ x ^ r) l).prod' :=
  let fr : β →* β := ⟨⟨fun b ↦ b ^ r, one_pow r⟩, (mul_pow · · r)⟩
  map_list_prod' fr l

end List

namespace Mathlib.Tactic.FieldSimp

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
noncomputable def eval [Semifield M] (l : NF M) : M :=
  (l.map (fun (⟨r, x⟩ : ℤ × M) ↦ zpow' x r)).prod'

@[simp] theorem eval_cons [Semifield M] (p : ℤ × M) (l : NF M) :
    (p ::ᵣ l).eval = l.eval * zpow' p.2 p.1 := by
  unfold eval cons
  rw [List.map_cons]
  rw [List.prod'_cons]


theorem atom_eq_eval [Semifield M] (x : M) : x = NF.eval [(1, x)] := by simp [eval]

variable (M) in
theorem one_eq_eval [Semifield M] : (1:M) = NF.eval (M := M) [] := rfl

theorem mul_eq_eval₁ [Semifield M] (a₁ : ℤ × M) {a₂ : ℤ × M} {l₁ l₂ l : NF M}
    (h : l₁.eval * (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval * (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, mul_assoc]
  congr! 1
  rw [mul_comm, mul_assoc]

theorem mul_eq_eval₂ [Semifield M] {r₁ r₂ : ℤ} (hr : r₁ + r₂ = 0) (x : M) (hx : x ≠ 0)
    {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval * ((r₂, x) ::ᵣ l₂).eval = l.eval := by
  simp only [← h, eval_cons, mul_assoc]
  congr! 1
  rw [mul_comm, mul_assoc, ← zpow'_add, add_comm, hr]
  sorry
  -- simp [hx]

theorem mul_eq_eval₂' [Semifield M] {r₁ r₂ : ℤ} (hr : r₁ + r₂ ≠ 0) (x : M)
    {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval * ((r₂, x) ::ᵣ l₂).eval = ((r₁ + r₂, x) ::ᵣ l).eval := by
  stop
  simp only [← h, eval_cons]
  obtain rfl | h := eq_or_ne x 0
  · rw [zero_zpow _ hr]
    obtain hr₁ | hr₂ : r₁ ≠ 0 ∨ r₂ ≠ 0 := by omega
    · simp [zero_zpow _ hr₁]
    · simp [zero_zpow _ hr₂]
  simp only [zpow_add₀ h, mul_assoc]
  congr! 1
  simp only [← mul_assoc]
  rw [mul_comm (x ^ r₁)]

theorem mul_eq_eval₃ [Semifield M] {a₁ : ℤ × M} (a₂ : ℤ × M) {l₁ l₂ l : NF M}
    (h : (a₁ ::ᵣ l₁).eval * l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval * (a₂ ::ᵣ l₂).eval = (a₂ ::ᵣ l).eval := by
  stop
  simp only [eval_cons, ← h, mul_assoc]

theorem mul_eq_eval [Semifield M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
    (hx₂ : x₂ = l₂.eval) (h : l₁.eval * l₂.eval = l.eval) :
    x₁ * x₂ = l.eval := by
  rw [hx₁, hx₂, h]

theorem div_eq_eval₁ [Semifield M] (a₁ : ℤ × M) {a₂ : ℤ × M} {l₁ l₂ l : NF M}
    (h : l₁.eval / (a₂ ::ᵣ l₂).eval = l.eval) :
    (a₁ ::ᵣ l₁).eval / (a₂ ::ᵣ l₂).eval = (a₁ ::ᵣ l).eval := by
  simp only [eval_cons, ← h, div_eq_mul_inv, mul_assoc]
  congr! 1
  rw [mul_comm]

theorem div_eq_eval₂ [Semifield M] {r₁ r₂ : ℤ} (hr : r₁ - r₂ = 0) (x : M) (hx : x ≠ 0)
    {l₁ l₂ l : NF M} (h : l₁.eval / l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval / ((r₂, x) ::ᵣ l₂).eval = l.eval := by
  simp only [← h, eval_cons, div_eq_mul_inv, mul_inv, mul_zpow, ← zpow'_neg, mul_assoc]
  congr! 1
  rw [mul_comm, mul_assoc]
  nth_rewrite 2 [mul_comm]
  rw [← zpow'_add, ← sub_eq_add_neg, hr]
  stop
  simp

theorem div_eq_eval₂' [Semifield M] {r₁ r₂ : ℤ} (hr : r₁ - r₂ ≠ 0) (x : M)
    {l₁ l₂ l : NF M} (h : l₁.eval / l₂.eval = l.eval) :
    ((r₁, x) ::ᵣ l₁).eval / ((r₂, x) ::ᵣ l₂).eval = ((r₁ - r₂, x) ::ᵣ l).eval := by
  stop
  simp only [← h, eval_cons, sub_neg_eq_add, zpow_neg]
  obtain rfl | h := eq_or_ne x 0
  · rw [zero_zpow _ hr]
    obtain hr₁ | hr₂ : r₁ ≠ 0 ∨ r₂ ≠ 0 := by omega
    · simp [zero_zpow _ hr₁]
    · simp [zero_zpow _ hr₂]
  simp only [zpow_sub₀ h, mul_assoc]
  simp only [pow_add, div_eq_mul_inv, mul_inv, mul_assoc, inv_inv]
  congr! 1
  simp only [← mul_assoc]
  congr! 1
  rw [mul_comm]

theorem div_eq_eval₃ [Semifield M] {a₁ : ℤ × M} (a₂ : ℤ × M) {l₁ l₂ l : NF M}
    (h : (a₁ ::ᵣ l₁).eval / l₂.eval = l.eval) :
    (a₁ ::ᵣ l₁).eval / (a₂ ::ᵣ l₂).eval = ((-a₂.1, a₂.2) ::ᵣ l).eval := by
  stop
  simp only [eval_cons, zpow_neg, mul_inv, div_eq_mul_inv, ← h, ← mul_assoc]

theorem div_eq_eval [Semifield M] {l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval)
    (hx₂ : x₂ = l₂.eval) (h : l₁.eval / l₂.eval = l.eval) :
    x₁ / x₂ = l.eval := by
  rw [hx₁, hx₂, h]

theorem add_eq_eval [Semifield M] {x₁ x₂ x₁' x₂' X₁ X₂ X₁' X₂' a b y : M}
    (h₁ : x₁ = X₁) (h₂ : x₂ = X₂)
    (h₁' : a * X₁' = X₁) (h₂' : a * X₂' = X₂)
    (h₁'' : X₁' = x₁') (h₂'' : X₂' = x₂')
    (H_atom : x₁' + x₂' = y)
    (H_mul : a * y = b) :
    x₁ + x₂ = b := by
  rw [h₁, h₂, ← h₁'', ← h₂''] at *
  rw [← H_mul, ← H_atom] at *
  rw [← h₁', ← h₂'] at *
  simp only at *
  rw [mul_add]

instance : Inv (NF M) where
  inv l := l.map fun (a, x) ↦ (-a, x)

-- generalize library `List.prod_inv`
theorem _root_.List.prod_inv₀ {K : Type*} [DivisionCommMonoid K] :
    ∀ (L : List K), L.prod⁻¹ = (map (fun x ↦ x⁻¹) L).prod
  | [] => by simp
  | x :: xs => by simp [mul_comm, prod_inv₀ xs]

theorem eval_inv [Semifield M] (l : NF M) : (l⁻¹).eval = l.eval⁻¹ := by
  simp only [NF.eval, List.map_map, List.prod'_inv₀, NF.instInv]
  congr
  ext p
  simp [zpow'_neg]

theorem one_div_eq_eval [Semifield M] (l : NF M) : 1 / l.eval = (l⁻¹).eval := by
  simp [eval_inv]

theorem inv_eq_eval [Semifield M] {l : NF M} {x : M} (h : x = l.eval) :
    x⁻¹ = (l⁻¹).eval := by
  rw [h, eval_inv]

instance : Pow (NF M) ℤ where
  pow l r := l.map fun (a, x) ↦ (r * a, x)

@[simp] theorem zpow_apply (r : ℤ) (l : NF M) : l ^ r = l.map fun (a, x) ↦ (r * a, x) :=
  rfl

-- in the library somewhere?
theorem _root_.List.prod_zpow {β : Type*} [DivisionCommMonoid β] {r : ℤ} {l : List β} :
    l.prod ^ r = (map (fun x ↦ x ^ r) l).prod :=
  let fr : β →* β := ⟨⟨fun b ↦ b ^ r, one_zpow r⟩, (mul_zpow · · r)⟩
  map_list_prod fr l

theorem eval_zpow [Semifield M] {l : NF M} {x : M} (h : x = l.eval) (r : ℤ) :
    (l ^ r).eval = zpow' x r := by
  unfold NF.eval at h ⊢
  simp only [h, List.prod'_zpow', map_map, NF.zpow_apply]
  congr
  ext p
  simp [← zpow'_mul, mul_comm]


theorem zpow'_eq_eval [Semifield M] {l : NF M} (r : ℤ) {x : M} (hx : x = l.eval) :
    zpow' x r = (l ^ r).eval := by
  rw [hx, eval_zpow]
  rfl

-- theorem zpow_zero_eq_eval [Semifield M] (x : M) : zpow' x (0:ℤ) = NF.eval [] := by
--   rw [zpow_zero, one_eq_eval]

instance : Pow (NF M) ℕ where
  pow l r := l.map fun (a, x) ↦ (r * a, x)

@[simp] theorem pow_apply (r : ℕ) (l : NF M) : l ^ r = l.map fun (a, x) ↦ (r * a, x) :=
  rfl

-- in the library somewhere?
theorem _root_.List.prod_pow {β : Type*} [CommMonoid β] {r : ℕ} {l : List β} :
    l.prod ^ r = (map (fun x ↦ x ^ r) l).prod :=
  let fr : β →* β := ⟨⟨fun b ↦ b ^ r, one_pow r⟩, (mul_pow · · r)⟩
  map_list_prod fr l

theorem eval_pow [Semifield M] {l : NF M} {x : M} (h : x = l.eval) (r : ℕ) :
    (l ^ r).eval = zpow' x r := by
  stop
  unfold NF.eval at h ⊢
  simp only [h, prod'_pow, map_map, NF.pow_apply]
  congr! 2
  -- ext p
  dsimp
  rw [mul_comm, zpow'_mul]
  norm_cast


theorem pow_eq_eval [Semifield M] {l : NF M} (r : ℕ) (hr : r ≠ 0) {x : M} (hx : x = l.eval) :
    x ^ r = (l ^ r).eval := by
  stop
  rw [hx, eval_pow]
  sorry



theorem pow_zero_eq_eval [Semifield M] (x : M) : x ^ (0:ℕ) = NF.eval [] := by
  rw [pow_zero, one_eq_eval]


theorem eq_of_eq_mul [Mul M] {x₁ x₂ x₁' x₂' X₁ X₁' X₂ X₂' d : M}
    (h₁ : x₁ = X₁) (h₂ : x₂ = X₂) (h₁' : d * X₁' = X₁) (h₂' : d * X₂' = X₂)
    (h₁'' : X₁' = x₁') (h₂'' : X₂' = x₂') (h : x₁' = x₂') :
    x₁ = x₂ := by
  rw [h₁, h₂, ← h₁', ← h₂', h₁'', h₂'', h]

end NF

variable {v : Level}

/-! ### Lists of expressions representing exponents and atoms, and operations on such lists -/

/-- Basic meta-code "normal form" object of the `field_simp` tactic: a type synonym
for a list of ordered triples comprising an expression representing a term of a type `M` (where
typically `M` is a field), together with an integer "power" and a natural number "index".

The natural number represents the index of the `M` term in the `AtomM` monad: this is not enforced,
but is sometimes assumed in operations.  Thus when items `((a₁, x₁), k)` and `((a₂, x₂), k)`
appear in two different `FieldSimp.qNF` objects (i.e. with the same `ℕ`-index `k`), it is expected
that the expressions `x₁` and `x₂` are the same.  It is also expected that the items in a
`FieldSimp.qNF` list are in strictly decreasing order by natural-number index.

By forgetting the natural number indices, an expression representing a `Mathlib.Tactic.FieldSimp.NF`
object can be built from a `FieldSimp.qNF` object; this construction is provided as
`Mathlib.Tactic.FieldSimp.qNF.toNF`. -/
abbrev qNF (M : Q(Type v)) := List ((ℤ × Q($M)) × ℕ)

namespace qNF

variable {M : Q(Type v)}

/-- Given `l` of type `qNF M`, i.e. a list of `(ℤ × Q($M)) × ℕ`s (two `Expr`s and a natural
number), build an `Expr` representing an object of type `NF M` (i.e. `List (ℤ × M)`) in the
in the obvious way: by forgetting the natural numbers and gluing together the integers and `Expr`s.
-/
def toNF (l : qNF M) : Q(NF $M) :=
  let l' : List Q(ℤ × $M) := (l.map Prod.fst).map (fun (a, x) ↦ q(($a, $x)))
  let qt : List Q(ℤ × $M) → Q(List (ℤ × $M)) := List.rec q([]) (fun e _ l ↦ q($e ::ᵣ $l))
  qt l'

/-- Given `l` of type `qNF M`, i.e. a list of `(ℤ × Q($M)) × ℕ`s (two `Expr`s and a natural
number), apply an expression representing a function with domain `ℤ` to each of the `ℤ`
components. -/
def onExponent (l : qNF M) (f : ℤ → ℤ) : qNF M :=
  l.map fun ((a, x), k) ↦ ((f a, x), k)

/-- Build a transparent expression for the product of powers represented by `l : qNF M`. -/
def evalPrettyMonomial (iM : Q(Semifield $M)) (r : ℤ) (x : Q($M)) :
    MetaM (Σ e : Q($M), Q(zpow' $x $r = $e)) := do
  match r with
  | 0 => /- If an exponent is zero then we must not have been able to prove that x is nonzero.  -/
    return ⟨q($x / $x), q(sorry)⟩
  | 1 => return ⟨x, q(zpow'_one $x)⟩
  | .ofNat r => return ⟨q($x ^ $r), q(sorry /-zpow_natCast $x $r-/)⟩
  | r => return ⟨q($x ^ $r), q(sorry /-rfl-/)⟩

/-- Build a transparent expression for the product of powers represented by `l : qNF M`. -/
def evalPretty (iM : Q(Semifield $M)) (l : qNF M) :
    MetaM (Σ e : Q($M), Q(NF.eval $(l.toNF) = $e)) := do
  match l with
  | [] => return ⟨q(1), q(rfl)⟩
  | [((r, x), _)] =>
    let ⟨e, pf⟩ ← evalPrettyMonomial iM r x
    return ⟨e, q(Eq.trans (one_mul _) $pf)⟩
  | ((r, x), _) :: t =>
    let ⟨e, pf_e⟩ ← evalPrettyMonomial iM r x
    let ⟨t', pf⟩ ← evalPretty iM t
    return ⟨q($t' * $e), (q(sorry /-congr_arg₂ HMul.hMul $pf $pf_e-/))⟩

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), construct another such term `l`, which will have the property that in
the field `$M`, the product of the "multiplicative linear combinations" represented by `l₁` and
`l₂` is the multiplicative linear combination represented by `l`.

The construction assumes, to be valid, that the lists `l₁` and `l₂` are in strictly decreasing order
by `ℕ`-component, and that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with
the same `ℕ`-component `k`, then the expressions `x₁` and `x₂` are equal.

The construction is as follows: merge the two lists, except that if pairs `(a₁, x₁)` and `(a₂, x₂)`
appear in `l₁`, `l₂` respectively with the same `ℕ`-component `k`, then contribute a term
`(a₁ + a₂, x₁)` to the output list with `ℕ`-component `k`. -/
def mul : qNF M → qNF M → qNF M
  | [], l => l
  | l, [] => l
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      ((a₁, x₁), k₁) :: mul t₁ (((a₂, x₂), k₂) :: t₂)
    else if k₁ = k₂ then
      /- If we can prove that the atom is nonzero then we could remove it from this list,
      but this will be done at a later stage. -/
      -- if a₁ + a₂ = 0 then
      --   mul t₁ t₂
      -- else
      ((a₁ + a₂, x₁), k₁) :: mul t₁ t₂
    else
      ((a₂, x₂), k₂) :: mul (((a₁, x₁), k₁) :: t₁) t₂

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), recursively construct a proof that in the field `$M`, the product of
the "multiplicative linear combinations" represented by `l₁` and `l₂` is the multiplicative linear
combination represented by `FieldSimp.qNF.mul l₁ l₁`. -/
def mkMulProof (iM : Q(Semifield $M)) (l₁ l₂ : qNF M) :
    Q((NF.eval $(l₁.toNF)) * NF.eval $(l₂.toNF) = NF.eval $((qNF.mul l₁ l₂).toNF)) :=
  match l₁, l₂ with
  | [], l => (q(one_mul (NF.eval $(l.toNF))):)
  | l, [] => (q(mul_one (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      let pf := mkMulProof iM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.mul_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkMulProof iM t₁ t₂
      if a₁ + a₂ = 0 then
        -- how do you quote a proof of a `ℤ` equality?
        let h : Q($a₁ + $a₂ = 0) := (q(Eq.refl (0:ℤ)):)
        let hx₁ : Q($x₁ ≠ 0) := q(sorry) -- use the discharger here
        (q(NF.mul_eq_eval₂ $h $x₁ $hx₁ $pf):)
      else
        -- how do you quote a proof of a `ℤ` disequality?
        let z : Q(decide ($a₁ + $a₂ ≠ 0) = true) := (q(Eq.refl true):)
        let h : Q($a₁ + $a₂ ≠ 0) := q(of_decide_eq_true $z)
        (q(NF.mul_eq_eval₂' $h $x₁ $pf):)
    else
      let pf := mkMulProof iM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.mul_eq_eval₃ ($a₂, $x₂) $pf):)

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), construct another such term `l`, which will have the property that in
the field `$M`, the quotient of the "multiplicative linear combinations" represented by `l₁` and
`l₂` is the multiplicative linear combination represented by `l`.

The construction assumes, to be valid, that the lists `l₁` and `l₂` are in strictly decreasing order
by `ℕ`-component, and that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with
the same `ℕ`-component `k`, then the expressions `x₁` and `x₂` are equal.

The construction is as follows: merge the first list and the negation of the second list, except
that if pairs `(a₁, x₁)` and `(a₂, x₂)` appear in `l₁`, `l₂` respectively with the same
`ℕ`-component `k`, then contribute a term `(a₁ - a₂, x₁)` to the output list with `ℕ`-component `k`.
-/
def div : qNF M → qNF M → qNF M
  | [], l => l.onExponent Neg.neg
  | l, [] => l
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      ((a₁, x₁), k₁) :: div t₁ (((a₂, x₂), k₂) :: t₂)
    else if k₁ = k₂ then
      -- if a₁ - a₂ = 0 then
      --   div t₁ t₂
      -- else
        ((a₁ - a₂, x₁), k₁) :: div t₁ t₂
    else
      ((-a₂, x₂), k₂) :: div (((a₁, x₁), k₁) :: t₁) t₂

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), recursively construct a proof that in the field `$M`, the quotient
of the "multiplicative linear combinations" represented by `l₁` and `l₂` is the multiplicative
linear combination represented by `FieldSimp.qNF.div l₁ l₁`. -/
def mkDivProof (iM : Q(Semifield $M)) (l₁ l₂ : qNF M) :
    Q(NF.eval $(l₁.toNF) / NF.eval $(l₂.toNF) = NF.eval $((qNF.div l₁ l₂).toNF)) :=
  match l₁, l₂ with
  | [], l => (q(NF.one_div_eq_eval $(l.toNF)):)
  | l, [] => (q(div_one (NF.eval $(l.toNF))):)
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      let pf := mkDivProof iM t₁ (((a₂, x₂), k₂) :: t₂)
      (q(NF.div_eq_eval₁ ($a₁, $x₁) $pf):)
    else if k₁ = k₂ then
      let pf := mkDivProof iM t₁ t₂
      if a₁ - a₂ = 0 then
        -- how do you quote a proof of a `ℤ` equality?
        let h : Q($a₁ - $a₂ = 0) := (q(Eq.refl (0:ℤ)):)
        let hx₁ : Q($x₁ ≠ 0) := q(sorry) -- use the discharger here
        (q(sorry/- NF.div_eq_eval₂ $h $x₁ $hx₁ $pf -/))
      else
        -- how do you quote a proof of a `ℤ` disequality?
        let z : Q(decide ($a₁ - $a₂ ≠ 0) = true) := (q(Eq.refl true):)
        let h : Q($a₁ - $a₂ ≠ 0) := q(of_decide_eq_true $z)
        (q(sorry /-NF.div_eq_eval₂' $h $x₁ $pf-/))
    else
      let pf := mkDivProof iM (((a₁, x₁), k₁) :: t₁) t₂
      (q(sorry/- NF.div_eq_eval₃ ($a₂, $x₂) $pf -/))

-- minimum of the
partial /- TODO figure out why! -/ def minimum : qNF M → qNF M → qNF M
| [], [] => []
| [], ((n, e), i) :: rest | ((n, e), i) :: rest, [] =>
  if 0 ≤ n then (minimum [] rest) else ((n, e), i) :: (minimum [] rest)
| ((n, e), i) :: rest, ((n', e'), i') :: rest' =>
    -- should factor into a separate definition
    if i > i' then
      if 0 ≤ n then minimum rest (((n', e'), i') :: rest')
      else ((n, e), i) :: minimum rest (((n', e'), i') :: rest')
    else if i = i' then
      ((min n n', e), i) :: minimum rest rest'
    else
      if 0 ≤ n' then minimum rest' (((n, e), i) :: rest)
      else ((n', e'), i') :: minimum rest' (((n, e), i) :: rest)

def negPart : qNF M → qNF M
  | [] => []
  | ((n, e), i) :: rest =>
    if 0 ≤ n then negPart rest else ((n, e), i) :: negPart rest

end qNF

/-! ### Core of the `field_simp` tactic -/

variable {M : Q(Type v)}

/-- The main algorithm behind the `field_simp` tactic: partially-normalizing an
expression in a field `M` into the form x1 ^ c1 * x2 ^ c2 * ... x_k ^ c_k,
where x1, x2, ... are distinct atoms in `M`, and c1, c2, ... are integers.

Possible TODO, if poor performance on large problems is witnessed: switch the implementation from
`AtomM` to `CanonM`, per the discussion
https://github.com/leanprover-community/mathlib4/pull/16593/files#r1749623191 -/
partial def normalize (iM : Q(Semifield $M)) (x : Q($M)) :
    AtomM (Σ l : qNF M, Q($x = NF.eval $(l.toNF))) := do
  let baseCase (y : Q($M)) : AtomM (Σ l : qNF M, Q($y = NF.eval $(l.toNF))):= do
    let (k, ⟨x', _⟩) ← AtomM.addAtomQ y
    pure ⟨[((1, x'), k)], q(NF.atom_eq_eval $x')⟩
  match x with
  /- normalize a multiplication: `x₁ * x₂` -/
  | ~q($x₁ * $x₂) =>
    let ⟨l₁, pf₁⟩ ← normalize iM x₁
    let ⟨l₂, pf₂⟩ ← normalize iM x₂
    -- build the new list and proof
    let pf := qNF.mkMulProof iM l₁ l₂
    pure ⟨qNF.mul l₁ l₂, (q(NF.mul_eq_eval $pf₁ $pf₂ $pf))⟩
  /- normalize a division: `x₁ / x₂` -/
  | ~q($x₁ / $x₂) =>
    let ⟨l₁, pf₁⟩ ← normalize iM x₁
    let ⟨l₂, pf₂⟩ ← normalize iM x₂
    -- build the new list and proof
    let pf := qNF.mkDivProof iM l₁ l₂
    pure ⟨qNF.div l₁ l₂, (q(NF.div_eq_eval $pf₁ $pf₂ $pf))⟩
  /- normalize a inversion: `y⁻¹` -/
  | ~q($y⁻¹) =>
    let ⟨l, pf⟩ ← normalize iM y
    -- build the new list and proof
    pure ⟨l.onExponent Neg.neg, (q(NF.inv_eq_eval $pf):)⟩
  | ~q($a + $b) =>
    let ⟨l₁, pf₁⟩ ← normalize iM a
    let ⟨l₂, pf₂⟩ ← normalize iM b
    let L : qNF M := qNF.minimum l₁ l₂
    let l₁' := qNF.div l₁ L
    let l₂' := qNF.div l₂ L
    let pf₁' : Q((NF.eval $(L.toNF)) * NF.eval $(l₁'.toNF) = NF.eval $(l₁.toNF)) :=
      qNF.mkMulProof iM L l₁'
    let pf₂' : Q((NF.eval $(L.toNF)) * NF.eval $(l₂'.toNF) = NF.eval $(l₂.toNF)) :=
      qNF.mkMulProof iM L l₂'
    let ⟨e₁, pf₁''⟩ ← qNF.evalPretty iM l₁'
    let ⟨e₂, pf₂''⟩ ← qNF.evalPretty iM l₂'
    let e : Q($M) := q($e₁ + $e₂)
    let ⟨sum, pf_atom⟩ ← baseCase e
    let L' := qNF.mul L sum
    let pf_mul : Q((NF.eval $(L.toNF)) * NF.eval $(sum.toNF) = NF.eval $(L'.toNF)) :=
      qNF.mkMulProof iM L sum
    pure ⟨L', (q(NF.add_eq_eval $pf₁ $pf₂ $pf₁' $pf₂' $pf₁'' $pf₂'' $pf_atom $pf_mul))⟩
  /- normalize an integer exponentiation: `y ^ (s : ℤ)` -/
  | ~q($y ^ ($s : ℤ)) =>
    let some s := Expr.int? s | baseCase x
    if s = 0 then
      pure ⟨[], (q(sorry /-NF.zpow_zero_eq_eval $y-/))⟩
    else
      let ⟨l, pf⟩ ← normalize iM y
      -- build the new list and proof
      pure ⟨l.onExponent (HMul.hMul s), (q(sorry /-zpow'_eq_eval $s $pf-/))⟩
  /- normalize a natural number exponentiation: `y ^ (s : ℕ)` -/
  | ~q($y ^ ($s : ℕ)) =>
    let some s := Expr.nat? s | baseCase x
    if s = 0 then
      pure ⟨[], (q(sorry /-NF.pow_zero_eq_eval $y-/))⟩
    else
      let ⟨l, pf⟩ ← normalize iM y
      have ps : Q($s ≠ 0) := q(sorry)
      -- build the new list and proof
      pure ⟨l.onExponent (HMul.hMul s), (q(NF.pow_eq_eval $s $ps $pf):)⟩
  /- normalize a `(1:M)` -/
  | ~q(1) => pure ⟨[], q(NF.one_eq_eval $M)⟩
  /- anything else should be treated as an atom -/
  | _ => baseCase x

/-- The main algorithm behind the `field_simp` tactic: partially-normalizing an
expression in a field `M` into the form x1 ^ c1 * x2 ^ c2 * ... x_k ^ c_k,
where x1, x2, ... are distinct atoms in `M`, and c1, c2, ... are integers.

Version with "pretty" output. -/
def normalizePretty (iM : Q(Semifield $M)) (x : Q($M)) : AtomM (Σ x' : Q($M), Q($x = $x')) := do
  let ⟨l, pf⟩ ← normalize iM x
  let ⟨x', pf'⟩ ← l.evalPretty iM
  return ⟨x', q(Eq.trans $pf $pf')⟩

/-- Given `e₁` and `e₂`, construct a new goal which is sufficient to prove `e₁ = e₂`. -/
def proveEq (iM : Q(Semifield $M)) (e₁ e₂ : Q($M)) : AtomM (MVarId × Q($e₁ = $e₂)) := do
  let ⟨l₁, pf₁⟩ ← normalize iM e₁
  let ⟨l₂, pf₂⟩ ← normalize iM e₂
  let L := qNF.negPart (qNF.minimum l₁ l₂)
  let l₁' := qNF.div l₁ L
  let l₂' := qNF.div l₂ L
  let pf₁' : Q((NF.eval $(L.toNF)) * NF.eval $(l₁'.toNF) = NF.eval $(l₁.toNF)) :=
    qNF.mkMulProof iM L l₁'
  let pf₂' : Q((NF.eval $(L.toNF)) * NF.eval $(l₂'.toNF) = NF.eval $(l₂.toNF)) :=
    qNF.mkMulProof iM L l₂'
  let ⟨e₁', pf₁''⟩ ← l₁'.evalPretty iM
  let ⟨e₂', pf₂''⟩ ← l₂'.evalPretty iM
  let mvar ← mkFreshExprMVarQ q($e₁' = $e₂')
  return ⟨Expr.mvarId! mvar, q(NF.eq_of_eq_mul $pf₁ $pf₂ $pf₁' $pf₂' $pf₁'' $pf₂'' $mvar)⟩

open Elab Tactic

/-- Conv tactic for field_simp normalisation.
Wraps the `MetaM` normalization function `normalize`. -/
elab "field_simp2" : conv => do
  -- find the expression `x` to `conv` on
  let x ← Conv.getLhs
  -- infer `u` and `K : Q(Type u)` such that `x : Q($K)`
  let ⟨u, K, _⟩ ← inferTypeQ' x
  -- find a `Semifield` instance on `K`
  let iK : Q(Semifield $K) ← synthInstanceQ q(Semifield $K)
  -- run the core normalization function `normalizePretty` on `x`
  let ⟨e, pf⟩ ← AtomM.run .reducible <| normalizePretty iK x
  -- convert `x` to the output of the normalization
  Conv.applySimpResult { expr := e, proof? := some pf }

elab "field_simp2" : tactic => liftMetaTactic fun g ↦ do
  -- find the proposition `t` to prove
  let t ← g.getType''
  let some ⟨_, a, b⟩ := t.eq? | throwError "field_simp proves only equality goals"
  -- infer `u` and `K : Q(Type u)` such that `x : Q($K)`
  let ⟨u, K, a⟩ ← inferTypeQ' a
  -- find a `Semifield` instance on `K`
  let iK : Q(Semifield $K) ← synthInstanceQ q(Semifield $K)
  -- run the core equality-proving mechanism on `x`
  let ⟨g', pf⟩ ← AtomM.run .reducible <| proveEq iK a b
  g.assign pf
  return [g']

end Mathlib.Tactic.FieldSimp

open Mathlib.Tactic.FieldSimp

variable {x y z : ℚ}

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => (1 : ℚ)

-- Combining powers of a single atom.
section

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x ^ 0

/-- info: x -/
#guard_msgs in
#conv field_simp2 => x ^ 1

/-- info: x -/
#guard_msgs in
#conv field_simp2 => x

/-- info: x ^ 2 -/
#guard_msgs in
#conv field_simp2 => x ^ 2

/-- info: x ^ 3 -/
#guard_msgs in
#conv field_simp2 => x ^ 1 * x ^ 2

/-- info: x ^ 2 -/
#guard_msgs in
#conv field_simp2 => x * x

/-- info: x ^ 45 -/
#guard_msgs in
#conv field_simp2 => x ^ 3 * x ^ 42

section -- variable exponents are not supported
variable {k : ℤ}

/-- info: x ^ k * x ^ 2 -/
#guard_msgs in
#conv field_simp2 => x ^ k * x ^ 2

end

/-- info: x ^ (-3) -/
#guard_msgs in
#conv field_simp2 => x ^ (-1 : ℤ) * x ^ (-2 : ℤ)

-- Cancellation: if x could be zero, we cannot cancel x * x⁻¹.
-- TODO: right now, we always cancel (which we should not)

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x * x⁻¹

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x⁻¹ * x

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x / x

/-- info: x ^ 2 -/
#guard_msgs in
#conv field_simp2 => x ^ 3 * x⁻¹

/-- info: x ^ (-3) -/
#guard_msgs in
#conv field_simp2 => x / x ^ 4

-- If x is non-zero, we do cancel.
section
variable {hx : x ≠ 0}

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x * x⁻¹

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x⁻¹ * x

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => x / x

/-- info: x ^ 2 -/
#guard_msgs in
#conv field_simp2 => x ^ 3 * x⁻¹

/-- info: x ^ (-3) -/
#guard_msgs in
#conv field_simp2 => x / x ^ 4

end

-- Combining this works also when other atoms are "in the way".
-- TODO: these tests are broken

/-- info: x ^ 3 * y ^ 4 -/
#guard_msgs in
#conv field_simp2 => x ^1 * y * x ^2 * y ^ 3

/-- info: x ^ 3 -/
#guard_msgs in
#conv field_simp2 => x ^ 1 * y * x ^2 * y⁻¹

variable {y' : ℚ} (hy' : y' ≠ 0)

/-- info: x ^ 3 -/
#guard_msgs in
#conv field_simp2 => x ^ 1 * y * x ^ 2 * y⁻¹

end

/-- info: x -/
#guard_msgs in
#conv field_simp2 => x

/-- info: x + y -/
#guard_msgs in
#conv field_simp2 => x + y

/-- info: x * y -/
#guard_msgs in
#conv field_simp2 => x * y

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => (x * y) / (y * x)

/-- info: x * (y + 1) -/
#guard_msgs in
#conv field_simp2 => x * y + x * 1

/-- info: 1 -/
#guard_msgs in
#conv field_simp2 => (x * y) * (y * x)⁻¹

/-- info: y -/
#guard_msgs in
#conv field_simp2 => x ^ (0:ℤ) * y

/-- info: y ^ 2 -/
#guard_msgs in
#conv field_simp2 => y * (y + x) ^ (0:ℤ) * y

/-- info: x * y ^ (-1) -/
#guard_msgs in
#conv field_simp2 => x / y

/-- info: (x + 1) ^ (-1) * (y + 1) ^ (-1) * (x * (y + 1) + (x + 1) * y) -/
#guard_msgs in
#conv field_simp2 => x / (x + 1) + y / (y + 1)

example : (1 : ℚ) = 1 := by conv_lhs => field_simp2
example : x = x := by conv_lhs => field_simp2
example : x * y = x * y := by conv_lhs => field_simp2
example : x / y = x * y ^ (-1:ℤ) := by conv_lhs => field_simp2
example : x / (y / x) = x ^ 2 * y ^ (-1:ℤ) := by conv_lhs => field_simp2
example : x / (y ^ (-3:ℤ) / x) = x ^ 2 * y ^ 3 := by conv_lhs => field_simp2
example : (x / y ^ (-3:ℤ)) * x = x ^ 2 * y ^ 3 := by conv_lhs => field_simp2
example : (x * y) / (y * x) = 1 := by conv_lhs => field_simp2
example : (x * y) * (y * x)⁻¹ = 1 := by conv_lhs => field_simp2
example : x ^ (0:ℤ) * y = y := by conv_lhs => field_simp2
example : y * (y + x) ^ (0:ℤ) * y = y ^ 2 := by conv_lhs => field_simp2
example : x * y * z = x * y * z := by conv_lhs => field_simp2
example : x * y + x * z = x * (y + z) := by conv_lhs => field_simp2
example : x / (x * y + x * z) = (y + z) ^ (-1:ℤ) := by conv_lhs => field_simp2
example : ((x ^ (2:ℤ)) ^ 3) = x ^ 6 := by conv_lhs => field_simp2
example : x ^ 3 * x⁻¹ = x ^ 2 := by conv_lhs => field_simp2
example : x / x ^ 4 = x ^ (-3:ℤ) := by conv_lhs => field_simp2
example : x ^ 1 * x ^ 2 = x ^ 3 := by conv_lhs => field_simp2
example : x * x = x ^ 2 := by conv_lhs => field_simp2
example : x ^ 3 * x ^ 42 = x ^ 45 := by conv_lhs => field_simp2

example : x / (x + 1) + y / (y + 1)
    = (x + 1) ^ (-1:ℤ) * (y + 1) ^ (-1:ℤ) * (x * (y + 1) + (x + 1) * y) := by
  conv_lhs => field_simp2

/-! ### Equality goals -/

example : (1:ℚ) / 3 + 1 / 6 = 1 / 2 := by
  field_simp2
  norm_cast

example : x / (x + y) + y / (x + y) = 1 := by
  field_simp2
  rfl

example : ((x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2)) ^ 2 + (2 * x * y / (x ^ 2 + y ^ 2)) ^ 2 = 1 := by
  field_simp2
  guard_target = (x ^ 2 - y ^ 2) ^ 2 + x ^ 2 * y ^ 2 * 2 ^ 2 = (x ^ 2 + y ^ 2) ^ 2
  sorry

-- from PythagoreanTriples
example {K : Type*} [Semifield K] (x y : K) :
    2 * (x / (y + 1)) / (1 + (x / (y + 1)) ^ 2) = x := by
  field_simp2
  guard_target = 2 * x * (y + 1) = x * ((y + 1) ^ 2 + x ^ 2)
  sorry

-- from Set.IsoIoo
example {K : Type*} [Field K] (x y z : K) :
    x / (1 - y) / (1 + y / (1 - y)) = z := by
  field_simp2
  guard_target = x = (1 - y + y) * z
  sorry

/-! ### Tests from `field_simp` file -/

/--
Test that the discharger can clear nontrivial denominators in ℚ.
-/
example (x : ℚ) (h₀ : x ≠ 0) : (4 / x)⁻¹ * ((3 * x^3) / x)^2 * ((1 / (2 * x))⁻¹)^3 = 18 * x^8 := by
  field_simp2
  guard_target = x ^ 8 * 3 ^ 2 * 2 ^ 3 = 4 * x ^ 8 * 18
  sorry
