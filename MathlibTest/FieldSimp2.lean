import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
## `field_simp` tests.
-/

private axiom test_sorry : ∀ {α}, α

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

/-- info: (x ^ 3)⁻¹ -/
#guard_msgs in
#conv field_simp2 => x ^ (-1 : ℤ) * x ^ (-2 : ℤ)

-- Cancellation: if x could be zero, we cannot cancel x * x⁻¹.

/-- info: x / x -/
#guard_msgs in
#conv field_simp2 => x * x⁻¹

/-- info: x / x -/
#guard_msgs in
#conv field_simp2 => x⁻¹ * x

/-- info: x / x -/
#guard_msgs in
#conv field_simp2 => x / x

/-- info: x ^ 2 -/
#guard_msgs in
#conv field_simp2 => x ^ 3 * x⁻¹

/-- info: (x ^ 3)⁻¹ -/
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

/-- info: (x ^ 3)⁻¹ -/
#guard_msgs in
#conv field_simp2 => x / x ^ 4

end

-- Combining this works also when other atoms are "in the way".
-- TODO: these tests are broken

/-- info: x ^ 3 * y ^ 4 -/
#guard_msgs in
#conv field_simp2 => x ^1 * y * x ^2 * y ^ 3

/-- info: x ^ 3 * y / y -/
#guard_msgs in
#conv field_simp2 => x ^ 1 * y * x ^2 * y⁻¹

variable {y' : ℚ} (hy' : y' ≠ 0)

/-- info: x ^ 3 -/
#guard_msgs in
#conv field_simp2 => x ^ 1 * y' * x ^ 2 * y'⁻¹

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

/-- info: x * y / (x * y) -/
#guard_msgs in
#conv field_simp2 => (x * y) / (y * x)

/-- info: x * (y + 1) -/
#guard_msgs in
#conv field_simp2 => x * y + x * 1

/-- info: x * y / (x * y) -/
#guard_msgs in
#conv field_simp2 => (x * y) * (y * x)⁻¹

/-- info: y -/
#guard_msgs in
#conv field_simp2 => x ^ (0:ℤ) * y

/-- info: y ^ 2 -/
#guard_msgs in
#conv field_simp2 => y * (y + x) ^ (0:ℤ) * y

/-- info: x / y -/
#guard_msgs in
#conv field_simp2 => x / y

/-- info: -(x / y) -/
#guard_msgs in
#conv field_simp2 => x / -y

/-- info: -(x / y) -/
#guard_msgs in
#conv field_simp2 => -x / y

variable (hx : x + 1 ≠ 0) in
/-- info: (x + (x + 1) * y / (y + 1)) / (x + 1) -/
#guard_msgs in
#conv field_simp2 => x / (x + 1) + y / (y + 1)

example : (1 : ℚ) = 1 := by conv_lhs => field_simp2
example : x = x := by conv_lhs => field_simp2
example : x * y = x * y := by conv_lhs => field_simp2
example : x / y = x / y := by conv_lhs => field_simp2
example : x / (y / x) = x ^ 2 / y := by conv_lhs => field_simp2
example : x / (y ^ (-3:ℤ) / x) = x ^ 2 * y ^ 3 := by conv_lhs => field_simp2
example : (x / y ^ (-3:ℤ)) * x = x ^ 2 * y ^ 3 := by conv_lhs => field_simp2
example (hx : x ≠ 0) (hy : y ≠ 0) : (x * y) / (y * x) = 1 := by conv_lhs => field_simp2
example : (x * y) / (y * x) = (x * y) / (x * y) := by conv_lhs => field_simp2
example (hx : x ≠ 0) (hy : y ≠ 0) : (x * y) * (y * x)⁻¹ = 1 := by conv_lhs => field_simp2
example : (x * y) * (y * x)⁻¹ = (x * y) / (x * y) := by conv_lhs => field_simp2
example : x ^ (0:ℤ) * y = y := by conv_lhs => field_simp2
example : y * (y + x) ^ (0:ℤ) * y = y ^ 2 := by conv_lhs => field_simp2
example : x * y * z = x * y * z := by conv_lhs => field_simp2
example : x * y + x * z = x * (y + z) := by conv_lhs => field_simp2
example (hx : x ≠ 0) : x / (x * y + x * z) = (y + z)⁻¹ := by conv_lhs => field_simp2
example : x / (x * y + x * z) = x / (x * (y + z)) := by conv_lhs => field_simp2
example : ((x ^ (2:ℤ)) ^ 3) = x ^ 6 := by conv_lhs => field_simp2
example : x ^ 3 * x⁻¹ = x ^ 2 := by conv_lhs => field_simp2
example : x / x ^ 4 = (x ^ 3)⁻¹ := by conv_lhs => field_simp2
example : x ^ 1 * x ^ 2 = x ^ 3 := by conv_lhs => field_simp2
example : x * x = x ^ 2 := by conv_lhs => field_simp2
example : x ^ 3 * x ^ 42 = x ^ 45 := by conv_lhs => field_simp2
example : x * x * x⁻¹ = x := by conv_lhs => field_simp2

example (_ : 0 < x + 1) (_ : 0 < y + 1) : x / (x + 1) + y / (y + 1)
    = (x * (y + 1) + (x + 1) * y) / ((x + 1) * (y + 1)) := by
  conv_lhs => field_simp2

-- TODO decide desired behaviour on this example
set_option linter.unusedVariables false in
example (hy : y ≠ 0) (hz : z ≠ 0) (hx : x = 0) : x / y = x / z := by
  field_simp2 -- if this cancels the `x` it renders it unsolvable
  exact test_sorry

/-! ### Equality goals -/

example : (1:ℚ) / 3 + 1 / 6 = 1 / 2 := by
  field_simp2
  guard_target = ((6:ℚ) + 3) * 2 = 6 * 3
  norm_num

-- check that `field_simp` closes goals when the equality reduces to an identity
example : x / (x + y) + y / (x + y) = 1 := by
  have : x + y ≠ 0 := test_sorry
  field_simp2

-- check that `field_simp` closes goals when the equality reduces to an identity
example : x ^ 2 * x⁻¹ = x := by field_simp2

-- -- FIXME
-- -- check that `field_simp` closes goals when a hypothesis reduces to the negation of an identity
-- example (hx : x ≠ 0) (h : x ^ 2 * x⁻¹ ≠ x) : True := by field_simp2 at h

example {a b : ℚ} (ha : a ≠ 0) : a / (a * b) + (-1) / b = 0 := by
  field_simp2
  guard_target = (1 + -1) / b = 0
  ring

example {a b : ℚ} (ha : a ≠ 0) : a / (a * b) - 1 / b = 0 := by
  field_simp2
  guard_target = (1 - 1) / b = 0
  ring

example {a b : ℚ} (h : b ≠ 0) : a / b + 2 * a / b + (-a) / b + (- (2 * a)) / b = 0 := by
  field_simp2
  guard_target = a * (1 + 2 + -1 + -2) = b * 0
  ring

example : x / y ^ 2 = (x + 1) / y := by
  field_simp2
  guard_target = x / y ^ 2 = (x + 1) / y
  exact test_sorry

-- TODO do we want the simproc to reduce this to a common denominator,
-- i.e. `x / y ^ 2 = y * (x + 1) / y ^ 2`, rather than `x * y = x + 1`?
example : x / y ^ 2 = (x + 1) / y := by
  simp only [field]
  guard_target = x / y ^ 2 = (x + 1) / y
  exact test_sorry

example : x / y = (x + 1) / y ^ 2 := by
  field_simp2
  guard_target = x / y = (x + 1) / y ^ 2
  exact test_sorry

example (hx : 0 < x) :
    ((x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2)) ^ 2 + (2 * x * y / (x ^ 2 + y ^ 2)) ^ 2 = 1 := by
  field_simp2
  guard_target = (x ^ 2 - y ^ 2) ^ 2 + x ^ 2 * y ^ 2 * 2 ^ 2 = (x ^ 2 + y ^ 2) ^ 2
  exact test_sorry

-- test the assumption discharger
example {K : Type*} [Semifield K] (x y : K) (hy : y + 1 ≠ 0) : 2 * x / (y + 1) = x := by
  field_simp2
  guard_target = 2 * x = x * (y + 1)
  exact test_sorry

-- test the assumption discharger
example {K : Type*} [Semifield K] (x y : K) (hy : y + 1 ≠ 0) : 2 * x / (y + 1) = x := by
  simp only [field]
  guard_target = 2 * x = x * (y + 1)
  exact test_sorry

-- from PythagoreanTriples
set_option linter.unusedVariables false in
example {K : Type*} [Semifield K] (hK : ∀ x : K, 1 + x ^ 2 ≠ 0) (x y : K) (hy : y + 1 ≠ 0) :
    2 * (x / (y + 1)) / (1 + (x / (y + 1)) ^ 2) = x := by
  /- TODO: re-extract this test, `Semifield` is not a strong enough typeclass. -/
  have : (y+1)^2 + x^2 ≠ 0 := test_sorry
  field_simp2
  /- TODO: do we want field_simp to cancel the x on either side? This is a consequence of which
  common factors we strip (currently the nonzero ones). -/
  guard_target = 2 * x * (y + 1) = x * ((y + 1) ^ 2 + x ^ 2)
  exact test_sorry

-- from Set.IsoIoo
-- TODO decide what pattern we expect from our users here
section

example {K : Type*} [Field K] (x y z : K) (hy : 1 - y ≠ 0) :
    x / (1 - y) / (1 + y / (1 - y)) = z := by
  have : 1 - y + y ≠ 0 := test_sorry
  field_simp2
  guard_target = x = (1 - y + y) * z
  exact test_sorry

example {K : Type*} [Field K] (x y z : K) (hy : 1 - y ≠ 0) :
    x / (1 - y) / (1 + y / (1 - y)) = z := by
  field_simp2
  ring_nf
  guard_target = x = z
  exact test_sorry

-- from PluenneckeRuzsa
-- FIXME? requires handling variable exponents
example (x z : ℚ≥0) (n : ℕ) : z * ((z / x) ^ n * x) = (z / x) ^ (n + 1) * x * x := by
  field_simp2
  exact test_sorry

end

-- test for operating in sub-expressions
set_option linter.unusedVariables false in
example (hx : y ≠ 0) {f : ℚ → ℚ} (hf : ∀ t, f t ≠ 0) :
    f (y * x / (y ^ 2 / z)) / f (z / (y / x)) = 1 := by
  field_simp2 [hf]
  ring_nf

/-! ### A bug with the simp component of the discharger

Previously `pow_ne_zero` was tagged `field_simps` and apparently took precedence in the discharger
run.
-/

example {K : Type*} [Field K] (n : ℕ) (w : K) (h0 : w ≠ 0) : w ^ n / w ^ n = 1 := by
  field_simp

/--
error: unsolved goals
x y z : ℚ
K : Type u_1
inst✝ : Field K
n : ℕ
w : K
h0 : w ≠ 0
⊢ w ^ n / w ^ n = 1
-/
#guard_msgs in
example {K : Type*} [Field K] (n : ℕ) (w : K) (h0 : w ≠ 0) : w ^ n / w ^ n = 1 := by
  field_simp2 [pow_ne_zero]

example {K : Type*} [Field K] (n : ℕ) (w : K) (h0 : w ≠ 0) : w ^ n / w ^ n = 1 := by
  field_simp2 [↓pow_ne_zero]

example {K : Type*} [Field K] (n : ℕ) (w : K) (h0 : w ≠ 0) : w ^ n / w ^ n = 1 := by
  field_simp2 [pow_ne_zero, -pow_eq_zero_iff, -pow_eq_zero_iff']

/-! ### Non-confluence issues -/

-- this initially had an infinite loop because the normalization didn't respect the simp-lemmas
-- `neg_mul` and `mul_neg`
example {K : Type*} [Field K] {a b c x : K} (P : K → Prop) : P (-(c * a * x) + -b) := by
  simp [fieldExpr]
  exact test_sorry

-- this initially had an infinite loop because the normalization didn't respect the simp-lemma
-- `one_div`
example (a : ℚ) (P : ℚ → Prop) : P (a * a⁻¹) := by
  simp [fieldExpr]
  exact test_sorry

/--
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
-- this one, from LinearAlgebra.QuadraticForm.Real, is undiagnosed
example (t : ℚ) (ht : t ≠ 0) (a : ∀ t, t ≠ 0 → ℚ) :
    (if h : t = 0 then 1 else a t h) = 1 := by
  simp only [field]

/--
error: tactic 'simp' failed, nested error:
maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
-- this one, from Analysis.SpecialFunctions.Stirling, is due to the simp-lemma `mul_inv_rev`
example (n : ℚ) (P : ℚ → Prop ): P ((4 * n)⁻¹) := by
  simp [fieldExpr]

/-! ### Testing to what extent the simproc discharger picks up hypotheses from the simp args -/
section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/- `simp [field, ...]` can use the provided arguments to prove nonzeroness directly.
Same for the old implementation (`field_simp`). -/

example  (hK : ∀ ξ : K, ξ + 1 ≠ 0) (x : K) : 1 / |x + 1| = 5 := by
  fail_if_success have : |x + 1| ≠ 0 := by positivity
  have H : |x + 1| ≠ 0 := by simp [hK x] -- this is how `field_simp` will prove nonzeroness
  clear H
  field_simp [hK x]
  guard_target = 1 = 5 * |x + 1|
  exact test_sorry

example (hK : ∀ ξ : K, ξ + 1 ≠ 0) (x : K) : 1 / |x + 1| = 5 := by
  fail_if_success have : |x + 1| ≠ 0 := by positivity
  have H : |x + 1| ≠ 0 := by simp [hK x] -- this is how `field_simp2` will prove nonzeroness
  clear H
  field_simp2 [hK x]
  guard_target = 1 = |x + 1| * 5
  exact test_sorry

example (hK : ∀ ξ : K, ξ + 1 ≠ 0) (x : K) : 1 / |x + 1| = 5 := by
  fail_if_success have : |x + 1| ≠ 0 := by positivity
  have H : |x + 1| ≠ 0 := by simp [hK x] -- this is how `simp [field, ...]` will prove nonzeroness
  clear H
  simp [field, hK x]
  guard_target = 1 = |x + 1| * 5
  exact test_sorry

/- `simp [field, ...]` **can't** pass the provided arguments as hypotheses to `positivity`.
Same for the old implementation (`field_simp`). -/

/-- error: simp made no progress -/
#guard_msgs in
-- doesn't cancel
example (hK : ∀ ξ : K, 0 < ξ + 1) (x : K) : 1 / (x + 1) = 5 := by
  field_simp [hK x]

-- doesn't cancel
set_option linter.unusedVariables false in
example (hK : ∀ ξ : K, 0 < ξ + 1) (x : K) : 1 / (x + 1) = 5 := by
  simp [field, hK x]
  guard_target = (x + 1)⁻¹ = 5
  exact test_sorry

-- cancels when the hypothesis is brought out for use by `positivity`
example (hK : ∀ ξ : K, 0 < ξ + 1) (x : K) : 1 / (x + 1) = 5 := by
  have := hK x
  field_simp
  guard_target = 1 = 5 * (x + 1)
  exact test_sorry

end

/-! ### Tests to distinguish from former implementation -/

example : x ^ 2 * x⁻¹ = x := by field_simp2
example (hx: x ≠ 0) : x / (x * y) = 1 / y := by field_simp2

example : x ^ 2 * x⁻¹ = x := by simp only [field]
example (hx: x ≠ 0) : x / (x * y) = 1 / y := by simp only [field]

/--
error: unsolved goals
x y z : ℚ
⊢ x ^ 2 / x = x
-/
#guard_msgs in
example : x ^ 2 * x⁻¹ = x := by field_simp

/-- error: simp made no progress -/
#guard_msgs in
example (hx: x ≠ 0) : x / (x * y) = 1 / y := by field_simp

set_option linter.unusedVariables false in
/- This example demonstrates a feature/bug of the former implementation: it used the `field_simp`
discharger on the side conditions of other simp-lemmas, not just the `field_simp` simp set. -/
example (m n : ℕ) (h : m ≤ n) (hm : (2:ℚ) < n - m) : (n:ℚ) / (n - m) = 1 / ↑(n - m) * n := by
  field_simp

/--
error: unsolved goals
x y z : ℚ
m n : ℕ
h : m ≤ n
hm : 2 < ↑n - ↑m
⊢ ↑n = ↑n * (↑n - ↑m) / ↑(n - m)
-/
#guard_msgs in
example (m n : ℕ) (h : m ≤ n) (hm : (2:ℚ) < n - m) : (n:ℚ) / (n - m) = 1 / ↑(n - m) * n := by
  simp [field]

set_option linter.unusedVariables false in
/- The new implementation requires that such a discharger must be invoked explicitly. -/
example (m n : ℕ) (h : m ≤ n) (hm : (2:ℚ) < n - m) : (n:ℚ) / (n - m) = 1 / ↑(n - m) * n := by
  simp (disch := assumption) [field]

/-! ### Tests from the former `field_simp` file -/

set_option linter.unusedVariables false in
/--
Test that the discharger can clear nontrivial denominators in ℚ.
-/
example (x : ℚ) (h₀ : x ≠ 0) :
    (4 / x)⁻¹ * ((3 * x ^ 3) / x) ^ 2 * ((1 / (2 * x))⁻¹) ^ 3 = 18 * x ^ 8 := by
  field_simp2
  guard_target = (3 : ℚ) ^ 2 * 2 ^ 3 = 4 * 18
  exact test_sorry

/-
Check that `field_simp` works for units of a ring.
-/

variable {R : Type _} [CommRing R] (a b c d e f g : R) (u₁ u₂ : Rˣ)

-- /--
-- Check that `divp_add_divp_same` takes priority over `divp_add_divp`.
-- -/
-- example : a /ₚ u₁ + b /ₚ u₁ = (a + b) /ₚ u₁ := by field_simp2

-- /--
-- Check that `divp_sub_divp_same` takes priority over `divp_sub_divp`.
-- -/
-- example : a /ₚ u₁ - b /ₚ u₁ = (a - b) /ₚ u₁ := by field_simp2

-- /-
-- Combining `eq_divp_iff_mul_eq` and `divp_eq_iff_mul_eq`.
-- -/
-- example : a /ₚ u₁ = b /ₚ u₂ ↔ a * u₂ = b * u₁ := by field_simp2

-- /--
-- Making sure inverses of units are rewritten properly.
-- -/
-- example : ↑u₁⁻¹ = 1 /ₚ u₁ := by field_simp2

-- /--
-- Checking arithmetic expressions.
-- -/
-- example : (f - (e + c * -(a /ₚ u₁) * b + d) - g) =
--     (f * u₁ - (e * u₁ + c * (-a) * b + d * u₁) - g * u₁) /ₚ u₁ := by field_simp2

-- /--
-- Division of units.
-- -/
-- example : a /ₚ (u₁ / u₂) = a * u₂ /ₚ u₁ := by field_simp2

-- example : a /ₚ u₁ /ₚ u₂ = a /ₚ (u₂ * u₁) := by field_simp2

set_option linter.unusedVariables false in
/--
Test that the discharger can clear nontrivial denominators in ℚ.
-/
example (x : ℚ) (h₀ : x ≠ 0) :
    (4 / x)⁻¹ * ((3 * x ^ 3) / x) ^ 2 * ((1 / (2 * x))⁻¹) ^ 3 = 18 * x ^ 8 := by
  field_simp2
  ring

set_option linter.unusedVariables false in
/-- Use a custom discharger -/
example (x : ℚ) (h₀ : x ≠ 0) :
    (4 / x)⁻¹ * ((3 * x ^ 3) / x) ^ 2 * ((1 / (2 * x))⁻¹) ^ 3 = 18 * x ^ 8 := by
  field_simp2 (discharger := simp; assumption)
  ring

-- /-- Specify a simp config. -/
-- example (x : ℚ) (h₀ : x ≠ 0) :
--     (4 / x)⁻¹ * ((3 * x ^ 3) / x) ^ 2 * ((1 / (2 * x))⁻¹) ^ 3 = 18 * x ^ 8 := by
--   fail_if_success field_simp2 (config := {maxSteps := 0})
--   field_simp2 (config := {})
--   ring

-- example {x y z w : ℚ} (h : x / y = z / w) (hy : y ≠ 0) (hw : w ≠ 0) : x * w = z * y := by
--   field_simp2 at h
--   assumption

-- -- An example of "unfolding" `field_simps` to its "definition"
-- example {aa : ℚ} (ha : (aa : ℚ) ≠ 0) (hb : 2 * aa = 3) : (1 : ℚ) / aa = 2/ 3 := by
--   simp (disch := field_simp_discharge) [-one_div, -one_divp, -mul_eq_zero, field_simps]
--   rw [hb]
