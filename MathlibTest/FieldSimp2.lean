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

section

-- TODO decide desired behaviour on this example
set_option linter.unusedVariables false in
example (hy : y ≠ 0) (hz : z ≠ 0) (hx : x = 0) : x / y = x / z := by
  field_simp2 -- if this cancels the `x` it renders it unsolvable
  exact test_sorry

/-! ### Equality goals -/

-- check that `field_simp` closes goals when the equality reduces to an identity
example : x ^ 2 * x⁻¹ = x := by field_simp2

-- -- FIXME
-- -- check that `field_simp` closes goals when a hypothesis reduces to the negation of an identity
-- example (hx : x ≠ 0) (h : x ^ 2 * x⁻¹ ≠ x) : True := by field_simp2 at h

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
