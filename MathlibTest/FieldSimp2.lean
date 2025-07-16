import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FieldSimp2
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
## `field_simp` tests.
-/

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

/-- info: x ^ 3 * (y / y) -/
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

/-- info: x / x * (y / y) -/
#guard_msgs in
#conv field_simp2 => (x * y) / (y * x)

/-- info: x * (y + 1) -/
#guard_msgs in
#conv field_simp2 => x * y + x * 1

/-- info: x / x * (y / y) -/
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

variable (hx : x + 1 ≠ 0) in
/-- info: (x + 1) ^ (-1) * (x + (x + 1) * y * (y + 1) ^ (-1)) -/
#guard_msgs in
#conv field_simp2 => x / (x + 1) + y / (y + 1)

example : (1 : ℚ) = 1 := by conv_lhs => field_simp2
example : x = x := by conv_lhs => field_simp2
example : x * y = x * y := by conv_lhs => field_simp2
example : x / y = x * y ^ (-1:ℤ) := by conv_lhs => field_simp2
example : x / (y / x) = x ^ 2 * y ^ (-1:ℤ) := by conv_lhs => field_simp2
example : x / (y ^ (-3:ℤ) / x) = x ^ 2 * y ^ 3 := by conv_lhs => field_simp2
example : (x / y ^ (-3:ℤ)) * x = x ^ 2 * y ^ 3 := by conv_lhs => field_simp2
example (hx : x ≠ 0) (hy : y ≠ 0) : (x * y) / (y * x) = 1 := by conv_lhs => field_simp2
example : (x * y) / (y * x) = x / x * (y / y) := by conv_lhs => field_simp2
example (hx : x ≠ 0) (hy : y ≠ 0) : (x * y) * (y * x)⁻¹ = 1 := by conv_lhs => field_simp2
example : (x * y) * (y * x)⁻¹ = x / x * (y / y) := by conv_lhs => field_simp2
example : x ^ (0:ℤ) * y = y := by conv_lhs => field_simp2
example : y * (y + x) ^ (0:ℤ) * y = y ^ 2 := by conv_lhs => field_simp2
example : x * y * z = x * y * z := by conv_lhs => field_simp2
example : x * y + x * z = x * (y + z) := by conv_lhs => field_simp2
example (hx : x ≠ 0) : x / (x * y + x * z) = (y + z) ^ (-1:ℤ) := by conv_lhs => field_simp2
example : x / (x * y + x * z) = (x / x) * (y + z) ^ (-1:ℤ) := by conv_lhs => field_simp2
example : ((x ^ (2:ℤ)) ^ 3) = x ^ 6 := by conv_lhs => field_simp2
example : x ^ 3 * x⁻¹ = x ^ 2 := by conv_lhs => field_simp2
example : x / x ^ 4 = x ^ (-3:ℤ) := by conv_lhs => field_simp2
example : x ^ 1 * x ^ 2 = x ^ 3 := by conv_lhs => field_simp2
example : x * x = x ^ 2 := by conv_lhs => field_simp2
example : x ^ 3 * x ^ 42 = x ^ 45 := by conv_lhs => field_simp2
example : x * x * x⁻¹ = x := by conv_lhs => field_simp2

example (_ : 0 < x + 1) (_ : 0 < y + 1) : x / (x + 1) + y / (y + 1)
    = (x + 1) ^ (-1:ℤ) * (y + 1) ^ (-1:ℤ) * (x * (y + 1) + (x + 1) * y) := by
  conv_lhs => field_simp2

-- TODO decide desired behaviour on this example
example (hy : y ≠ 0) (hz : z ≠ 0) (hx : x = 0) : x / y = x / z := by
  field_simp2 -- if this cancels the `x` it renders it unsolvable
  sorry

/-! ### Equality goals -/

example : (1:ℚ) / 3 + 1 / 6 = 1 / 2 := by
  field_simp2
  norm_num

example : x / (x + y) + y / (x + y) = 1 := by
  have : x + y ≠ 0 := sorry
  field_simp2
  rfl

example (hx : 0 < x) : ((x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2)) ^ 2 + (2 * x * y / (x ^ 2 + y ^ 2)) ^ 2 = 1 := by
  field_simp2
  guard_target = (x ^ 2 - y ^ 2) ^ 2 + x ^ 2 * y ^ 2 * 2 ^ 2 = (x ^ 2 + y ^ 2) ^ 2
  sorry

-- from PythagoreanTriples
example {K : Type*} [Semifield K] (hK : ∀ x : K, 1 + x ^ 2 ≠ 0) (x y : K) (hy : y + 1 ≠ 0) :
    2 * (x / (y + 1)) / (1 + (x / (y + 1)) ^ 2) = x := by
  /- TODO: re-extract this test, `Semifield` is not a strong enough typeclass. -/
  have : (y+1)^2 + x^2 ≠ 0 := by
    sorry
  field_simp2
  /- TODO: do we want field_simp to cancel the x on either side? This is a consequence of how
    we defined qNF.gcd -/
  guard_target = 2 *  (y + 1) = ((y + 1) ^ 2 + x ^ 2)
  sorry

-- from Set.IsoIoo
-- TODO decide what pattern we expect from our users here
section

example {K : Type*} [Field K] (x y z : K) (hy : 1-y ≠ 0) :
    x / (1 - y) / (1 + y / (1 - y)) = z := by
  have : 1 - y + y ≠ 0 := by
    sorry
  field_simp2
  guard_target = x = (1 - y + y) * z
  sorry

example {K : Type*} [Field K] (x y z : K) (hy : 1-y ≠ 0) :
    x / (1 - y) / (1 + y / (1 - y)) = z := by
  field_simp2
  ring_nf
  field_simp2
  guard_target = x = z
  sorry

end

/-! ### Tests from the former `field_simp` file -/

/--
Test that the discharger can clear nontrivial denominators in ℚ.
-/
example (x : ℚ) (h₀ : x ≠ 0) : (4 / x)⁻¹ * ((3 * x^3) / x)^2 * ((1 / (2 * x))⁻¹)^3 = 18 * x^8 := by
  field_simp2
  guard_target = (3 : ℚ) ^ 2 * 2 ^ 3 = 4 * 18
  sorry

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

/--
Test that the discharger can clear nontrivial denominators in ℚ.
-/
example (x : ℚ) (h₀ : x ≠ 0) :
    (4 / x)⁻¹ * ((3 * x^3) / x)^2 * ((1 / (2 * x))⁻¹)^3 = 18 * x^8 := by
  field_simp2
  ring

/-- Use a custom discharger -/
example (x : ℚ) (h₀ : x ≠ 0) :
    (4 / x)⁻¹ * ((3 * x^3) / x)^2 * ((1 / (2 * x))⁻¹)^3 = 18 * x^8 := by
  field_simp2 (discharger := simp; assumption)
  ring

-- /-- Specify a simp config. -/
-- example (x : ℚ) (h₀ : x ≠ 0) :
--     (4 / x)⁻¹ * ((3 * x^3) / x)^2 * ((1 / (2 * x))⁻¹)^3 = 18 * x^8 := by
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
