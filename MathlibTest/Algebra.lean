import Mathlib.Tactic.Algebra.Basic

axiom sorryAlgebraTest {P : Prop} : P

example (x : ℚ) (n : ℕ) : n • x + x = (n: ℤ) • x + x := by
  algebra

example (x : ℚ) (a : ℤ) : algebraMap ℤ ℚ a * x = a • x := by
  algebra

example {R A : Type*} {a : R} [CommSemiring R] [CommSemiring A] [Algebra R A] (x : A) :
    a • x = a • x := by
  algebra with R

-- Test universe polymorphism.
example {R : Type} {A : Type 1} {a : R} [CommSemiring R] [CommSemiring A] [Algebra R A] (x : A) :
    a • x = a • x := by
  algebra with R

example {R A : Type*} {a b : R} [CommSemiring R] [CommSemiring A] [Algebra R A] (x y : A) :
    (a + b) • (x + y) = b • x + a • (x + y) + b • y := by
  algebra

example {R A : Type*} {a b : R} [CommRing R] [CommRing A] [Algebra R A] (x y : A) :
    (a - b) • (x + y) = - b • x + a • (x + y) - b • y := by
  algebra

example {x : ℚ} {y : ℤ} : y • x + (1:ℤ) • x = (1 + y) • x := by
  algebra

example (x : ℚ) :  x + x = (2 : ℤ) • x := by
  algebra

example (x y : ℚ) : x + y  = y + x := by
  algebra

example (x y : ℚ) : x + y*x + x + y  = (x + x) + (x*y + y) := by
  algebra

example (x : ℚ) : x + x + x  = 3 * x := by
  algebra

example (x : ℚ) : (x + x) + (x + x)  = x + x + x + x := by
  algebra

example (x y : ℚ) : (x + y)*(x+y) = x*x + 2 * x * y + y * y := by
  algebra

-- Handle negative integer constants
example (x y : ℚ) : (x + (-3) * y)*(x+y) = x*x + (-2) * x * y + (-3) * y^2 := by
  algebra with ℤ

example (x : ℚ) : (x + 1)^3 = x^3 + 3*x^2 + 3*x + 1 := by
  algebra

example (x : ℚ) (n : ℕ) : (x + 2) ^ (2 * n+1) = ((x+2)^n)^2 * (x+2) := by
  algebra

-- Test positive rational constants
example (x : ℚ) : (1/2) * x = x * (1/2) := by
  algebra

example (x : ℚ) : (3/4) * x + (1/4) * x = x := by
  algebra with ℚ

example (x y : ℚ) : (1/2) * (x + y) = (1/2) * x + (1/2) * y := by
  algebra

example (x : ℚ) : (2/3) * x + (1/3) * x = x := by
  algebra with ℚ

-- Test negative rational constants
example (x : ℚ) : (-1/2) * x = -(x * (1/2)) := by
  algebra

example (x : ℚ) : (-3/4) * x + (3/4) * x = 0 := by
  algebra

example (x y : ℚ) : (-1/2) * x + (-1/2) * y = (-1/2) * (x + y) := by
  algebra

-- Test mixed rational and integer operations
example (x : ℚ) : 2 * x + (1/2) * x = (5/2) * x := by
  algebra

example (x : ℚ) : (1/2) * x - x = (-1/2) * x := by
  algebra

example (x : ℚ) : 3 * x - (1/4) * x = (11/4) * x := by
  algebra

-- Test rational constants in polynomial operations
example (x : ℚ) : ((1/2) * x + (1/3))^2 = (1/4) * x^2 + (1/3) * x + (1/9) := by
  algebra

example (x y : ℚ) : ((1/2) * x + (1/2) * y)^2 = (1/4) * (x^2 + 2 * x * y + y^2) := by
  algebra

example (x : ℚ) : (x + (2/3))^3 = x^3 + 2 * x^2 + (4/3) * x + (8/27) := by
  algebra

-- Test rational constants with scalar multiplication
example (x : ℚ) : (1/2 : ℚ) • x = (1/2) * x := by
  algebra

example (x : ℚ) : (3/4 : ℚ) • x + (1/4 : ℚ) • x = x := by
  algebra

-- Test with Algebra over ℚ
example {A : Type*} [CommRing A] [Algebra ℚ A] (x y : A) :
    (1/2 : ℚ) • (x + y) = (1/2 : ℚ) • x + (1/2 : ℚ) • y := by
  algebra

example {A : Type*} [CommRing A] [Algebra ℚ A] (x : A) :
    (3/4 : ℚ) • x + (1/4 : ℚ) • x = x := by
  algebra with ℚ


/- This test exists to record the fact that `algebra` might infer the wrong ring
if there are multiple incomparable rings. -/
/--
error: algebra failed, algebra expressions not equal
A : Type u_1
R : Type u_2
R' : Type u_3
inst✝⁴ : CommRing A
inst✝³ : CommRing R
inst✝² : CommRing R'
inst✝¹ : Algebra R A
inst✝ : Algebra R' A
r : R
r' : R'
x : A
⊢ x * (algebraMap R' A) r' + r • x * (algebraMap R' A) 1 + 1 • x * (algebraMap R' A) 1 =
    x * (algebraMap R' A) r' + (r + 1) • x * (algebraMap R' A) 1
-/
#guard_msgs in
example {A R R' : Type*} [CommRing A] [CommRing R] [CommRing R'] [Algebra R A] [Algebra R' A] (r : R) (r' : R') (x : A) :
(r : R) • x + (1 : R) • x + (r' : R') • x = (r + 1 : R) • x + (r' : R') • x := by
  algebra

example {A R R' : Type*} [CommRing A] [CommRing R] [CommRing R'] [Algebra R A] [Algebra R' A] (r : R) (r' : R') (x : A) :
(r : R) • x + (1 : R) • x + (r' : R') • x = (r + 1 : R) • x + (r' : R') • x := by
  algebra with R

example {A R R' : Type*} [CommRing A] [CommRing R] [CommRing R'] [Algebra R A] [Algebra R' A] (r : R) (r' : R') (x : A) :
(r : R) • x + (1 : ℕ) • x + (r' : R') • x = (r' : R') • x + (1 : ℕ) • x + (r : R) • x:= by
  algebra

/--
info: Try this:
  [apply] algebra_nf with _
  ⏎
   'algebra_nf' without specifying the base ring is unstable. Use `algebra_nf with` instead.
-/
#guard_msgs in
example (x : ℚ) (a : ℤ) : algebraMap ℤ ℚ a * x = a • x := by
  algebra_nf

/--
info: Try this:
  [apply] algebra_nf with _
  ⏎
   'algebra_nf' without specifying the base ring is unstable. Use `algebra_nf with` instead.
-/
#guard_msgs in
example (x : ℚ) (n : ℕ) : n • x + x = (n : ℤ) • x + x := by
  algebra_nf
  /- This behaviour is not desirable, it would be better if both sides were lifted to nsmul or zsmul.
  We keep the test to document this behaviour. For this reason we push users to provide an explicit
  base ring. -/
  guard_target = (1 + n) • x = (1 + ↑n : ℤ) • x
  exact sorryAlgebraTest

/--
info: Try this:
  [apply] algebra_nf with _
  ⏎
   'algebra_nf' without specifying the base ring is unstable. Use `algebra_nf with` instead.
-/
#guard_msgs in
example (x y : ℚ) : x + (y)*(x+y) = 0 := by
  algebra_nf
  guard_target = x + x * y + y ^ 2 = 0
  exact sorryAlgebraTest

example (x y : ℚ) : x + (x)*(x + -y) = 0 := by
  algebra_nf with ℤ
  guard_target = x - (x * y) + x ^ 2 = 0
  exact sorryAlgebraTest

example (x : ℚ) (n : ℕ) : (x^n - 1)^2 = 0 := by
  algebra_nf with ℤ
  guard_target =  1 - 2 * x ^ n + x ^ (n * 2) = 0
  exact sorryAlgebraTest

-- Test algebra_nf with rational constants
example (x : ℚ) : (1/2) * x + (1/3) * x = 1 := by
  algebra_nf with ℚ
  guard_target = (5/6 : ℚ) * x = 1
  exact sorryAlgebraTest

example (x y : ℚ) : ((2/5) * x + (3/5) * y)^2 = 0 := by
  algebra_nf with ℚ
  guard_target = (12 / 25 : ℚ) * (x * y) + (4 / 25 : ℚ) * x ^ 2 + (9 / 25 : ℚ) * y ^ 2 = 0
  exact sorryAlgebraTest

example {R A : Type*} [Field R] [CharZero R] [CommRing A] [Algebra R A] (x : A) (r : R) :
    ((4/3 : R) • x + r • (1 : A))^2 = 0 := by
  algebra_nf with R
  guard_target = r ^ 2 • (1 : A) + (r * (8 / 3) : R) • x + (16 / 9 : R) • x ^ 2 = 0
  exact sorryAlgebraTest

/- Record the fact that we turn scalar multiplication by a constant into normal multiplication
where possible. -/
example {R A : Type*} [Field R] [CharZero R] [Field A] [Algebra R A] (x : A) (r : R) :
    ((4/3 : R) • x + r • (1 : A))^2 = 0 := by
  algebra_nf with R
  guard_target = r ^ 2 • (1 : A) + (r * (8 / 3) : R) • x + (16 / 9 : A) * x ^ 2 = 0
  exact sorryAlgebraTest
