/-
Copyright (c) 2025 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/
import Mathlib.Tactic.Module

open Lean hiding Module
open Meta Elab Qq Mathlib.Tactic List Mathlib.Tactic.Module

namespace Mathlib.Tactic.Algebra

open Mathlib.Meta AtomM

attribute [local instance] monadLiftOptionMetaM

/-

Comments:

To implement `smul` need `mul` to handle the case where the two scalar rings are equal
To implement `mul` need `smul` to handle $(r₁ • s) * (r₂ • s') = (r₁ • r₂) • (s * s'), so is this
one big mutually inductive family?

Also need `add` to implement `mul` properly, so some work to be done.

There's a problem in `matchRingsSMul` when the two rings are defeq. I don't think there is a great
way to cast one of the ExProds to the other.
-/

section ExSum

set_option linter.style.longLine false


open Ring in
mutual

inductive ExBase : ∀ {v: Lean.Level} {A : Q(Type v)} (_ : Q(CommSemiring $A)), (a : Q($A)) → Type
  | one {w : Lean.Level} {A : Q(Type w)} {sA : Q(CommSemiring $A)} : ExBase q($sA) q((1 : $A))
  | sum {u : Level} {A : Q(Type u)} {sA : Q(CommSemiring $A)} {a : Q($A)} (va : ExSum q($sA) q($a)) : ExBase q($sA) q($a)

/-- A polynomial expression, which is a sum of monomials. -/
inductive ExSum : ∀ {v: Lean.Level} {A : Q(Type v)} (_ : Q(CommSemiring $A)), (a : Q($A)) → Type
  -- | unsafeCast {u v : Lean.Level} {A : Q(Type u)} (B : Q(Type v))
  --   {a : Q($A)} (va : ExSum A a) : ExSum q($B) (q($a):)
  | zero {w : Lean.Level} {A : Q(Type w)} {sA : Q(CommSemiring $A)} : ExSum  q($sA) q(((nat_lit 0).rawCast:$A))
  /-- A sum `a + b` is a polynomial if `a` is a monomial and `b` is another polynomial. -/
  | add {v w: Lean.Level} {R : Q(Type v)} {A : Q(Type w)}
    {sR : Q(CommSemiring $R)} {sA : Q(CommSemiring $A)} {r : Q($R)}
    {a b : Q($A)} (sAlg : Q(Algebra $R $A)) :
    ExBase q($sR) q($r) → ExProd q($sA) q($a) → ExSum q($sA) q($b) →
      ExSum q($sA) q($r • $a + $b)

end


mutual
def ExBase.toString {v: Lean.Level} {A : Q(Type v)} (sA : Q(CommSemiring $A)) (a : Q($A)) :
  ExBase sA a → String
  | .one => "one"
  | .sum va => va.toString

def ExSum.toString {v: Lean.Level} {A : Q(Type v)} (sA : Q(CommSemiring $A)) (a : Q($A)) :
  ExSum sA a → String
    | .zero => "zero"
    -- | .one => "one"
    | .add _ vr _ vt => s!"add with r = {vr.toString}, tail = {vt.toString}"

end

instance {v : Level} {A : Expr} {sA : Expr} {a : Expr} : ToString (@ExSum v A sA a) where
  toString := ExSum.toString sA a

-- def ExSum.cmps {v: Lean.Level} {A : Q(Type v)} {sA : Q(CommSemiring $A)} {a : Q($A)} :
--   ExSum q($sA) a → List Ordering
--   | .add _ _ va (.add s vr vb vt) =>
--     va.cmp vb :: (ExSum.add s vr vb vt).cmps
--   | _ => []

-- #exit
-- unsafe def _root_.Mathlib.Tactic.Ring.ExBase.cast {u : Level} {A₁ : Q(Type u)} {A₂ : Q(Type u)} {sA₁ : _} (sA₂ : _) (hdef : $A₁ =Q $A₂) {a₁ : Q($A₁)}
--   (vr₁ : Ring.ExBase sA₁ q($a₁)) : (a₂ : Q($A₂)) × Ring.ExBase sA₂ q($a₂) := match vr₁ with
--   | .atom (e := e) id =>
--     let e : Q($A₂) := e
--     ⟨_, .atom (e := e) id⟩
--   | _ =>
--     sorry

-- unsafe def _root_.Mathlib.Tactic.Ring.ExProd.unsafeCast {u : Level} {A₁ : Q(Type u)} {A₂ : Q(Type u)} {sA₁ : _} (sA₂ : _) (hdef : $A₁ =Q $A₂) {a₁ : Q($A₁)}
--   (vr₁ : Ring.ExProd sA₁ q($a₁)) : (a₂ : Q($A₂)) × Ring.ExProd sA₂ q($a₂) := match vr₁ with
--   | .const (e := e) value hyp =>
--     let e' : Q($A₂) := e
--     ⟨e, .const (e := e') value hyp⟩
--   | .mul (x := x) vx ve vb .. =>
--     -- let x' : Q($A₂) := x
--     let ⟨_, vx'⟩ := vx.unsafeCast sA₂ hdef
--     let ⟨_, vb'⟩ := vb.unsafeCast sA₂ hdef
--     ⟨_, .mul vx' ve vb'⟩

partial def _root_.Mathlib.Tactic.Ring.ExProd.atomsList {u : Level} {A₁ : Q(Type u)} {sA₁ : _} {a₁ : Q($A₁)}
  (vr₁ : Ring.ExProd sA₁ q($a₁)) : List ℕ := match vr₁ with
  | .const (e := e) value hyp =>
    []
  | .mul (x := x) (.atom id ..) ve vb .. =>
    id :: vb.atomsList
    -- let x' : Q($A₂) := x
  | _ =>
    []

instance {u : Level} {A : Q(Type u)} {sA : Q(CommSemiring $A)} :
  Inhabited ((e : Q($A)) ×  ((ExSum q($sA)) q($e))) := ⟨_, .zero⟩

partial def ExSum.cast {u v : Level} {A₁ : Q(Type u)} {sA₁ : Q(CommSemiring $A₁)} {A₂ : Q(Type v)}
  (sA₂ : Q(CommSemiring $A₂)) {a₁ : Q($A₁)}
  (vr₁ : ExSum q($sA₁) q($a₁)) : (a₂ : Q($A₂)) × ExSum q($sA₂) q($a₂) :=
  match vr₁ with
  | zero =>
    ⟨_, .zero⟩
  | @add v' w' R A sR sA r a t sAlg vr va vt  =>
    have : w' =QL v := ⟨⟩
    have : $A =Q $A₂ := ⟨⟩
    have : $sA =Q $sA₂ := ⟨⟩
    have sAlg' : Q(Algebra $R $A₂) := sAlg
    let ⟨_, vt⟩ := vt.cast (v := v) sA₂
    let ⟨_, va⟩ := va.cast (sβ := sA₂)
    ⟨_, .add (sA := sA₂) sAlg' vr va vt ⟩

partial def ExBase.cast {u v : Level} {A₁ : Q(Type u)} {sA₁ : Q(CommSemiring $A₁)} {A₂ : Q(Type v)}
  (sA₂ : Q(CommSemiring $A₂)) {a₁ : Q($A₁)}
  (vr₁ : ExBase q($sA₁) q($a₁)) : (a₂ : Q($A₂)) × ExBase q($sA₂) q($a₂) :=
  match vr₁ with
  | one =>
    ⟨_, .one⟩
  | sum vr =>
    let ⟨_, vr'⟩ := vr.cast sA₂
    ⟨_, .sum (vr')⟩

def sℕ : Q(CommSemiring ℕ) := q(Nat.instCommSemiring)


def ofProd {u : Level}  {A : Q(Type u)} (sA : Q(CommSemiring $A))
  {e : Q($A)} (prod : Ring.ExProd q($sA) q($e)) :=
  ExSum.add (q(Semiring.toNatAlgebra) : Q(Algebra ℕ $A)) (.one) prod (.zero)


namespace ExSum

end ExSum
end ExSum

structure Result {u : Lean.Level} {A : Q(Type u)} (E : Q($A) → Type) (e : Q($A)) where
  /-- The normalized result. -/
  expr : Q($A)
  /-- The data associated to the normalization. -/
  val : E expr
  /-- A proof that the original expression is equal to the normalized result. -/
  proof : Q($e = $expr)

def ExBase.toExSum {v: Lean.Level} {A : Q(Type v)} (sA : Q(CommSemiring $A)) (a : Q($A)) :
  ExBase q($sA) q($a) → Result (ExSum q($sA)) a
  | .one => ⟨_, ofProd sA (.const (e := q(1:$A)) 1 none), q(sorry)⟩
  | .sum va => ⟨_, va, q(sorry)⟩

section Proofs
variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A] {e e' ea a a' : A} {r er : R}

theorem atom_pf (h : e = a):
    e = ((nat_lit 1).rawCast : R) • (a ^ (nat_lit 1).rawCast * (nat_lit 1).rawCast) +
      (Nat.rawCast 0) := by
  simp [h]

theorem smul_zero_rawCast : r • ((nat_lit 0).rawCast : A) = (nat_lit 0).rawCast := by
  simp

theorem smul_congr (hr : r = er) (ha : a = ea) (h : er • ea = e'): r • a = e' := by
  rw [hr, ha, h]

theorem add_rawCast_zero : a + Nat.rawCast 0 = a := by
  simp


lemma mul_natCast_zero {R : Type*} [CommSemiring R] (r : R):
    r * (Nat.rawCast 0 : R) = Nat.rawCast 0 := by
  simp

class LawfulHMul (R₁ R₂ : Type*) [CommSemiring R₁] [CommSemiring R₂]  [HMul R₁ R₂ R₁] where
  mul_zero : ∀ r₁ : R₁, r₁ * (0 : R₂) = 0
  zero_mul : ∀ r₂ : R₂, (0 : R₁) * r₂ = 0
  mul_one : ∀ r₁ : R₁, r₁ * (1 : R₂) = r₁
  cast : R₁ → R₂
  cast_mul : ∀ r₁ : R₁, ∀ r₂ : R₂, cast (r₁ * r₂) = cast r₁ * r₂
  cast_one : cast 1 = 1
  cast_zero : cast 0 = 0

attribute [local simp] LawfulHMul.mul_zero LawfulHMul.zero_mul LawfulHMul.cast_mul
  LawfulHMul.cast_one LawfulHMul.cast_zero

-- theorem test [Algebra R ℕ] : r • 1 =

lemma hmul_zero_natCast {R₁ R₂ : Type*} [CommSemiring R₁] [CommSemiring R₂]
    [HMul R₁ R₂ R₁] [LawfulHMul R₁ R₂] (r₁ : R₁):
  r₁ * (Nat.rawCast 0 : R₂) = Nat.rawCast 0 := by
  simp [LawfulHMul.mul_zero]

lemma hmul_cast_one_mul {R₁ R₂ : Type*} [CommSemiring R₁] [CommSemiring R₂]
    [HMul R₁ R₂ R₁] [LawfulHMul R₁ R₂] (r₂ : R₂) :
    (LawfulHMul.cast ((1:R₁) * r₂) : R₂) = (1 : ℕ) •  r₂ + (Nat.rawCast 0:R₂) := by
  simp

lemma hmul_cast_zero_mul {R₁ R₂ : Type*} [CommSemiring R₁] [CommSemiring R₂]
    [HMul R₁ R₂ R₁] [LawfulHMul R₁ R₂] (r₂ : R₂) :
    (LawfulHMul.cast ((Nat.rawCast 0:R₁) * r₂) : R₂) = (Nat.rawCast 0:R₂) := by
  simp

local instance {R : Type*} [CommSemiring R] : LawfulHMul R R where
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_one := mul_one
  cast := id
  cast_mul := fun _ _ ↦ rfl
  cast_one := rfl
  cast_zero := rfl

end Proofs

-- variable {u v w : Level} {R : Q(Type u)} {A : Q(Type v)} (sA : Q(CommSemiring $A))
--   (sR : Q(CommSemiring $R)) (sAlg : Q(Algebra $R $A))

def evalAtom {v : Level}  {A : Q(Type v)} (sA : Q(CommSemiring $A)) (e : Q($A)) :
    AtomM (Result (ExSum q($sA)) q($e)) := do
  let r ← (← read).evalAtom e
  have e' : Q($A) := r.expr
  let (i, ⟨a', _⟩) ← addAtomQ e'
  let ve' := ofProd sA <|
    (Ring.ExBase.atom i (e := a')).toProd (Ring.ExProd.mkNat Ring.sℕ 1).2
  pure ⟨_, ve', match r.proof? with
  | none =>
      have : $e =Q $a' := ⟨⟩
      (q(atom_pf rfl))
  | some (p : Q($e = $a')) => (q(atom_pf $p))⟩
/- Implementation taken from Tactic.Module -/

partial def _root_.Mathlib.Tactic.Ring.ExProd.extractConst {u : Level} {A : Q(Type u)}
    {sA : Q(CommSemiring $A)}
    {a : Q($A)} :
    Ring.ExProd sA a →
    MetaM (Σ (n : ℕ), Σ a' : Q($A), Ring.ExProd q($sA) a' × Q($a = $n * $a'))
  | .const c _ => do
    if c < 0 then
      throwError "Negative constants have not been implemented"
    if c.den ≠ 1 then
      throwError "Rational constants have not been implemented"
    have n : ℕ := c.num.natAbs
    /- TODO:  _are_ these defeq?-/
    have : $a =Q $n * 1 := ⟨⟩
    pure ⟨n, q(1 : $A), .const 1, q(sorry)⟩
  | .mul va ve vb => do
    let ⟨n, b', vb', pb'⟩ ← vb.extractConst
    return ⟨n, _, .mul va ve vb', q(sorry)⟩

-- TODO: decide if this is a good idea globally in
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/.60MonadLift.20Option.20.28OptionT.20m.29.60/near/469097834
private local instance {m : Type* → Type*} [Pure m] : MonadLift Option (OptionT m) where
  monadLift f := .mk <| pure f

mutual
-- TODO: for now, we'll assume all constants are natural numbers. Generally these can be arbitrary
-- rational numbers
-- Supporting negative numbers is a bit annoying, since we can't guarantee that $R$ has negation.
-- In this case we'd have to assume $R = ℕ$ and lift to ℤ
partial def _root_.Mathlib.Tactic.Ring.ExProd.moveConst {u v : Level} {A : Q(Type u)} {R : Q(Type v)}
    {sA : Q(CommSemiring $A)} {sR : Q(CommSemiring $R)} (sRA : Q(Algebra $R $A))
    {r : Q($R)}
    {a : Q($A)}
    (vr : ExBase q($sR) r)
    (va : Ring.ExProd q($sA) a) :
    MetaM <| Σ r' : Q($R), Σ a' : Q($A), ExBase q($sR) r' × Ring.ExProd q($sA) a' × Q($r • $a = $r' • $a')
    := do
  let ⟨n, a, va, pa⟩ ← va.extractConst
  if n == 1 then
    return ⟨r, a, vr, va, q(sorry)⟩
  let ⟨_, vr', pr'⟩ := vr.toExSum
  let ⟨r, vr, pr⟩ ← evalMul_exProd sR (.const (e := q($n : $R)) n) vr'
  return ⟨r, a, .sum vr, va, q(sorry)⟩


partial def evalAddExProd {u v w : Level} {A : Q(Type u)} {R₁ : Q(Type v)} {R₂ : Q(Type w)}
    {sA : Q(CommSemiring $A)} {sR₁ : Q(CommSemiring $R₁)} (sRA₁ : Q(Algebra $R₁ $A))
    {sR₂ : Q(CommSemiring $R₂)} (sRA₂ : Q(Algebra $R₂ $A))
    {r₁ : Q($R₁)}  {r₂ : Q($R₂)}
    {a₁ a₂ : Q($A)}
    (va₁ : Ring.ExProd q($sA) a₁)
    (va₂ : Ring.ExProd q($sA) a₂) :
    ExBase q($sR₁) r₁ →
    ExBase q($sR₂) r₂ →
    MetaM (
      Σ u' : Level, Σ R : Q(Type u'), Σ sR : Q(CommSemiring $R), Σ sRA : Q(Algebra $R $A),
        Σ r : Q($R), Σ a : Q($A),
      (ExBase q($sR) r × Ring.ExProd q($sA) a × Q($r₁ • $a₁ + $r₂ • $a₂ = $r • $a)))
  | .one, .one => do
    let res ← (OptionT.run (Ring.evalAddOverlap sA va₁ va₂) : CoreM _)
    match ← (OptionT.run (Ring.evalAddOverlap sA va₁ va₂) : CoreM _) with
    | .none =>
      /- This should be inaccessible -/
      throwError "evalAddExProd not implemented"
    | .some (.zero pf_isNat_zero) =>
        --TODO: reorder code such that this term can be removed.
        return ⟨_, R₁, sR₁, sRA₁, _, _, .one, .const (e := q(0:$A)) 0, q(sorry)⟩
    | .some (.nonzero ⟨_, va, pa⟩) =>
        return ⟨_, R₁, sR₁, sRA₁, _, _, .one, va, q(sorry)⟩
  | vr₁, vr₂ => do
    dbg_trace s!"Executing evalAddExProd with ring $A$ = {A}, R₁ = {R₁}, R₂ = {R₂}"
    let ⟨r₁, a₁, vr₁, va₁, pra₁⟩ ← va₁.moveConst sRA₁ vr₁
    let ⟨r₂, a₂, vr₂, va₂, pra₂⟩ ← va₂.moveConst sRA₂ vr₂
    have : $a₁ =Q $a₂ := ⟨⟩
    if ← withReducible <| isDefEq R₁ R₂ then
      have : v =QL w := ⟨⟩
      have : $R₁ =Q $R₂ :=  ⟨⟩
      let ⟨r₁', vr₁'⟩ := vr₁.cast sR₂
      let ⟨r₁', vr₁', pr₁'⟩ := vr₁'.toExSum
      let ⟨r₂', vr₂', pr₂'⟩ := vr₂.toExSum
      -- have : $r₁' =Q $r₁ := ⟨⟩
      -- throwError s!"calling evalAdd recursively on {vr₁'}, {vr₂}"
      let ⟨r, vr, pr⟩ ← evalAdd sR₂ vr₁' vr₂'
      -- sorry
      pure ⟨w, R₂, sR₂, sRA₂, r, a₂, ⟨.sum vr, va₂, q(sorry)⟩⟩
    -- otherwise the "smaller" of the two rings must be commutative
    else try
      -- first try to exhibit `R₂` as an `R₁`-algebra
      let _i₃ ← synthInstanceQ q(Algebra $R₁ $R₂)
      IO.println s!"synthed algebra instance {R₁} {R₂}"
      let _i₄ ← synthInstanceQ q(IsScalarTower $R₁ $R₂ $A)
      IO.println s!"synthed IsScalarTower instance {R₁} {R₂} {A}"
      assumeInstancesCommute
      let ⟨_, vr₂, pr₂⟩ := vr₂.toExSum
      let ⟨r, vr, pr⟩ ← evalAdd sR₂ (.add _i₃ vr₁ (.const (e := q(1:$R₂)) 1) .zero) vr₂
      -- let ⟨r, vr, pr⟩ ← evalSMul iR₂ iR₁ _i₃ vr₁ vr₂
      pure ⟨w, R₂, sR₂, sRA₂, r, a₂, .sum vr, va₂, q(sorry)⟩
      -- pure ⟨u₂, R₂, iR₂, iRA₂, r, vr, q($pr ▸ (smul_assoc $r₁ $r₂ $a).symm)⟩
    catch _ => try
      -- then if that fails, try to exhibit `R₁` as an `R₂`-algebra
      let _i₃ ← synthInstanceQ q(Algebra $R₂ $R₁)
      IO.println s!"synthed algebra instance {R₂} {R₁}"
      let _i₄ ← synthInstanceQ q(IsScalarTower $R₂ $R₁ $A)
      assumeInstancesCommute
      let ⟨_, vr₁, pr₁⟩ := vr₁.toExSum
      let ⟨r, vr, pr⟩ ← evalAdd sR₁ (.add _i₃ vr₂ (.const (e := q(1:$R₁)) 1) .zero) vr₁
      -- let ⟨r, vr, pr⟩ ← evalSMul iR₂ iR₁ _i₃ vr₁ vr₂
      pure ⟨v, R₁, sR₁, sRA₁, r, a₁, .sum vr, va₁, q(sorry)⟩
      -- pure ⟨u₁, R₁, iR₁, iRA₁, r, vr,
      --   q($pr ▸ smul_algebra_smul_comm $r₂ $r₁ $a ▸ (smul_assoc $r₂ $r₁ $a).symm)⟩
    catch _ =>
      -- throw o
      throwError "algebra failed: {R₁} is not an {R₂}-algebra and {R₂} is not an {R₁}-algebra"


partial def evalAdd {u : Level} {A : Q(Type u)}
    (sA : Q(CommSemiring $A))
    {a₁ a₂ : Q($A)} :
    ExSum q($sA) a₁ →
    ExSum q($sA) a₂ → MetaM (Result (ExSum q($sA)) q($a₁ + $a₂))
  | va₁, .zero => do
    assumeInstancesCommute
    return ⟨_, va₁, q(sorry /-hmul_cast_zero_mul (R₁ := $A₁) $a₂-/)⟩
  | .zero, va₂ => do
    assumeInstancesCommute
    return ⟨_, va₂, q(sorry /-hmul_cast_zero_mul (R₁ := $A₁) $a₂-/)⟩
  | .add (R := R₁) (sR := sR₁) (r := r₁) (a := a₁) (b := t₁) sRA₁ vr₁ va₁ vt₁,
    .add (R := R₂) (sR := sR₂) (r := r₂) (a := a₂) (b := t₂) sRA₂ vr₂ va₂ vt₂ =>
  match va₁.cmp va₂ with
  | .lt => do
    IO.println s!"Comparison of {← ppExpr a₁} and {← ppExpr a₂} was lt. adding {va₁.atomsList} first"
    let ⟨_, vt, pt⟩ ← evalAdd sA vt₁ (.add sRA₂ vr₂ va₂ vt₂)
    return ⟨_, .add sRA₁ vr₁ va₁ vt, q(sorry)⟩
  | .gt => do
    IO.println s!"Comparison of {← ppExpr a₁} and {← ppExpr a₂} was gt. adding {va₂.atomsList} first"
    let ⟨_, vt, pt⟩ ← evalAdd sA vt₂ (.add sRA₁ vr₁ va₁ vt₁)
    return ⟨_, .add sRA₂ vr₂ va₂ vt, q(sorry)⟩
  | .eq => do
    IO.println s!"Comparison {← ppExpr a₁} and {← ppExpr a₂} was eq. exprod was {va₁.atomsList}."
    let ⟨_, vt, pt⟩ ← evalAdd sA vt₁ vt₂
    let ⟨u, R, sR, sRA, r, a, vr, va, par⟩ ← evalAddExProd sRA₁ sRA₂ va₁ va₂ vr₁ vr₂
    return ⟨_, .add sRA vr va vt, q(sorry)⟩
      -- throwError "evalAdd not implemented."



  -- | .one , .one => do
  --   -- TODO: insert the specific instance.
  --   return ⟨_, .add q(inferInstance : Algebra ℕ $A) .one (.const (e := q(2:$A)) 2) .zero, q(sorry)⟩
  --   -- assumeInstancesCommute
  --   -- IO.println "Adding one not implemented"
  --   -- throwError "Adding one not implemented"
  -- | .add sAlg vr va vt, .one => do
  --   let ⟨_, vt', pt'⟩ ← evalAdd sA vt .one
  --   return ⟨_, .add sAlg vr va vt', q(sorry)⟩
  -- | .one, .add sAlg vr va vt => do
  --   let ⟨_, vt', pt'⟩ ← evalAdd sA vt .one
  --   return ⟨_, .add sAlg vr va vt', q(sorry)⟩
  --   -- return ⟨_, ofProd sA va₂, q(sorry /-hmul_cast_one_mul (R₁ := ℕ) $a₂-/)⟩

  -- | .add (R := R₁) (sR := sR₁) (r := r₁) (a := a₁) (b := t₁) sRA₁ vr₁ va₁ vt₁,
  --   .add (R := R₂) (sR := sR₂) (r := r₂) (a := a₂) (b := t₂) sRA₂ vr₂ va₂ vt₂ => do
  --   -- IO.println s!"Adding {a₁} and {a₂}."
  --   match va₁.cmp va₂ with
  --   | .lt =>
  --     IO.println s!"Comparison was lt. adding {va₁.atomsList} first"
  --     let ⟨_, vt, pt⟩ ← evalAdd sA vt₁ (.add sRA₂ vr₂ va₂ vt₂)
  --     return ⟨_, .add sRA₁ vr₁ va₁ vt, q(sorry)⟩
  --   | .gt =>
  --     IO.println s!"Comparison was gt. adding {va₂.atomsList} first"
  --     let ⟨_, vt, pt⟩ ← evalAdd sA vt₂ (.add sRA₁ vr₁ va₁ vt₁)
  --     return ⟨_, .add sRA₂ vr₂ va₂ vt, q(sorry)⟩
  --   | .eq =>
  --     IO.println s!"Comparison was eq. exprod was {va₁.atomsList}."
  --     let ⟨_, vt, pt⟩ ← evalAdd sA vt₁ vt₂
  --     let ⟨u, R, sR, sRA, r, a, vr, va, par⟩ ← evalAddExProd sRA₁ sRA₂ va₁ va₂ vr₁ vr₂
  --     return ⟨_, .add sRA vr va vt, q(sorry)⟩
  --   -- sorry

partial def evalMul_exProd {u : Level} {A : Q(Type u)}
    (sA : Q(CommSemiring $A))
    {a₁ a₂ : Q($A)}
    (va₂ : Ring.ExProd q($sA) q($a₂)) :
    ExSum q($sA) a₁ → MetaM (Result (ExSum sA) q($a₁ * $a₂))
  | .zero => do
    IO.println s!"evalMul_exProd on {← ppExpr a₁} and {← ppExpr a₂}"
    assumeInstancesCommute
    return ⟨_, .zero, q(sorry /-hmul_cast_zero_mul (R₁ := $A₁) $a₂-/)⟩
  -- | .one => do
  --   assumeInstancesCommute
  --   return ⟨_, ofProd sA va₂, q(sorry /-hmul_cast_one_mul (R₁ := ℕ) $a₂-/)⟩
  | .add (A := A) (sA := sA) (R := R) (sR := sR) (sAlg := sRA) (r := r) (a := a) (b := t)
      vr va vt => do
    let ⟨a', va', pa'⟩ ←  Ring.evalMulProd sA va va₂
    let ⟨t', vt', pt'⟩ ← evalMul_exProd sA va₂ vt
    return ⟨_, .add sRA vr va' vt', q(sorry)⟩

partial def evalMul {u : Level} {A : Q(Type u)}
    (sA : Q(CommSemiring $A))
     {a₁ a₂ : Q($A)}
    (va₁ : ExSum q($sA) a₁) :
    ExSum q($sA) a₂ → MetaM (Result (ExSum q($sA)) q($a₁ * $a₂))
  | .zero => do
    return ⟨_, .zero, q(sorry)⟩
  -- | .one => do
  --   assumeInstancesCommute
  --   return ⟨_, va₁, q(mul_one $a₁)⟩
  | .add (A := A) (sA := sA) (R := R) (sR := sR) (sAlg := sRA) (r := r) (a := a) (b := t)
      vr va vt => do
    let ⟨a', va', pa'⟩ ← evalMul_exProd sA va va₁
    let ⟨ra', vra', pra'⟩ ← evalSMul sA sR sRA vr va'
    let ⟨t', vt', pt'⟩ ← evalMul sA va₁ vt
    let ⟨_, v, p⟩ ← evalAdd sA vra' vt'
    return ⟨_, v, q(sorry)⟩


-- partial def evalHMul_exProd {u : Level} {A₁ : Q(Type u)} {A₂ : Q(Type u)} (hdef : $A₁ =Q $A₂)
--     (sA₁ : Q(CommSemiring $A₁)) (sA₂ : Q(CommSemiring $A₂))
--     {sHMul : Q(HMul $A₁ $A₂ $A₁)} (sLaw : Q(LawfulHMul $A₁ $A₂)) {a₁ : Q($A₁)} {a₂ : Q($A₂)}
--     (va₁ : ExSum A₁ a₁) (va₂ : Ring.ExProd sA₂ a₂) :
--     MetaM <| Result (ExSum A₂) q($a₁ * $a₂) := do
--   match va₁ with
--   | .zero _ =>
--     assumeInstancesCommute
--     return ⟨_, .zero sA₂, q(sorry /-hmul_cast_zero_mul (R₁ := $A₁) $a₂-/)⟩
--   | .one sA =>
--     assumeInstancesCommute
--     return ⟨_, ofProd sA₂ va₂, q(sorry /-hmul_cast_one_mul (R₁ := ℕ) $a₂-/)⟩
--   | .add (A := A) (sA := sA) (R := R) (sR := sR) (sAlg := sRA) vr va vt =>
--     throwError "HMul for two ExProds not implemented."
--     -- return ⟨sorry, sorry, sorry⟩


-- partial def evalHMul {u : Level} {A₁ : Q(Type u)} {A₂ : Q(Type u)}
--     (sA₁ : Q(CommSemiring $A₁)) (sA₂ : Q(CommSemiring $A₂))
--     {sHMul : Q(HMul $A₁ $A₂ $A₁)} (sLaw : Q(LawfulHMul $A₁ $A₂)) {a₁ : Q($A₁)} {a₂ : Q($A₂)}
--     (va₁ : ExSum A₁ a₁) (va₂ : ExSum A₂ a₂) :
--     MetaM <| Result (ExSum A₁) q($a₁ * $a₂) := do
--   match va₂ with
--   | .zero sA =>
--     assumeInstancesCommute
--     return ⟨_, .zero sA₁, q(hmul_zero_natCast $a₁)⟩
--   | .one sA =>
--     assumeInstancesCommute
--     return ⟨_, va₁, q(LawfulHMul.mul_one $a₁)⟩
--   | .add (A := A) (sA := sA) (R := R) (sR := sR) (sAlg := sRA) (a := a) vr va vt =>
--     assumeInstancesCommute
--     let ⟨et, vt', pt⟩ ← evalHMul sA₁ sA sLaw va₁ vt
--     let ⟨_, _, _⟩ ← evalHMul_exProd sA₁ sA sLaw va₁ (a₂ := a) va
--     return ⟨sorry, sorry, sorry⟩



partial def matchRingsSMul {v : Level} {A : Q(Type v)}
  {iA : Q(Semiring $A)}
  {u₁ : Level} {R₁ : Q(Type u₁)} (iR₁ : Q(CommSemiring $R₁)) (iRA₁ : Q(@Algebra $R₁ $A $iR₁ $iA))
  {u₂ : Level} {R₂ : Q(Type u₂)} (iR₂ : Q(CommSemiring $R₂)) (iRA₂ : Q(@Algebra $R₂ $A $iR₂ $iA))
 {r₁ : Q($R₁)} {r₂ : Q($R₂)} (vr₁ : ExSum iR₁ r₁) (vr₂ : ExSum iR₂ r₂) (a : Q($A)) :
    MetaM <|
      Σ u : Level, Σ R : Q(Type u), Σ iR : Q(CommSemiring $R),
      Σ _ : Q(@Algebra $R $A $iR $iA),
      Σ r' : Q($R),
        (ExSum iR r' ×
        Q($r₁ • ($r₂ • $a) = $r' • $a)) := do
  -- is isDefEqQ anything? Probably not, you need to know that both terms have the same type.
  if ← withReducible <| isDefEq R₁ R₂ then
    have : u₁ =QL u₂ := ⟨⟩
    have : $R₁ =Q $R₂ :=  ⟨⟩
    /- Question: what do I do here? I just want to view $r₁$ as having type $R₂$-/
    -- IO.println s!"smul with defeq rings {R₁} and {R₂} not yet implemented."
    -- throwError s!"smul with defeq rings {R₁} and {R₂} not yet implemented."
    /- Is this safe and correct? -/
    -- have : Q($r₁' • $r₂ • $a = $r₁ • $r₂ • $a) := ← Lean.Meta.mkEqRefl q($r₁ • $r₂ • $a)
    let ⟨r₁', vr₁'⟩ := vr₁.cast iR₂
    -- let ⟨r₁', vr₁', pr₁'⟩ := vr₁'.toExSum
    -- let ⟨r₂', vr₂', pr₂'⟩ := vr₂.toExSum
    have : $r₁' =Q $r₁ := ⟨⟩
    let ⟨r, vr, pr⟩ ← evalMul iR₂ vr₁' vr₂
    pure ⟨_, R₂, iR₂, iRA₂, r, vr, q(sorry /- $this  @smul_smul $R₂ $A _ _ $r₁' $r₂ $a -/ )⟩

  -- otherwise the "smaller" of the two rings must be commutative
  else try
    -- first try to exhibit `R₂` as an `R₁`-algebra
    let _i₁ ← synthInstanceQ q(CommSemiring $R₁)
    let _i₃ ← synthInstanceQ q(Algebra $R₁ $R₂)
    IO.println s!"synthed algebra instance {R₁} {R₂}"
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₁ $R₂ $A)
    IO.println s!"synthed IsScalarTower instance {R₁} {R₂} {A}"
    assumeInstancesCommute
    -- let ⟨r₂', vr₂', pr₂'⟩ := vr₂.toExSum
    let ⟨r, vr, pr⟩ ← evalSMul iR₂ iR₁ _i₃ (.sum vr₁) vr₂
    pure ⟨u₂, R₂, iR₂, iRA₂, r, vr, q(sorry)⟩
  catch e => try
    throw e
    -- then if that fails, try to exhibit `R₁` as an `R₂`-algebra
    let _i₁ ← synthInstanceQ q(CommSemiring $R₂)
    let _i₃ ← synthInstanceQ q(Algebra $R₂ $R₁)
    IO.println s!"synthed algebra instance {R₂} {R₁}"
    let _i₄ ← synthInstanceQ q(IsScalarTower $R₂ $R₁ $A)
    assumeInstancesCommute
    -- let ⟨r₁', vr₁', pr₁'⟩ := vr₁.toExSum
    let ⟨r, vr, pr⟩ ← evalSMul iR₁ iR₂ _i₃ (.sum vr₂) vr₁
    pure ⟨u₁, R₁, iR₁, iRA₁, r, vr, q(sorry)⟩
  catch o =>
    throw o
    throwError s!"algebra failed: {← ppExpr R₁} is not an {← ppExpr R₂}-algebra and {← ppExpr R₂} is not an {← ppExpr R₁}-algebra"

partial def evalSMul {u v : Level} {R : Q(Type u)} {A : Q(Type v)} (sA : Q(CommSemiring $A))
  (sR : Q(CommSemiring $R)) (sRA : Q(Algebra $R $A)) {r : Q($R)} {a : Q($A)} :
   ExBase sR r → ExSum sA a →
    MetaM (Result (ExSum sA) q($r • $a))
  | vr,  .zero => do
    -- TODO: is this the right way to do this?
    assumeInstancesCommute
    return ⟨_, .zero, q(smul_zero_rawCast (r := $r) (A := $A))⟩
  -- | .one => do
  --   assumeInstancesCommute
  --   return ⟨_, .add sRA vr (.const (e := q(1 : $A)) 1 .none) .zero, q((add_rawCast_zero).symm)⟩
    /- Note: removing the (a := a) produces an inscrutable error during a pattern match-/
  | .one, va => do
    return ⟨_, va, q(by simp)⟩
  | .sum vr, .add (R := S) (sR := sS) sSA (r := s) (a := a) vs va vt => do
    assumeInstancesCommute
    let ⟨et, vt, pt⟩ ← evalSMul sA sR sRA (.sum vr) vt
    let ⟨_, vs', ps'⟩ := vs.toExSum
    let ⟨u₁, R₁, iR₁, sR₁A, r₁, vr₁, pr₁⟩ ← matchRingsSMul sS sSA sR sRA vs' vr a
    -- sorry
    return ⟨_, .add sR₁A (.sum vr₁) va vt, q(sorry)⟩

end
--     -- throwError "smul add not implemented."
-- end
-- /-
-- * `e = 0` if `norm_num` returns `IsNat e 0`
-- * `e = Nat.rawCast n + 0` if `norm_num` returns `IsNat e n`
-- * `e = Int.rawCast n + 0` if `norm_num` returns `IsInt e n`
-- * `e = Rat.rawCast n d + 0` if `norm_num` returns `IsRat e n d`
-- -/
-- def evalCast {u : Level} {A : Q(Type u)} (sA : Q(CommSemiring $A)) {e : Q($A)} :
--     NormNum.Result e → Option (Result (ExSum sA) e)
--   | .isNat _ (.lit (.natVal 0)) p => do
--     assumeInstancesCommute
--     pure ⟨_, .zero, q(sorry)⟩
--   | .isNat _ lit p => do
--     assumeInstancesCommute
--     pure ⟨_, (Ring.ExProd.mkNat sA lit.natLit!).2.toSum, (q(cast_pos $p) :)⟩
--   | .isNegNat rα lit p =>
--     pure ⟨_, (Ring.ExProd.mkNegNat _ rα lit.natLit!).2.toSum, (q(cast_neg $p) : Expr)⟩
--   | .isRat dα q n d p =>
--     pure ⟨_, (ExProd.mkRat sα dα q n d q(IsRat.den_nz $p)).2.toSum, (q(cast_rat $p) : Expr)⟩
--   | _ => none

partial def eval {u : Lean.Level} {A : Q(Type u)} (sA : Q(CommSemiring $A))
    (e : Q($A)) : AtomM (Result (ExSum sA) e) := Lean.withIncRecDepth do
  let els := do
    evalAtom sA e
  let .const n _ := (← withReducible <| whnf e).getAppFn | els
  match n with
  | ``HSMul.hSMul | ``SMul.smul => match e with
    | ~q(@SMul.smul $R _ $inst $r $a) =>
      have sR : Q(CommSemiring $R) := ← synthInstanceQ q(CommSemiring $R)
      have sAlg : Q(Algebra $R $A) := ← synthInstanceQ q(Algebra $R $A)
      assumeInstancesCommute
      let ⟨_, vr, pr⟩ ← eval sR r
      let ⟨_, va, pa⟩ ← eval sA a
      let ⟨ef, vf, pf⟩ ← evalSMul sA sR sAlg (.sum vr) va
      return ⟨ef, vf, q(smul_congr $pr $pa $pf)⟩
    | ~q(@HSMul.hSMul $R _ _ $inst $r $a) =>
      throwError "hsmul not implemented"
    | _ => els
  | ``HAdd.hAdd | ``Add.add => match e with
    | ~q($a + $b) =>
      let ⟨_, va, pa⟩ ← eval sA a
      let ⟨_, vb, pb⟩ ← eval sA b
      let ⟨_, vab, pab⟩ ← evalAdd sA va vb
      return ⟨_, vab, q(sorry)⟩
      -- let ⟨c, vc, p⟩ ← evalAdd sα va vb
      -- pure ⟨c, vc, (q(add_congr $pa $pb $p) : Expr)⟩
    | _ => els
  | ``HMul.hMul | ``Mul.mul => match e with
    | ~q($a * $b) =>
      let ⟨_, va, pa⟩ ← eval sA a
      let ⟨_, vb, pb⟩ ← eval sA b
      let ⟨_, vab, pab⟩ ← evalMul sA va vb
      return ⟨_, vab, q(sorry)⟩
    | _ =>
      els
  | _ =>
    els

open Lean Parser.Tactic Elab Command Elab.Tactic Meta Qq

theorem eq_congr {R : Type*} {a b a' b' : R} (ha : a = a') (hb : b = b') (h : a' = b') : a = b := by
  subst ha hb
  exact h

def normalize (goal : MVarId) : AtomM MVarId := do
  -- let goal ← try getMainGoal catch
  --   | _ => return
  let some (A, e₁, e₂) :=
    (← whnfR <|← instantiateMVars <|← goal.getType).eq?
    | throwError "algebra failed: not an equality"
  let .sort u ← whnf (← inferType A) | unreachable!
  let v ← try u.dec catch _ => throwError "not a type{indentExpr A}"
  have A : Q(Type v) := A
  have sA : Q(CommSemiring $A) := ← synthInstanceQ q(CommSemiring $A)
  have e₁ : Q($A) := e₁
  have e₂ : Q($A) := e₂
  let (⟨a, exa, pa⟩ : Result (ExSum sA) e₁) ← eval sA e₁
  let (⟨b, exb, pb⟩ : Result (ExSum sA) e₂) ← eval sA e₂
  let g' ← mkFreshExprMVarQ q($a = $b)
  goal.assign q(eq_congr $pa $pb $g' : $e₁ = $e₂)
  -- if ← isDefEq a b then
    -- have : $a =Q $b := ⟨⟩
    -- g'.mvarId!.assign (q(rfl : $a = $b) : Expr)
    return g'.mvarId!
  -- else throwError "algebra failed to normalize expression."
  -- let l ← ExSum.eq_exSum g'.mvarId! a b exa exb
  -- Tactic.pushGoals l
  /- TODO: we probably want to do some sort of normalization of intermediate expressions.
    `norm_num` does not seem set up to do this very well. Much of the work is actually done by
    `simp`, namely `a+0 -> a` and `a*1 -> a`. -/
  -- for g in l do
  --   let l ← evalTacticAt (← `(tactic| norm_num)) g
  --   Tactic.pushGoals l
    -- NormNum.normNumAt g (← getSimpContext)

elab (name := algebra) "algebra" : tactic =>
  withMainContext do
    let g ← getMainGoal
    let g ← AtomM.run .default (normalize g)
    Tactic.pushGoal g


example {S R A : Type*} [CommSemiring S] [CommSemiring R] [CommSemiring A] [Algebra S R]
    [Algebra R A] [Algebra S A] [IsScalarTower S R A] {r : R} {s : S} {a₁ a₂ : A} :
    (s • a₁) * (r • a₂) = (s • r) • (a₁ * a₂) := by
  simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_assoc]
  rw [smul_comm]


end Mathlib.Tactic.Algebra


example (x : ℚ) :  x = (1 : ℤ) • x := by
  simp_rw [← SMul.smul_eq_hSMul]
  algebra
  match_scalars <;> simp

example (x : ℚ) : x = 1 := by
  algebra
  sorry

-- BUG: ExProd.one doesn't match with the empty product in sums.
example (x : ℚ) : x + x + x  = 3 * x := by
  algebra
  sorry

-- BUG: infinite loop
example (x : ℚ) : (x + x) + (x + x)  = 4 * x := by
  algebra
  -- simp
  simp only [Nat.rawCast, Nat.cast_one, pow_one, Nat.cast_ofNat, one_smul, Nat.cast_zero, add_zero,
    mul_one]

-- BUG: the x*y terms are not being combined.
example (x y : ℚ) : (x + y)*(x+y) = 1 := by
  -- simp_rw [← SMul.smul_eq_hSMul]
  algebra
  simp only [show Nat.rawCast 1 = 1 by rfl]
  simp only [pow_one, Nat.rawCast, Nat.cast_one, mul_one, one_smul, Nat.cast_ofNat, Nat.cast_zero,
    add_zero]

--   sorry

--   -- match_scalars <;> simp

example (x y : ℚ) : (x+y)*x = 1 := by
  -- simp_rw [← SMul.smul_eq_hSMul]
  algebra
  simp only [show Nat.rawCast 1 = 1 by rfl]
  simp only [pow_one, Nat.rawCast, Nat.cast_one, mul_one, one_smul, Nat.cast_ofNat, Nat.cast_zero,
    add_zero]
  sorry

example (x y : ℚ) : (x+y)*y  = 1 := by
  -- simp_rw [← SMul.smul_eq_hSMul]
  algebra
  simp only [show Nat.rawCast 1 = 1 by rfl]
  simp only [pow_one, Nat.rawCast, Nat.cast_one, mul_one, one_smul, Nat.cast_ofNat, Nat.cast_zero,
    add_zero]
  sorry
