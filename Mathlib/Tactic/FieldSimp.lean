/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, David Renshaw, Heather Macbeth, Arend Mellendijk, Michael Rothgang
-/
import Mathlib.Tactic.FieldSimp.Discharger
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.FieldSimp'
import Mathlib.Util.AtLoc
import Mathlib.Util.AtomM.Recurse
import Mathlib.Util.Simp
import Mathlib.Util.SynthesizeUsing


/-! # A tactic for clearing denominators in fields

-/

open Lean Meta Elab Qq Mathlib.Tactic List

namespace Mathlib.Tactic.FieldSimp

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
def toNF (l : qNF q($M)) : Q(NF $M) :=
  let l' : List Q(ℤ × $M) := (l.map Prod.fst).map (fun (a, x) ↦ q(($a, $x)))
  let qt : List Q(ℤ × $M) → Q(List (ℤ × $M)) := List.rec q([]) (fun e _ l ↦ q($e ::ᵣ $l))
  qt l'

/-- Given `l` of type `qNF M`, i.e. a list of `(ℤ × Q($M)) × ℕ`s (two `Expr`s and a natural
number), apply an expression representing a function with domain `ℤ` to each of the `ℤ`
components. -/
def onExponent (l : qNF M) (f : ℤ → ℤ) : qNF M :=
  l.map fun ((a, x), k) ↦ ((f a, x), k)

/-- Build a transparent expression for the product of powers represented by `l : qNF M`. -/
def evalPrettyMonomial (iM : Q(GroupWithZero $M)) (r : ℤ) (x : Q($M)) :
    MetaM (Σ e : Q($M), Q(zpow' $x $r = $e)) := do
  match r with
  | 0 => /- If an exponent is zero then we must not have been able to prove that x is nonzero.  -/
    return ⟨q($x / $x), q(zpow'_zero_eq_div ..)⟩
  | 1 => return ⟨x, q(zpow'_one $x)⟩
  | .ofNat r => do
    let pf ← mkDecideProofQ q($r ≠ 0)
    return ⟨q($x ^ $r), q(zpow'_ofNat $x $pf)⟩
  | r => do
    let pf ← mkDecideProofQ q($r ≠ 0)
    return ⟨q($x ^ $r), q(zpow'_of_ne_zero_right _ _ $pf)⟩

def tryClearZero
    (disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type)) (iM : Q(GroupWithZero $M))
    (r : ℤ) (x : Q($M)) (i : ℕ) (l : qNF M) :
    MetaM <| Σ l' : qNF M, Q(NF.eval $(qNF.toNF (((r, x), i) :: l)) = NF.eval $(l'.toNF)) := do
  if r != 0 then
    return ⟨((r, x), i) :: l, q(rfl)⟩
  try
    let pf' : Q($x ≠ 0) ← disch q($x ≠ 0)
    have pf_r : Q($r = 0) := ← mkDecideProofQ q($r = 0)
    return ⟨l, (q(NF.eval_cons_of_pow_eq_zero $pf_r $pf' $(l.toNF)):)⟩
  catch _=>
    return ⟨((r, x), i) :: l, q(rfl)⟩

def removeZeros
    (disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type)) (iM : Q(GroupWithZero $M))
    (l : qNF M) :
    MetaM <| Σ l' : qNF M, Q(NF.eval $(l.toNF) = NF.eval $(l'.toNF)) :=
  match l with
  | [] => return ⟨[], q(rfl)⟩
  | ((r, x), i) :: t => do
    let ⟨t', pf⟩ ← removeZeros disch iM t
    let ⟨l', pf'⟩ ← tryClearZero disch iM r x i t'
    let pf' : Q(NF.eval (($r, $x) ::ᵣ $(qNF.toNF t')) = NF.eval $(qNF.toNF l')) := pf'
    let pf'' : Q(NF.eval (($r, $x) ::ᵣ $(qNF.toNF t)) = NF.eval $(qNF.toNF l')) :=
      q(NF.eval_cons_eq_eval_of_eq_of_eq $r $x $pf $pf')
    return ⟨l', pf''⟩

/-- Given a product of powers, split as a quotient: the positive powers divided by (the negations
of) the negative powers. -/
def split (iM : Q(CommGroupWithZero $M)) (l : qNF M) :
    MetaM (Σ l_n l_d : qNF M, Q(NF.eval $(l.toNF)
      = NF.eval $(l_n.toNF) / NF.eval $(l_d.toNF))) := do
  match l with
  | [] => return ⟨[], [], q(Eq.symm (div_one (1:$M)))⟩
  | ((r, x), i) :: t =>
    let ⟨t_n, t_d, pf⟩ ← split iM t
    if r > 0 then
      return ⟨((r, x), i) :: t_n, t_d, (q(NF.cons_eq_div_of_eq_div $r $x $pf):)⟩
    else if r = 0 then
      return ⟨((1, x), i) :: t_n, ((1, x), i) :: t_d, (q(NF.cons_zero_eq_div_of_eq_div $x $pf):)⟩
    else
      let r' : ℤ := -r
      return ⟨t_n, ((r', x), i) :: t_d, (q(NF.cons_eq_div_of_eq_div' $r' $x $pf):)⟩

private def evalPrettyAux (iM : Q(GroupWithZero $M)) (l : qNF M) :
    MetaM (Σ e : Q($M), Q(NF.eval $(l.toNF) = $e)) := do
  match l with
  | [] => return ⟨q(1), q(rfl)⟩
  | [((r, x), _)] =>
    let ⟨e, pf⟩ ← evalPrettyMonomial iM r x
    return ⟨e, q(Eq.trans (one_mul _) $pf)⟩
  | ((r, x), _) :: t =>
    let ⟨e, pf_e⟩ ← evalPrettyMonomial iM r x
    let ⟨t', pf⟩ ← evalPrettyAux iM t
    return ⟨q($t' * $e), (q(congr_arg₂ HMul.hMul $pf $pf_e):)⟩

/-- Build a transparent expression for the product of powers represented by `l : qNF M`. -/
def evalPretty (iM : Q(CommGroupWithZero $M)) (l : qNF M) :
    MetaM (Σ e : Q($M), Q(NF.eval $(l.toNF) = $e)) := do
  let ⟨l_n, l_d, pf⟩ ← split iM l
  let ⟨num, pf_n⟩ ← evalPrettyAux q(inferInstance) l_n
  let ⟨den, pf_d⟩ ← evalPrettyAux q(inferInstance) l_d
  match l_n, l_d with
  | _, [] => return ⟨num, q(eq_div_of_eq_one_of_subst $pf $pf_n)⟩
  | [], _ =>
    -- we choose this normal form rather than `1 / den` because `one_div` is a Mathlib simp-lemma
    return ⟨q($den⁻¹), q(eq_div_of_eq_one_of_subst' $pf $pf_d)⟩
  | _, _ =>
    let pf_n : Q(NF.eval $(l_n.toNF) = $num) := pf_n
    let pf_d : Q(NF.eval $(l_d.toNF) = $den) := pf_d
    let pf : Q(NF.eval $(l.toNF) = NF.eval $(l_n.toNF) / NF.eval $(l_d.toNF)) := pf
    let pf_tot := q(eq_div_of_subst $pf $pf_n $pf_d)
    return ⟨q($num / $den), pf_tot⟩

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
def mul : qNF q($M) → qNF q($M) → qNF q($M)
  | [], l => l
  | l, [] => l
  | ((a₁, x₁), k₁) :: t₁, ((a₂, x₂), k₂) :: t₂ =>
    if k₁ > k₂ then
      ((a₁, x₁), k₁) :: mul t₁ (((a₂, x₂), k₂) :: t₂)
    else if k₁ = k₂ then
      /- If we can prove that the atom is nonzero then we could remove it from this list,
      but this will be done at a later stage. -/
      ((a₁ + a₂, x₁), k₁) :: mul t₁ t₂
    else
      ((a₂, x₂), k₂) :: mul (((a₁, x₁), k₁) :: t₁) t₂

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), recursively construct a proof that in the field `$M`, the product of
the "multiplicative linear combinations" represented by `l₁` and `l₂` is the multiplicative linear
combination represented by `FieldSimp.qNF.mul l₁ l₁`. -/
def mkMulProof (iM : Q(CommGroupWithZero $M)) (l₁ l₂ : qNF M) :
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
      (q(NF.mul_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
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
      ((a₁ - a₂, x₁), k₁) :: div t₁ t₂
    else
      ((-a₂, x₂), k₂) :: div (((a₁, x₁), k₁) :: t₁) t₂

/-- Given two terms `l₁`, `l₂` of type `qNF M`, i.e. lists of `(ℤ × Q($M)) × ℕ`s (an integer, an
`Expr` and a natural number), recursively construct a proof that in the field `$M`, the quotient
of the "multiplicative linear combinations" represented by `l₁` and `l₂` is the multiplicative
linear combination represented by `FieldSimp.qNF.div l₁ l₁`. -/
def mkDivProof (iM : Q(CommGroupWithZero $M)) (l₁ l₂ : qNF M) :
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
      (q(NF.div_eq_eval₂ $a₁ $a₂ $x₁ $pf):)
    else
      let pf := mkDivProof iM (((a₁, x₁), k₁) :: t₁) t₂
      (q(NF.div_eq_eval₃ ($a₂, $x₂) $pf):)

/-- Extract a common factor `L` of two products-of-powers `l₁` and `l₂` in `M`, in the sense that
both `l₁` and `l₂` are quotients by `L` of products of *positive* powers.

The boolean flag `nonzero` specifies whether we extract a *certified nonzero* (and therefore
potentially smaller) common factor. The metaprogram returns a "proof" that this common factor is
nonzero, i.e. an expression `Q(NF.eval $(L.toNF) ≠ 0)`, but this will be junk if the boolean flag
`nonzero` is set to `false`. -/
partial def gcd (iM : Q(CommGroupWithZero $M)) (l₁ l₂ : qNF M)
    (disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type)) (nonzero : Bool) :
  MetaM <| Σ (L l₁' l₂' : qNF M),
    Q((NF.eval $(L.toNF)) * NF.eval $(l₁'.toNF) = NF.eval $(l₁.toNF)) ×
    Q((NF.eval $(L.toNF)) * NF.eval $(l₂'.toNF) = NF.eval $(l₂.toNF)) ×
    Q(NF.eval $(L.toNF) ≠ 0) :=

  /- Handle the case where atom `i` is present in the first list but not the second. -/
  let absent (l₁ l₂ : qNF M) (n : ℤ) (e : Q($M)) (i : ℕ) :
      MetaM <| Σ (L l₁' l₂' : qNF M),
        Q((NF.eval $(L.toNF)) * NF.eval $(l₁'.toNF) = NF.eval $(qNF.toNF (((n, e), i) :: l₁))) ×
        Q((NF.eval $(L.toNF)) * NF.eval $(l₂'.toNF) = NF.eval $(l₂.toNF)) ×
        Q(NF.eval $(L.toNF) ≠ 0) := do
    let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← gcd iM l₁ l₂ disch nonzero
    if 0 < n then
      -- Don't pull anything out
      return ⟨L, ((n, e), i) :: l₁', l₂', (q(NF.eval_mul_eval_cons $n $e $pf₁):), q($pf₂), pf₀⟩
    else if n = 0 then
      -- Don't pull anything out, but eliminate the term if it is a cancellable zero
      let ⟨l₁'', pf''⟩ ← tryClearZero disch q(inferInstance) 0 e i l₁'
      let pf'' : Q(NF.eval ((0, $e) ::ᵣ $(l₁'.toNF)) = NF.eval $(l₁''.toNF)) := pf''
      return ⟨L, l₁'', l₂', (q(NF.eval_mul_eval_cons_zero $pf₁ $pf''):), q($pf₂), pf₀⟩
    try
      let pf : Q($e ≠ 0) ← disch q($e ≠ 0)
      -- if nonzeroness proof succeeds
      return ⟨((n, e), i) :: L, l₁', ((-n, e), i) :: l₂', (q(NF.eval_cons_mul_eval $n $e $pf₁):),
        (q(NF.eval_cons_mul_eval_cons_neg $n $pf $pf₂):),
        (q(NF.cons_ne_zero $n $pf $pf₀):)⟩
    catch _ =>
      -- if we can't prove nonzeroness, don't pull out e.
      return ⟨L, ((n, e), i) :: l₁', l₂', (q(NF.eval_mul_eval_cons $n $e $pf₁):), q($pf₂), pf₀⟩

  /- Handle the case where atom `i` is present in both lists. -/
  let bothPresent (t₁ t₂ : qNF M) (n₁ n₂ : ℤ) (e : Q($M)) (he : Q($e ≠ 0)) (i : ℕ) :
      MetaM <| Σ (L l₁' l₂' : qNF M),
        Q((NF.eval $(L.toNF)) * NF.eval $(l₁'.toNF) = NF.eval $(qNF.toNF (((n₁, e), i) :: t₁))) ×
        Q((NF.eval $(L.toNF)) * NF.eval $(l₂'.toNF) = NF.eval $(qNF.toNF (((n₂, e), i) :: t₂))) ×
        Q(NF.eval $(L.toNF) ≠ 0) := do
    let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← gcd iM t₁ t₂ disch nonzero
    if n₁ < n₂ then
      let N : ℤ := n₂ - n₁
      return ⟨((n₁, e), i) :: L, l₁', ((n₂ - n₁, e), i) :: l₂',
        (q(NF.eval_cons_mul_eval $n₁ $e $pf₁):), (q(NF.mul_eq_eval₂ $n₁ $N $e $pf₂):),
          (q(NF.cons_ne_zero $n₁ $he $pf₀):)⟩
    else if n₁ = n₂ then
      return ⟨((n₁, e), i) :: L, l₁', l₂', (q(NF.eval_cons_mul_eval $n₁ $e $pf₁):),
        (q(NF.eval_cons_mul_eval $n₂ $e $pf₂):), (q(NF.cons_ne_zero $n₁ $he $pf₀):)⟩
    else
      let N : ℤ := n₁ - n₂
      return ⟨((n₂, e), i) :: L, ((n₁ - n₂, e), i) :: l₁', l₂',
        (q(NF.mul_eq_eval₂ $n₂ $N $e $pf₁):), (q(NF.eval_cons_mul_eval $n₂ $e $pf₂):),
          (q(NF.cons_ne_zero $n₂ $he $pf₀):)⟩

  match l₁, l₂ with
  | [], [] => pure ⟨[], [], [],
    (q(one_mul (NF.eval $(qNF.toNF (M := M) []))):),
    (q(one_mul (NF.eval $(qNF.toNF (M := M) []))):), q(one_ne_zero)⟩
  | ((n, e), i) :: t, [] => do
    let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← absent t [] n e i
    return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩
  | [], ((n, e), i) :: t => do
    let ⟨L, l₂', l₁', pf₂, pf₁, pf₀⟩ ← absent t [] n e i
    return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩
  | ((n₁, e₁), i₁) :: t₁, ((n₂, e₂), i₂) :: t₂ => do
    if i₁ > i₂ then
      let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← absent t₁ (((n₂, e₂), i₂) :: t₂) n₁ e₁ i₁
      return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩
    else if i₁ == i₂ then
      if nonzero then
        try
          let pf_e ← disch q($e₁ ≠ 0)
          -- if we can prove nonzeroness
          bothPresent t₁ t₂ n₁ n₂ e₁ pf_e i₁
        catch _ =>
          -- if we can't prove nonzeroness, don't pull out e.
          let ⟨L, l₁', l₂', pf₁, pf₂, pf₀⟩ ← gcd iM t₁ t₂ disch nonzero
          return ⟨L, ((n₁, e₁), i₁) :: l₁', ((n₂, e₂), i₂) :: l₂',
            (q(NF.eval_mul_eval_cons $n₁ $e₁ $pf₁):), (q(NF.eval_mul_eval_cons $n₂ $e₂ $pf₂):), pf₀⟩
      else
        -- this is a "junk" sorry: the proof doesn't get used when flag `nonzero` is set to false
        bothPresent t₁ t₂ n₁ n₂ e₁ q(sorry) i₁
    else
      let ⟨L, l₂', l₁', pf₂, pf₁, pf₀⟩ ← absent t₂ (((n₁, e₁), i₁) :: t₁) n₂ e₂ i₂
      return ⟨L, l₁', l₂', q($pf₁), q($pf₂), pf₀⟩

end qNF

/-! ### Core of the `field_simp` tactic -/

variable {M : Q(Type v)}

/-- The main algorithm behind the `field_simp` tactic: partially-normalizing an
expression in a field `M` into the form x1 ^ c1 * x2 ^ c2 * ... x_k ^ c_k,
where x1, x2, ... are distinct atoms in `M`, and c1, c2, ... are integers. -/
partial def normalize (disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type))
    (iM : Q(CommGroupWithZero $M)) (x : Q($M)) :
    AtomM (Σ y : Q($M), (Σ g : Sign M, Q($x = $(g.expr y))) ×
      Σ l : qNF M, Q($y = NF.eval $(l.toNF))) := do
  let baseCase (y : Q($M)) (normalize? : Bool) :
      AtomM (Σ (l : qNF M), Q($y = NF.eval $(l.toNF))) := do
    if normalize? then
      let r ← (← read).evalAtom y
      have y' : Q($M) := r.expr
      have pf : Q($y = $y') := ← r.getProof
      let (k, ⟨x', _⟩) ← AtomM.addAtomQ y'
      pure ⟨[((1, x'), k)], q(Eq.trans $pf (NF.atom_eq_eval $x'))⟩
    else
      let (k, ⟨x', _⟩) ← AtomM.addAtomQ y
      pure ⟨[((1, x'), k)], q(NF.atom_eq_eval $x')⟩
  match x with
  /- normalize a multiplication: `x₁ * x₂` -/
  | ~q($x₁ * $x₂) =>
    let ⟨y₁, ⟨g₁, pf₁_sgn⟩, l₁, pf₁⟩ ← normalize disch iM x₁
    let ⟨y₂, ⟨g₂, pf₂_sgn⟩, l₂, pf₂⟩ ← normalize disch iM x₂
    -- build the new list and proof
    have pf := qNF.mkMulProof iM l₁ l₂
    let ⟨G, pf_y⟩ := ← Sign.mul iM y₁ y₂ g₁ g₂
    pure ⟨q($y₁ * $y₂), ⟨G, q(Eq.trans (congr_arg₂ HMul.hMul $pf₁_sgn $pf₂_sgn) $pf_y)⟩,
      qNF.mul l₁ l₂, q(NF.mul_eq_eval $pf₁ $pf₂ $pf)⟩
  /- normalize a division: `x₁ / x₂` -/
  | ~q($x₁ / $x₂) =>
    let ⟨y₁, ⟨g₁, pf₁_sgn⟩, l₁, pf₁⟩ ← normalize disch iM x₁
    let ⟨y₂, ⟨g₂, pf₂_sgn⟩, l₂, pf₂⟩ ← normalize disch iM x₂
    -- build the new list and proof
    let pf := qNF.mkDivProof iM l₁ l₂
    let ⟨G, pf_y⟩ := ← Sign.div iM y₁ y₂ g₁ g₂
    pure ⟨q($y₁ / $y₂), ⟨G, q(Eq.trans (congr_arg₂ HDiv.hDiv $pf₁_sgn $pf₂_sgn) $pf_y)⟩,
      qNF.div l₁ l₂, q(NF.div_eq_eval $pf₁ $pf₂ $pf)⟩
  /- normalize a inversion: `y⁻¹` -/
  | ~q($y⁻¹) =>
    let ⟨y', ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM y
    let pf_y ← Sign.inv iM y' g
    -- build the new list and proof, casing according to the sign of `x`
    pure ⟨q($y'⁻¹), ⟨g, q(Eq.trans (congr_arg Inv.inv $pf_sgn) $pf_y)⟩,
      l.onExponent Neg.neg, (q(NF.inv_eq_eval $pf):)⟩
  /- normalize an integer exponentiation: `y ^ (s : ℤ)` -/
  | ~q($y ^ ($s : ℤ)) =>
    let some s := Expr.int? s | pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
    if s = 0 then
      pure ⟨q(1), ⟨Sign.plus, (q(zpow_zero $y):)⟩, [], q(NF.one_eq_eval $M)⟩
    else
      let ⟨y', ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM y
      let pf_s ← mkDecideProofQ q($s ≠ 0)
      let ⟨G, pf_y⟩ ← Sign.zpow iM y' g s
      let pf_y' := q(Eq.trans (congr_arg (· ^ $s) $pf_sgn) $pf_y)
      pure ⟨q($y' ^ $s), ⟨G, pf_y'⟩, l.onExponent (HMul.hMul s), (q(NF.zpow_eq_eval $pf_s $pf):)⟩
  /- normalize a natural number exponentiation: `y ^ (s : ℕ)` -/
  | ~q($y ^ ($s : ℕ)) =>
    let some s := Expr.nat? s | pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
    if s = 0 then
      pure ⟨q(1), ⟨Sign.plus, (q(pow_zero $y):)⟩, [], q(NF.one_eq_eval $M)⟩
    else
      let ⟨y', ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM y
      let pf_s ← mkDecideProofQ q($s ≠ 0)
      let ⟨G, pf_y⟩ ← Sign.pow iM y' g s
      let pf_y' := q(Eq.trans (congr_arg (· ^ $s) $pf_sgn) $pf_y)
      pure ⟨q($y' ^ $s), ⟨G, pf_y'⟩, l.onExponent (HMul.hMul s), (q(NF.pow_eq_eval $pf_s $pf):)⟩
  /- normalize a `(1:M)` -/
  | ~q(1) => pure ⟨q(1), ⟨Sign.plus,  q(rfl)⟩, [], q(NF.one_eq_eval $M)⟩
  /- normalize an addition: `a + b` -/
  | ~q(HAdd.hAdd (self := @instHAdd _ $i) $a $b) =>
    let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf₁⟩ ← normalize disch iM a
    let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf₂⟩ ← normalize disch iM b
    let ⟨L, l₁', l₂', pf₁', pf₂', _⟩ ← l₁.gcd iM l₂ disch false
    let ⟨e₁, pf₁''⟩ ← qNF.evalPretty iM l₁'
    let ⟨e₂, pf₂''⟩ ← qNF.evalPretty iM l₂'
    have pf_a := ← mkEqMul iM pf_sgn₁ q(Eq.trans $pf₁ (Eq.symm $pf₁')) pf₁''
    have pf_b := ← mkEqMul iM pf_sgn₂ q(Eq.trans $pf₂ (Eq.symm $pf₂')) pf₂''
    let e : Q($M) := q($(g₁.expr e₁) + $(g₂.expr e₂))
    let ⟨sum, pf_atom⟩ ← baseCase e false
    let _i ← synthInstanceQ q(Semifield $M)
    assumeInstancesCommute
    let L' := qNF.mul L sum
    let pf_mul : Q((NF.eval $(L.toNF)) * NF.eval $(sum.toNF) = NF.eval $(L'.toNF)) :=
      qNF.mkMulProof iM L sum
    pure ⟨x, ⟨Sign.plus, q(rfl)⟩, L', q(subst_add $pf_a $pf_b $pf_atom $pf_mul)⟩
  /- normalize a subtraction: `a - b` -/
  | ~q(HSub.hSub (self := @instHSub _ $i) $a $b) =>
    let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf₁⟩ ← normalize disch iM a
    let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf₂⟩ ← normalize disch iM b
    let ⟨L, l₁', l₂', pf₁', pf₂', _⟩ ← l₁.gcd iM l₂ disch false
    let ⟨e₁, pf₁''⟩ ← qNF.evalPretty iM l₁'
    let ⟨e₂, pf₂''⟩ ← qNF.evalPretty iM l₂'
    have pf_a := ← mkEqMul iM pf_sgn₁ q(Eq.trans $pf₁ (Eq.symm $pf₁')) pf₁''
    have pf_b := ← mkEqMul iM pf_sgn₂ q(Eq.trans $pf₂ (Eq.symm $pf₂')) pf₂''
    let e : Q($M) := q($(g₁.expr e₁) - $(g₂.expr e₂))
    let ⟨sum, pf_atom⟩ ← baseCase e false
    let _i ← synthInstanceQ q(Field $M)
    assumeInstancesCommute
    let L' := qNF.mul L sum
    let pf_mul : Q((NF.eval $(L.toNF)) * NF.eval $(sum.toNF) = NF.eval $(L'.toNF)) :=
      qNF.mkMulProof iM L sum
    pure ⟨x, ⟨Sign.plus, q(rfl)⟩, L', q(subst_sub $pf_a $pf_b $pf_atom $pf_mul)⟩
  /- normalize a negation: `-a` -/
  | ~q(Neg.neg (self := $i) $a) =>
    let ⟨y, ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM a
    try
      let iM' ← synthInstanceQ q(Field $M) -- FIXME don't re-synth if have it in `g`
      assumeInstancesCommute
      let ⟨G, pf_y⟩ ← Sign.neg iM' y g
      pure ⟨y, ⟨G, q(Eq.trans (congr_arg Neg.neg $pf_sgn) $pf_y)⟩, l, pf⟩
    catch _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩
  -- TODO special-case handling of zero? maybe not necessary
  /- anything else should be treated as an atom -/
  | _ => pure ⟨x, ⟨.plus, q(rfl)⟩, ← baseCase x true⟩

/-- The main algorithm behind the `field_simp` tactic: partially-normalizing an
expression in a field `M` into the form x1 ^ c1 * x2 ^ c2 * ... x_k ^ c_k,
where x1, x2, ... are distinct atoms in `M`, and c1, c2, ... are integers.

Version with "pretty" output. -/
def normalizePretty (disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type))
    (iM : Q(CommGroupWithZero $M)) (x : Q($M)) : AtomM (Σ x' : Q($M), Q($x = $x')) := do
  let ⟨y, ⟨g, pf_sgn⟩, l, pf⟩ ← normalize disch iM x
  let ⟨l', pf'⟩ ← qNF.removeZeros disch q(inferInstance) l
  let ⟨x', pf''⟩ ← qNF.evalPretty iM l'
  let zz : Q($y = $x') := q(Eq.trans (Eq.trans $pf $pf') $pf'')
  return ⟨g.expr x', q(Eq.trans $pf_sgn $(g.congr zz))⟩

/-- Given `e₁` and `e₂`, cancel nonzero factors to construct a new equality which is logically
equivalent to `e₁ = e₂`. -/
def reduceEqQ (disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type))
    (iM : Q(CommGroupWithZero $M)) (e₁ e₂ : Q($M)) :
    AtomM (Σ f₁ f₂ : Q($M), Q(($e₁ = $e₂) = ($f₁ = $f₂))) := do
  let ⟨_, ⟨g₁, pf_sgn₁⟩, l₁, pf_l₁⟩ ← normalize disch iM e₁
  let ⟨_, ⟨g₂, pf_sgn₂⟩, l₂, pf_l₂⟩ ← normalize disch iM e₂
  let ⟨_, l₁', l₂', pf_lhs, pf_rhs, pf₀⟩ ← l₁.gcd iM l₂ disch true
  let ⟨f₁', pf_l₁'⟩ ← l₁'.evalPretty iM
  let ⟨f₂', pf_l₂'⟩ ← l₂'.evalPretty iM
  have zz₁ := ← mkEqMul iM pf_sgn₁ q(Eq.trans $pf_l₁ (Eq.symm $pf_lhs)) pf_l₁'
  have zz₂ := ← mkEqMul iM pf_sgn₂ q(Eq.trans $pf_l₂ (Eq.symm $pf_rhs)) pf_l₂'
  return ⟨g₁.expr f₁', g₂.expr f₂', q(eq_eq_cancel_eq $zz₁ $zz₂ $pf₀)⟩

/-- Given an equality `a = b`, cancel nonzero factors to construct a new equality which is logically
equivalent to `a = b`. -/
def eval (disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type)) (e : Expr) :
    AtomM Simp.Result := do
  try
    let some ⟨_, a, b⟩ := e.eq? | throwError "not an equality"
    -- infer `u` and `K : Q(Type u)` such that `x : Q($K)`
    let ⟨u, K, a⟩ ← inferTypeQ' a
    -- find a `CommGroupWithZero` instance on `K`
    let iK : Q(CommGroupWithZero $K) ← synthInstanceQ q(CommGroupWithZero $K)
    trace[Tactic.field_simp] "clearing denominators in {a} = {b}"
    -- run the core equality-transforming mechanism on `a = b`
    let ⟨a', b', pf⟩ ← reduceEqQ disch iK a b
    let t' ← mkAppM ``Eq #[a', b']
    return { expr := t', proof? := pf }
  catch _ =>
    -- boring unless a function application
    guard e.isApp
    let ⟨f, _⟩ := e.getAppFnArgs
    guard <|
      f ∈ [``HMul.hMul, ``HDiv.hDiv, ``Inv.inv, ``HPow.hPow, ``HAdd.hAdd, ``HSub.hSub, ``Neg.neg]
    -- infer `u` and `K : Q(Type u)` such that `x : Q($K)`
    let ⟨u, K, _⟩ ← inferTypeQ' e
    -- find a `CommGroupWithZero` instance on `K`
    let iK : Q(CommGroupWithZero $K) ← synthInstanceQ q(CommGroupWithZero $K)
    -- run the core normalization function `normalizePretty` on `e`
    trace[Tactic.field_simp] "running conv on {e}"
    let ⟨e, pf⟩ ← normalizePretty disch iK e
    return { expr := e, proof? := some pf }

/-- Given `x` in a commutative group-with-zero, construct a new expression in the standard form
*** / *** (all denominators at the end) which is equal to `x`. -/
def reduceExpr (disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type)) (x : Expr) :
    MetaM Simp.Result := do
  -- infer `u` and `K : Q(Type u)` such that `x : Q($K)`
  let ⟨u, K, _⟩ ← inferTypeQ' x
  -- find a `CommGroupWithZero` instance on `K`
  let iK : Q(CommGroupWithZero $K) ← synthInstanceQ q(CommGroupWithZero $K)
  -- run the core normalization function `normalizePretty` on `x`
  trace[Tactic.field_simp] "running conv on {x}"
  let ⟨e, pf⟩ ← AtomM.run .reducible <| normalizePretty disch iK x
  return { expr := e, proof? := some pf }

/-- Given an equality `a = b`, cancel nonzero factors to construct a new equality which is logically
equivalent to `a = b`. -/
def reduceEq (disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type)) (t : Expr) :
    MetaM Simp.Result := do
  let some ⟨_, a, b⟩ := t.eq? | throwError "not an equality"
  -- infer `u` and `K : Q(Type u)` such that `x : Q($K)`
  let ⟨u, K, a⟩ ← inferTypeQ' a
  -- find a `CommGroupWithZero` instance on `K`
  let iK : Q(CommGroupWithZero $K) ← synthInstanceQ q(CommGroupWithZero $K)
  trace[Tactic.field_simp] "clearing denominators in {a} = {b}"
  -- run the core equality-transforming mechanism on `a = b`
  let ⟨a', b', pf⟩ ← AtomM.run .reducible <| reduceEqQ disch iK a b
  let t' ← mkAppM `Eq #[a', b']
  return { expr := t', proof? := pf }

open Elab Tactic Lean.Parser.Tactic

/-- If the user provided a discharger, elaborate it. If not, we will use the `field_simp` default
discharger, which (among other things) includes a simp-run for the specified argument list, so we
elaborate those arguments. -/
def parseDischarger (d : Option (TSyntax `Lean.Parser.Tactic.discharger))
    (args : Option (TSyntax `Lean.Parser.Tactic.simpArgs)) :
    TacticM (∀ {u : Level} (type : Q(Sort u)), MetaM Q($type)) := do
  match d with
  | none =>
    let ctx ← Simp.mkSimpContext (args.getD ⟨.missing⟩) (contextual := true)
    let tac := wrapSimpDischargerWithCtx FieldSimp.discharge ctx
    return (synthesizeUsing' · tac)
  | some d =>
    -- TODO if `args` is `some`, give user a warning here that it will be ignored
    match d with
    | `(discharger| (discharger:=$tac)) =>
      let tac := (evalTactic (← `(tactic| ($tac))) *> pruneSolvedGoals)
      return (synthesizeUsing' · tac)
    | _ => throwError "could not parse the provided discharger {d}"

/-- Conv tactic for field_simp normalisation. -/
elab "field_simp" d:(discharger)? args:(simpArgs)? : conv => do
  -- find the expression `x` to `conv` on
  let x ← Conv.getLhs
  let disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type) ← parseDischarger d args
  -- bring into field_simp standard form
  let r ← reduceExpr disch x
  -- convert `x` to the output of the normalization
  Conv.applySimpResult r

/-
Simprocs are `post` by default (but calling with `↓`, i.e. `simp [↓field, ...]`, makes it `pre`).

Summary of the meaning of the simproc outputs in "post" mode:
* `done (r : Result)` returns the result.
* `visit (e : Result)` is passed to `pre` again IF resulting expression is not equal (`==`) to
  initial expression.
* `continue (e? : Option Result := none)` is passed to `pre` again
-/
def reduceEqStep (disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type)) (t : Expr) :
    MetaM Simp.Step := do
  try
    return .visit (← reduceEq disch t)
  catch _ =>
    return .continue

def reduceExprStep (disch : ∀ {u : Level} (type : Q(Sort u)), MetaM Q($type)) (t : Expr) :
    MetaM Simp.Step := do
  try
    return .visit (← reduceExpr disch t)
  catch _ =>
    return .continue

simproc_decl _root_.field (Eq _ _) := fun (t : Expr) ↦ do
  let ctx ← Simp.getContext
  let disch {u} e := synthesizeUsing' (u := u) e <|
    wrapSimpDischargerWithCtx FieldSimp.discharge ctx
  reduceEqStep disch t

simproc_decl _root_.fieldExpr (_) := fun (t : Expr) ↦ do
  let ctx ← Simp.getContext
  let disch {u} e := synthesizeUsing' (u := u) e <|
    wrapSimpDischargerWithCtx FieldSimp.discharge ctx
  reduceExprStep disch t

elab "field_simp" d:(discharger)? args:(simpArgs)? loc:(location)? : tactic => withMainContext do
  let disch ← parseDischarger d args
  let s ← IO.mkRef {}
  let cleanup r := do r.mkEqTrans (← simpOnlyNames [``eq_self] r.expr)
  let m := AtomM.recurse s {} (eval disch) cleanup
  let loc := (loc.map expandLocation).getD (.targets #[] true)
  atLoc m "field_simp" (failIfUnchanged := true) (mayCloseGoalFromHyp := true) loc

end Mathlib.Tactic.FieldSimp

/-!
 We register `field_simp` with the `hint` tactic.
 -/
register_hint field_simp
