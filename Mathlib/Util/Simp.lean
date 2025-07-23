/-
Copyright (c) 2025 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
import Lean.Meta.Tactic.Simp.Types
import Mathlib.Init
import Qq

/-! # Additional simp utilities

This file adds additional tools for metaprogramming with the `simp` tactic

-/

open Lean Meta Qq Elab Tactic

namespace Lean.Meta.Simp

/-- `Qq` version of `Lean.Meta.Simp.Methods.discharge?`, which avoids having to use `~q` matching
on the proof expression returned by `discharge?`

`dischargeQ? (a : Q(Prop))` attempts to prove `a` using the discharger, returning
`some (pf : Q(a))` if a proof is found and `none` otherwise. -/
@[inline]
def Methods.dischargeQ? (M : Methods) (a : Q(Prop)) : SimpM <| Option Q($a) := M.discharge? a

-- adapted from `Lean.Elab.Tactic.mkSimpContext `
/-- Build a `Simp.Context` for a specified `optConfig`, following the same algorithm that would be
done in a "simp only" run: no simp-lemmas except for the small `simpOnlyBuiltins` set. -/
def mkSimpOnlyContext (cfg : Syntax) : TacticM Simp.Context := do
  let mut simpTheorems ← simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
  let congrTheorems ← Meta.getSimpCongrTheorems
  Simp.mkContext
    (config := (← elabSimpConfig cfg (kind := SimpKind.simp)))
    (simpTheorems := #[simpTheorems])
    congrTheorems

-- adapted from `Lean.Elab.Tactic.mkSimpContext `
/-- Build a `Simp.Context` with the default configuration (except that `contextual` may be
specified), following the same algorithm that would be done in a "simp" run: look up all the
simp-lemmas in the library, and adjust (add/erase) as specified by the provided `simpArgs` list. -/
def mkSimpContext (args : Syntax) (contextual : Bool := false) : TacticM Simp.Context := do
  let simpTheorems ← Meta.getSimpTheorems
  let congrTheorems ← Meta.getSimpCongrTheorems
  let ctx ← Simp.mkContext
     (config := { (← elabSimpConfig .missing (kind := SimpKind.simp)) with contextual } )
     (simpTheorems := #[simpTheorems])
     congrTheorems
  let r ← elabSimpArgs args (eraseLocal := false) (kind := SimpKind.simp) (simprocs := {}) ctx
  if !r.starArg then
    return r.ctx
  else
    let ctx := r.ctx
    let mut simpTheorems := ctx.simpTheorems
    /-
    When using `zetaDelta := false`, we do not expand let-declarations when using `[*]`.
    Users must explicitly include it in the list.
    -/
    let hs ← getPropHyps
    for h in hs do
      unless simpTheorems.isErased (.fvar h) do
        simpTheorems ← simpTheorems.addTheorem (.fvar h) (← h.getDecl).toExpr
          (config := ctx.indexConfig)
    return ctx.setSimpTheorems simpTheorems

end Lean.Meta.Simp
