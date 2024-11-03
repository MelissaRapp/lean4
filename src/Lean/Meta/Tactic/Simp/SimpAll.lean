/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Simp.Main

namespace Lean.Meta

open Simp (Stats SimprocsArray)

namespace SimpAll

structure Entry where
  fvarId   : FVarId -- original fvarId
  userName : Name
  id       : Origin -- id of the theorem at `SimpTheorems`
  origType : Expr
  type     : Expr
  proof    : Expr
  deriving Inhabited

structure State where
  modified     : Bool := false
  mvarId       : MVarId
  entries      : Array Entry := #[]
  ctx          : Simp.Context
  simprocs     : SimprocsArray
  usedTheorems : Simp.UsedSimps := {}
  diag         : Simp.Diagnostics := {}
  negativeCache: Simp.NegativeCache := {}
  localHyps  : SimpTheoremsArray := {}

abbrev M := StateRefT State MetaM

private def initEntries : M Unit := do
  let hs ←  (← get).mvarId.withContext do getPropHyps
  let hsNonDeps ← (← get).mvarId.getNondepPropHyps
  let mut simpThms := (← get).ctx.simpTheorems
  let mut localHyps : SimpTheoremsArray := {}
  let negativeCaching := (← get).ctx.config.negativeCaching
  for h in hs do
    unless simpThms.isErased (.fvar h) do
      let localDecl ← h.getDecl
      let proof  := localDecl.toExpr
      simpThms ← simpThms.addTheorem (.fvar h) proof
      if negativeCaching then localHyps ← localHyps.addTheorem (.fvar h) proof
      modify fun s => { s with ctx.simpTheorems := simpThms, localHyps := localHyps }
      if hsNonDeps.contains h then
        -- We only simplify nondependent hypotheses
        let type ← instantiateMVars localDecl.type
        let entry : Entry := { fvarId := h, userName := localDecl.userName, id := .fvar h, origType := type, type, proof }
        modify fun s => { s with entries := s.entries.push entry }

private abbrev getSimpTheorems : M SimpTheoremsArray :=
  return (← get).ctx.simpTheorems

private abbrev getLocalHyps : M SimpTheoremsArray :=
  return (← get).localHyps

private partial def loop : M Bool := do
  modify fun s => { s with modified := false }
  let simprocs := (← get).simprocs
  let negativeCaching := (← get).ctx.config.negativeCaching
  -- simplify entries
  for i in [:(← get).entries.size] do
    let mut negativeCache := (← get).negativeCache
    let entry := (← get).entries[i]!
    let ctx := (← get).ctx
    -- We disable the current entry to prevent it to be simplified to `True`
    let simpThmsWithoutEntry := (← getSimpTheorems).eraseTheorem entry.id
    let localHypsWithoutEntry := (← getLocalHyps).eraseTheorem entry.id
    let ctx := { ctx with simpTheorems := simpThmsWithoutEntry }
    let (r, stats, negativeCache') ← simpStepWithNegativeCache (← get).mvarId entry.proof entry.type ctx simprocs (stats := { (← get) with })
      (negativeCache := negativeCache) (localHyps := localHypsWithoutEntry)
    modify fun s => { s with usedTheorems := stats.usedTheorems, diag := stats.diag, negativeCache := negativeCache' }
    match r with
    | none => return true -- closed the goal
    | some (proofNew, typeNew) =>
      unless typeNew == entry.type do
        /- We must erase the `id` for the simplified theorem. Otherwise,
           the previous versions can be used to self-simplify the new version. For example, suppose we have
           ```
            x : Nat
            h : x ≠ 0
            ⊢ Unit
           ```
           In the first round, `h : x ≠ 0` is simplified to `h : ¬ x = 0`.

           It is also important for avoiding identical hypotheses to simplify each other to `True`.
           Example
           ```
           ...
           h₁ : p a
           h₂ : p a
           ⊢ q a
           ```
           `h₁` is first simplified to `True`. If we don't remove `h₁` from the set of simp theorems, it will
           be used to simplify `h₂` to `True` and information is lost.

           We must use `mkExpectedTypeHint` because `inferType proofNew` may not be equal to `typeNew` when
           we have theorems marked with `rfl`.
        -/
        trace[Meta.Tactic.simp.all] "entry.id: {← ppOrigin entry.id}, {entry.type} => {typeNew}"
        let mut simpThmsNew := (← getSimpTheorems).eraseTheorem (.fvar entry.fvarId)
        let idNew ← mkFreshId
        simpThmsNew ← simpThmsNew.addTheorem (.other idNew) (← mkExpectedTypeHint proofNew typeNew)
        let mut localHypsNew : SimpTheoremsArray := {}
        if negativeCaching then
         localHypsNew := (← getLocalHyps).eraseTheorem (.fvar entry.fvarId)
         localHypsNew ← localHypsNew.addTheorem (.other idNew) (← mkExpectedTypeHint proofNew typeNew)
        modify fun s => { s with
          modified         := true
          ctx.simpTheorems := simpThmsNew
          entries[i]       := { entry with type := typeNew, proof := proofNew, id := .other idNew }
          localHyps := localHypsNew
        }
  -- simplify target
  let mvarId := (← get).mvarId
  let (r, stats, negativeCache') ← simpTargetWithNegativeCache mvarId (← get).ctx simprocs (stats := { (← get) with })
    (negativeCache := (← get).negativeCache) (localHyps := ← getLocalHyps)
  modify fun s => { s with usedTheorems := stats.usedTheorems, diag := stats.diag, negativeCache := negativeCache' }
  match r with
  | none => return true
  | some mvarIdNew =>
    unless mvarId == mvarIdNew do
      modify fun s => { s with
        modified := true
        mvarId   := mvarIdNew
      }
  if (← get).modified then
    loop
  else
    return false

def main : M (Option MVarId) := do
  initEntries
  if (← loop) then
    return none -- close the goal
  else
    let mvarId := (← get).mvarId
    -- Prior to #2334, the logic here was to re-assert all hypotheses and call `tryClearMany` on them all.
    -- This had the effect that the order of hypotheses was sometimes modified, whether or not any where simplified.
    -- Now we only re-assert the first modified hypothesis,
    -- along with all subsequent hypotheses, so as to preserve the order of hypotheses.
    let mut toAssert := #[]
    let mut toClear := #[]
    let mut modified := false
    for e in (← get).entries do
      if e.type.isTrue then
        -- Do not assert `True` hypotheses
        toClear := toClear.push e.fvarId
      else if modified || e.type != e.origType then
        toClear := toClear.push e.fvarId
        toAssert := toAssert.push { userName := e.userName, type := e.type, value := e.proof }
        modified := true
    let (_, mvarId) ← mvarId.assertHypotheses toAssert
    mvarId.tryClearMany toClear

end SimpAll

def simpAllWithNegativeCache (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (stats : Stats := {})
    (negativeCache : Simp.NegativeCache := {}) : MetaM (Option MVarId × Stats × Simp.NegativeCache) := do
  mvarId.withContext do
    let (r, s) ← SimpAll.main.run { stats with mvarId, ctx, simprocs, negativeCache }
    if let .some mvarIdNew := r then
      if ctx.config.failIfUnchanged && mvarId == mvarIdNew then
        throwError "simp_all made no progress"
    return (r, { s with }, s.negativeCache )

def simpAll (mvarId : MVarId) (ctx : Simp.Context) (simprocs : SimprocsArray := #[]) (stats : Stats := {}) : MetaM (Option MVarId × Stats) := do
  let (result, stats, _) ← simpAllWithNegativeCache mvarId ctx simprocs stats
  return (result, stats)

builtin_initialize
  registerTraceClass `Meta.Tactic.simp.all

end Lean.Meta
