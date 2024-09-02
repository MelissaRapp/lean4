/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr
import Lean.Util.PtrSet
import Lean.Meta.Basic

namespace Lean
namespace Expr
namespace FindImplTelescoping
open Lean.Meta
unsafe abbrev FindM (m) := StateT (PtrSet Expr) m

@[inline] unsafe def checkVisited [Monad m] (e : Expr) : OptionT (FindM m) Unit := do
  if (← get).contains e then
    failure
  modify fun s => s.insert e

unsafe def findMTelescoping? [Monad m] [MonadControlT MetaM m] (p : Expr → m Bool) (e : Expr) : OptionT (FindM m) Expr :=
  let rec visit (e : Expr) := do
    checkVisited e
    if ← p e then
      pure e
    else match e with
      | .forallE _ d b _ => visit d <|> forallTelescope e fun xs _ => visit (b.instantiate xs)
      | .lam _ d b _     => visit d <|> lambdaTelescope e fun xs _ => visit (b.instantiate xs)
      | .mdata _ b       => visit b
      | .letE _ t v b _  => visit t <|> visit v <|> lambdaLetTelescope e fun xs _ => visit (b.instantiate xs)
      | .app f a         => visit f <|> visit a
      | .proj _ _ b      => visit b
      | _                => failure
  visit e

unsafe def findUnsafeMTelescoping? {m} [Monad m] [MonadControlT MetaM m]  [MonadTrace m] (p : Expr → m Bool) (e : Expr) : m (Option Expr) :=
  findMTelescoping? p e |>.run' mkPtrSet

end FindImplTelescoping

@[implemented_by FindImplTelescoping.findUnsafeMTelescoping?]
/- This is a reference implementation for the unsafe one above -/
def findMTelescoping? [Monad m] [MonadControlT MetaM m] [MonadTrace m] (p : Expr → m Bool) (e : Expr) : m (Option Expr) := do
  if ← p e then
    return some e
  else match e with
    | .forallE _ d b _ => findMTelescoping? p d <||> findMTelescoping? p b
    | .lam _ d b _     => findMTelescoping? p d <||> findMTelescoping? p b
    | .mdata _ b       => findMTelescoping? p b
    | .letE _ t v b _  => findMTelescoping? p t <||> findMTelescoping? p v <||> findMTelescoping? p b
    | .app f a         => findMTelescoping? p f <||> findMTelescoping? p a
    | .proj _ _ b      => findMTelescoping? p b
    | _                => pure none

def anyMTelescoping [Monad m] [MonadControlT MetaM m] [MonadTrace m] (p : Expr → m Bool) (e : Expr) : m Bool := do
  pure (<-findMTelescoping? p e).isSome

end Expr
end Lean
