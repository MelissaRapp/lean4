/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Expr
import Lean.Util.PtrSet

namespace Lean
namespace Expr
namespace FindImpl

unsafe abbrev FindM (m) := StateT (PtrSet Expr) m

@[inline] unsafe def checkVisited [Monad m] (e : Expr) : OptionT (FindM m) Unit := do
  if (← get).contains e then
    failure
  modify fun s => s.insert e

unsafe def findM? [Monad m] (p : Expr → m Bool) (e : Expr) : OptionT (FindM m) Expr :=
  let rec visit (e : Expr) := do
    checkVisited e
    if ← p e then
      pure e
    else match e with
      | .forallE _ d b _ => visit d <|> visit b
      | .lam _ d b _     => visit d <|> visit b
      | .mdata _ b       => visit b
      | .letE _ t v b _  => visit t <|> visit v <|> visit b
      | .app f a         => visit f <|> visit a
      | .proj _ _ b      => visit b
      | _                => failure
  visit e

unsafe def findUnsafeM? {m} [Monad m] (p : Expr → m Bool) (e : Expr) : m (Option Expr) :=
  findM? p e |>.run' mkPtrSet

@[inline] unsafe def findUnsafe? (p : Expr → Bool) (e : Expr) : Option Expr := findUnsafeM? (m := Id) p e

end FindImpl

@[implemented_by FindImpl.findUnsafeM?]
/- This is a reference implementation for the unsafe one above -/
def findM? [Monad m] (p : Expr → m Bool) (e : Expr) : m (Option Expr) := do
  if ← p e then
    return some e
  else match e with
    | .forallE _ d b _ => findM? p d <||> findM? p b
    | .lam _ d b _     => findM? p d <||> findM? p b
    | .mdata _ b       => findM? p b
    | .letE _ t v b _  => findM? p t <||> findM? p v <||> findM? p b
    | .app f a         => findM? p f <||> findM? p a
    | .proj _ _ b      => findM? p b
    | _                => pure none

end Expr
end Lean
