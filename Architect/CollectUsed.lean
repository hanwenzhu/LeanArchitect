module

public import Architect.Basic

public meta section

/-!
This is similar to Lean's `collectAxioms`, but collects nodes in the blueprint (plus all axioms)
rather than just axioms.
-/

namespace Architect

open Lean

namespace CollectUsed

structure Context where
  env : Environment
  opts : Options
  root : Name

structure State where
  visited : NameSet    := {}
  used    : Array Name := #[]

abbrev M := ReaderT Context $ StateM State

partial def collect (c : Name) : M Unit := do
  let collectExpr (e : Expr) : M Unit := e.getUsedConstants.forM collect
  let s ← get
  unless s.visited.contains c do
    modify fun s => { s with visited := s.visited.insert c }
    let { env, opts, root } ← read
    -- When we collect constants used by `a`, we don't just want to return `{a}`.
    if c != root && isBlueprintNode env opts c then
      modify fun s => { s with used := s.used.push c }
    else
      -- This line is `match env.checked.get.find? c with` in Lean.CollectAxioms
      match env.find? c with
      | some (ConstantInfo.axiomInfo _)  => modify fun s => { s with used := s.used.push c }
      | some (ConstantInfo.defnInfo v)   => collectExpr v.type *> collectExpr v.value
      | some (ConstantInfo.thmInfo v)    => collectExpr v.type *> collectExpr v.value
      | some (ConstantInfo.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
      | some (ConstantInfo.quotInfo _)   => pure ()
      | some (ConstantInfo.ctorInfo v)   => collectExpr v.type
      | some (ConstantInfo.recInfo v)    => collectExpr v.type
      | some (ConstantInfo.inductInfo v) => collectExpr v.type *> v.ctors.forM collect
      | none                             => pure ()

end CollectUsed

/--
Returns the irreflexive transitive set of blueprint nodes that a constant depends on,
as a pair of sets (constants used by type, constants used by value).
They are made disjoint except that possibly both contain `sorryAx`.
-/
def collectUsed [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m] (constName : Name) :
    m (NameSet × NameSet) := do
  let env ← getEnv
  let opts ← getOptions
  let mut s : CollectUsed.State := {}

  -- Collect constants used by statement
  let info ← getConstInfo constName
  for c in info.type.getUsedConstants do
    (_, s) := ((CollectUsed.collect c).run { env, opts, root := constName }).run s
  let typeUsed := NameSet.ofArray s.used

  -- Collect constants used by proof
  (_, s) := ((CollectUsed.collect constName).run { env, opts, root := constName }).run s
  let valueUsed := NameSet.ofArray s.used

  return (typeUsed, valueUsed \ typeUsed.erase ``sorryAx)

end Architect
