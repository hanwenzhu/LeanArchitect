module

public import Architect.Basic
public import Architect.Command

public meta section

open Lean Elab

namespace Architect

/-! The blueprint content in a module (see `BlueprintContent`) consists of:

- Blueprint nodes extracted  from `@[blueprint]` tags
- All module docstrings defined in `blueprint_comment /-- ... -/`

These contents are sorted by declaration range (similar to the sort in doc-gen4).
-/

deriving instance Repr for ModuleDoc in
/-- The export blueprint LaTeX from a module is determined by the list of `BlueprintContent`
in the module. This is analogous to doc-gen4's `ModuleMember`. -/
inductive BlueprintContent where
  | node : NodeWithPos → BlueprintContent
  | modDoc : ModuleDoc → BlueprintContent
deriving Inhabited, Repr

def BlueprintContent.declarationRange : BlueprintContent → Option DeclarationRange
  | .node n => n.location.map (·.range)
  | .modDoc doc => some doc.declarationRange

/-- An order for blueprint contents, based on their declaration range. -/
def BlueprintContent.order (l r : BlueprintContent) : Bool :=
  match l.declarationRange, r.declarationRange with
  | some l, some r => Position.lt l.pos r.pos
  | some _, none => true
  | _, _ => false

/-- Get blueprint contents of the current module. -/
def getMainModuleBlueprintContents : CoreM (Array BlueprintContent) := do
  let env ← getEnv
  let opts ← getOptions
  let nodes ← (getLocalBlueprintNodes env opts).mapM fun (_, node) => BlueprintContent.node <$> node.toNodeWithPos
  let modDocs := (getMainModuleBlueprintDoc env).toArray.map BlueprintContent.modDoc
  return (nodes ++ modDocs).qsort BlueprintContent.order

/-- Get blueprint contents of an imported module. When `blueprint.all` is set, auto-nodes for the
module's own declarations are included (this is the path used by `lake build :blueprint`). -/
def getBlueprintContents (module : Name) : CoreM (Array BlueprintContent) := do
  let env ← getEnv
  let opts ← getOptions
  let some modIdx := env.getModuleIdx? module | return #[]
  let allNodes := getModuleBlueprintNodes env opts modIdx ++ getModuleAutoBlueprintNodes env opts modIdx
  let nodes ← allNodes.mapM fun (_, node) => BlueprintContent.node <$> node.toNodeWithPos
  let modDocs := (getModuleBlueprintDoc? env module).getD #[] |>.map BlueprintContent.modDoc
  return (nodes ++ modDocs).qsort BlueprintContent.order

end Architect
