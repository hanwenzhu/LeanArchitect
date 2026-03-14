import Architect.Basic
import Architect.Command


open Lean Elab Meta

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

/-- Whether a constant should be auto-included in the blueprint in `--all` mode.
Uses the same filtering as Lean's `allowCompletion` (IDE completion, `exact?`, etc.)
plus a declaration-ranges check (as in doc-gen4) to skip auto-generated declarations.
Only includes theorems, definitions, and inductives. -/
private def shouldAutoInclude (name : Name) : CoreM Bool := do
  let env ← getEnv
  -- Use Lean's canonical blacklist (isInternal, isAuxRecursor, isNoConfusion, isRec, isMatcher)
  if !allowCompletion env name then return false
  -- Skip private declarations
  if isPrivateName name then return false
  -- Skip if already tagged with @[blueprint]
  if (blueprintExt.find? env name).isSome then return false
  -- Skip declarations without source location (auto-generated, per doc-gen4)
  if (← findDeclarationRangesCore? name).isNone then return false
  -- Only include theorems, definitions, and inductives
  return match env.find? name with
    | some (.thmInfo _) => true
    | some (.defnInfo _) => true
    | some (.inductInfo _) => true
    | _ => false

/-- Create a default blueprint `Node` for a constant that was not explicitly tagged
with `@[blueprint]`. Used in `--all` mode. Uses the doc-string as the statement text. -/
private def mkDefaultNode (env : Environment) (name : Name) (docString : String := "") : Node :=
  let isTheorem := match env.find? name with
    | some (.thmInfo _) => true
    | _ => false
  {
    name
    latexLabel := name.toString
    statement := {
      text := docString
      uses := #[]
      excludes := #[]
      usesLabels := #[]
      excludesLabels := #[]
      latexEnv := if isTheorem then "theorem" else "definition"
    }
    proof := if isTheorem then some {
      text := ""
      uses := #[]
      excludes := #[]
      usesLabels := #[]
      excludesLabels := #[]
      latexEnv := "proof"
    } else none
    notReady := false
    discussion := none
    title := none
  }

/-- Get auto-included blueprint nodes for constants in a specific module.
Only enumerates constants belonging to the given module index — does not
traverse the full environment. Registers nodes in the blueprint environment
extensions so that downstream rendering (dependency inference, sorry detection,
`\lean{}` links) works correctly. -/
private def getAutoIncludedNodes (modIdx : ModuleIdx) : CoreM (Array BlueprintContent) := do
  let env ← getEnv
  let constNames := env.header.moduleData[modIdx.toNat]!.constNames
  let mut nodes : Array BlueprintContent := #[]
  for name in constNames do
    if ← shouldAutoInclude name then
      let docString := (← findDocString? (← getEnv) name).getD ""
      let node := mkDefaultNode (← getEnv) name docString
      -- Register in env extensions so rendering can find these nodes
      blueprintExt.add name node
      modifyEnv fun env => addLeanNameOfLatexLabel env node.latexLabel name
      nodes := nodes.push (.node (← node.toNodeWithPos))
  return nodes

/-- Get blueprint contents of the current module.
This is only used from `#show_blueprint` / `#show_blueprint_json` commands within a Lean file.
The extraction executable uses `getBlueprintContents` for all modules, since it loads them
as imports. -/
def getMainModuleBlueprintContents : CoreM (Array BlueprintContent) := do
  let env ← getEnv
  let nodes ← (blueprintExt.getEntries env).toArray.mapM fun (_, node) => BlueprintContent.node <$> node.toNodeWithPos
  let modDocs := (getMainModuleBlueprintDoc env).toArray.map BlueprintContent.modDoc
  return (nodes ++ modDocs).qsort BlueprintContent.order

/-- Get blueprint contents of an imported module.
Only enumerates constants belonging to the specified module. -/
def getBlueprintContents (module : Name) (all : Bool := false) : CoreM (Array BlueprintContent) := do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? module | return #[]
  let nodes ← (blueprintExt.getModuleEntries env modIdx).mapM fun (_, node) => BlueprintContent.node <$> node.toNodeWithPos
  let autoNodes ← if all then getAutoIncludedNodes modIdx else pure #[]
  let modDocs := (getModuleBlueprintDoc? env module).getD #[] |>.map BlueprintContent.modDoc
  return (nodes ++ autoNodes ++ modDocs).qsort BlueprintContent.order

end Architect
