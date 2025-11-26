import Lean
import Architect.CollectUsed
import Architect.Content
import Architect.Tactic


open Lean Meta Elab

namespace Architect

/-- `Config` is the type of arguments that can be provided to `blueprint`. -/
structure Config where
  /-- The statement of the node in text. -/
  statement : Option String := none
  /-- By default, only theorems have separate proof parts. This option overrides this behavior. -/
  hasProof : Option Bool := none
  /-- The proof of the node in text. Uses proof docstrings if not present. -/
  proof : Option String := none
  /-- The set of nodes that this node depends on. Infers from the constant if not present. -/
  uses : Array Name := #[]
  /-- Additional raw labels of nodes that this node depends on. -/
  usesRaw : Array String := #[]
  /-- The set of nodes that the proof of this node depends on. Infers from the constant's value if not present. -/
  proofUses : Array Name := #[]
  /-- Additional raw labels of nodes that the proof of this node depends on. -/
  proofUsesRaw : Array String := #[]
  /-- The surrounding environment is not ready to be formalized, typically because it requires more blueprint work. -/
  notReady : Bool := false
  /-- A GitHub issue number where the surrounding definition or statement is discussed. -/
  discussion : Option Nat := none
  /-- The short title of the node in LaTeX. -/
  title : Option String := none
  /-- The LaTeX environment to use for the node. -/
  latexEnv : Option String := none
  /-- The LaTeX label to use for the node. -/
  latexLabel : Option String := none
  /-- Enable debugging. -/
  trace : Bool := false
deriving Repr

syntax blueprintStatementOption := &"statement" " := " docComment
syntax blueprintHasProofOption := &"hasProof" " := " (&"true" <|> &"false")
syntax blueprintProofOption := &"proof" " := " docComment
syntax blueprintUsesOption := &"uses" " := " "[" (ident <|> str),* "]"
syntax blueprintProofUsesOption := &"proofUses" " := " "[" (ident <|> str),* "]"
syntax blueprintTitleOption := &"title" " := " str
syntax blueprintNotReadyOption := &"notReady" " := " (&"true" <|> &"false")
syntax blueprintDiscussionOption := &"discussion" " := " num
syntax blueprintLatexEnvOption := &"latexEnv" " := " str
syntax blueprintLatexLabelOption := &"latexLabel" " := " str

syntax blueprintOption := "("
  blueprintStatementOption <|>
  blueprintHasProofOption <|> blueprintProofOption <|>
  blueprintUsesOption <|> blueprintProofUsesOption <|>
  blueprintTitleOption <|>
  blueprintNotReadyOption <|> blueprintDiscussionOption <|>
  blueprintLatexEnvOption <|> blueprintLatexLabelOption ")"
syntax blueprintOptions := (ppSpace str)? (ppSpace blueprintOption)*

/--
The `blueprint` attribute tags a constant to add to the blueprint.

You may optionally add:
- `"latex-label"`: The LaTeX label to use for the node (default: the Lean name).
- `statement := /-- ... -/`: The statement of the node in LaTeX.
- `hasProof := true`: If the node has a proof part (default: true if the node is a theorem).
- `proof := /-- ... -/`: The proof of the node in LaTeX (default: the docstrings in proof tactics).
- `uses := [a, "b"]`: The dependencies of the node, as Lean constants or LaTeX labels (default: inferred from the used constants).
- `proofUses := [a, "b"]`: The dependencies of the proof of the node, as Lean constants or LaTeX labels (default: inferred from the used constants).
- `title := "Title"`: The title of the node in LaTeX.
- `notReady := true`: Whether the node is not ready.
- `discussion := 123`: The discussion issue number of the node.
- `latexEnv := "lemma"`: The LaTeX environment to use for the node (default: "theorem" or "definition").

For more information, see [LeanArchitect](https://github.com/hanwenzhu/LeanArchitect).

Use `blueprint?` to show the raw data of the added node.
-/
syntax (name := blueprint) "blueprint" "?"? blueprintOptions : attr

@[inherit_doc blueprint]
macro "blueprint?" opts:blueprintOptions : attr => `(attr| blueprint ? $opts)

/-- Elaborates the configuration options for `blueprint`. -/
def elabBlueprintConfig : Syntax → CoreM Config
  | `(attr| blueprint%$_tk $[?%$trace?]? $[$label?:str]? $[$opts:blueprintOption]*) => do
    let mut config : Config := { trace := trace?.isSome }
    if let some latexLabel := label? then config := { config with latexLabel := latexLabel.getString }
    for stx in opts do
      match stx with
      | `(blueprintOption| (statement := $doc)) =>
        validateDocComment doc
        let statement := (← getDocStringText doc).trim
        config := { config with statement }
      | `(blueprintOption| (hasProof := true)) =>
        config := { config with hasProof := some .true }
      | `(blueprintOption| (hasProof := false)) =>
        config := { config with hasProof := some .false }
      | `(blueprintOption| (proof := $doc)) =>
        validateDocComment doc
        let proof := (← getDocStringText doc).trim
        config := { config with proof }
      | `(blueprintOption| (uses := [$[$ids],*])) =>
        let uses ← ids.filterMapM fun
          | `(ident| $id:ident) => some <$> tryResolveConst id
          | _ => pure none
        let usesRaw := ids.filterMap fun
          | `(str| $str:str) => some str.getString
          | _ => none
        config := { config with uses := config.uses ++ uses, usesRaw := config.usesRaw ++ usesRaw }
      | `(blueprintOption| (proofUses := [$[$ids],*])) =>
        let proofUses ← ids.filterMapM fun
          | `(ident| $id:ident) => some <$> tryResolveConst id
          | _ => pure none
        let proofUsesRaw := ids.filterMap fun
          | `(str| $str:str) => some str.getString
          | _ => none
        config := { config with proofUses := config.proofUses ++ proofUses, proofUsesRaw := config.proofUsesRaw ++ proofUsesRaw }
      | `(blueprintOption| (title := $str)) =>
        config := { config with title := str.getString }
      | `(blueprintOption| (notReady := true)) =>
        config := { config with notReady := .true }
      | `(blueprintOption| (notReady := false)) =>
        config := { config with notReady := .false }
      | `(blueprintOption| (discussion := $n)) =>
        config := { config with discussion := n.getNat }
      | `(blueprintOption| (latexEnv := $str)) =>
        config := { config with latexEnv := str.getString }
      | `(blueprintOption| (latexLabel := $str)) =>
        config := { config with latexLabel := str.getString }
      | _ => throwUnsupportedSyntax
    return config
  | _ => throwUnsupportedSyntax

/-- Whether a node has a proof part. -/
def hasProof (name : Name) (cfg : Config) : CoreM Bool := do
  return cfg.hasProof.getD (cfg.proof.isSome || wasOriginallyTheorem (← getEnv) name)

def mkStatementPart (_name : Name) (latexLabel : String) (cfg : Config) (hasProof : Bool) (used : NameSet) :
    CoreM NodePart := do
  let env ← getEnv
  let leanOk := !used.contains ``sorryAx
  -- Used constants = blueprint constants specified by `uses :=` + used in the statement
  let uses := cfg.uses.foldl (·.insert ·) used
  let usesLabels : Std.HashSet String := .ofArray <|
    uses.toArray.filterMap fun c => (blueprintExt.find? env c).map (·.latexLabel)
  let statement := cfg.statement.getD ""
  return {
    leanOk
    text := statement
    uses := (usesLabels.erase latexLabel).toArray ++ cfg.usesRaw
    latexEnv := cfg.latexEnv.getD (if hasProof then "theorem" else "definition")
  }

def mkProofPart (name : Name) (latexLabel : String) (cfg : Config) (used : NameSet) : CoreM NodePart := do
  let env ← getEnv
  let leanOk := !used.contains ``sorryAx
  -- Used constants = blueprint constants specified by `proofUses :=` + used in the statement
  let uses := cfg.proofUses.foldl (·.insert ·) used
  let usesLabels : Std.HashSet String := .ofArray <|
    uses.toArray.filterMap fun c => (blueprintExt.find? env c).map (·.latexLabel)
  -- Use proof docstring for proof text
  let proof := cfg.proof.getD ("\n\n".intercalate (getProofDocString env name).toList)
  return {
    leanOk
    text := proof
    uses := (usesLabels.erase latexLabel).toArray ++ cfg.proofUsesRaw
    latexEnv := "proof"
  }

def mkNode (name : Name) (cfg : Config) : CoreM Node := do
  trace[blueprint.debug] "mkNode {.ofConstName name} {repr cfg}"
  let (statementUsed, proofUsed) ← collectUsed name
  trace[blueprint.debug] "Collected used constants:
    {.ofArray (statementUsed.toArray.map .ofConstName)}
    {.ofArray (proofUsed.toArray.map .ofConstName)}"
  let latexLabel := cfg.latexLabel.getD name.toString
  if ← hasProof name cfg then
    let statement ← mkStatementPart name latexLabel cfg .true statementUsed
    let proof ← mkProofPart name latexLabel cfg proofUsed
    return { cfg with name, latexLabel, statement, proof }
  else
    let used := statementUsed ∪ proofUsed
    let statement ← mkStatementPart name latexLabel cfg .false used
    return { cfg with name, latexLabel, statement, proof := none }

register_option blueprint.checkCyclicUses : Bool := {
  defValue := .true,
  descr := "Whether to check for cyclic dependencies in the blueprint."
}

/--
Raises an error if `newLabel` occurs in the (irreflexive transitive) dependencies of `label`.
If ignored, this would create a cycle and then an error during `leanblueprint web`.

(Note: this check will only raise an error if `blueprint.ignoreUnknownConstants` is true,
which may permit cyclic dependencies.)
-/
partial def checkCyclicUses {m} [Monad m] [MonadEnv m] [MonadError m]
    (newLabel : String) (label : String)
    (visited : Std.HashSet String := ∅) (path : Array String := #[]) : m Unit := do
  let path' := path.push label
  if visited.contains label then
    if path.contains label then
      throwError "cyclic dependency in blueprint:\n  {" uses ".intercalate (path'.toList.map toString)}"
    else
      return
  let visited' := visited.insert label

  for name in getLeanNamesOfLatexLabel (← getEnv) label do
    if let some node := blueprintExt.find? (← getEnv) name then
      for used in node.statement.uses ++ (node.proof.map (·.uses) |>.getD #[]) do
        checkCyclicUses newLabel used visited' path'
    else
      throwError "unknown constant {name} in blueprint"

initialize registerBuiltinAttribute {
    name := `blueprint
    descr := "Adds a node to the blueprint"
    applicationTime := .afterCompilation
    add := fun name stx kind => do
      unless kind == AttributeKind.global do throwError "invalid attribute 'blueprint', must be global"
      let cfg ← elabBlueprintConfig stx
      withOptions (·.updateBool `trace.blueprint (cfg.trace || ·)) do

      let node ← mkNode name cfg
      blueprintExt.add name node
      modifyEnv fun env => addLeanNameOfLatexLabel env node.latexLabel name
      trace[blueprint] "Blueprint node added:\n{repr node}"

      if blueprint.checkCyclicUses.get (← getOptions) then
        checkCyclicUses node.latexLabel node.latexLabel

      -- pushInfoLeaf <| .ofTermInfo {
      --   elaborator := .anonymous, lctx := {}, expectedType? := none,
      --   stx, expr := toExpr node }
  }

end Architect
