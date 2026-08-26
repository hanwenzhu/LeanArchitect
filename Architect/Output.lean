module

public import Architect.CollectUsed
public import Architect.Content
public import Architect.Tactic

public meta section

open Lean

namespace Architect

section ToLatex

/-!
Conversion from Lean nodes to LaTeX.
-/

abbrev Latex := String

/-!
We convert nodes to LaTeX.

The output provides the following macros:
- `\inputleannode{name}`: Inputs the theorem or definition with label `name`.
- `\inputleanmodule{Module}`: Inputs the entire module (containing nodes and blueprint module docstrings in it) with module name `Module`.

The structure of the output of a module `A` with nodes `b` and `c` is:
```
A.tex
A/b.tex
A/c.tex
```

The first is a header file that defines the macro `\inputleannode{name}`, which simply inputs `A/name.tex`.
The rest are artifact files that contain the LaTeX of each node.
-/

def Latex.input (file : System.FilePath) : Latex :=
  -- Windows prints filepaths using backslashes (\) instead of forward slashes (/).
  -- LaTeX interprets these as control sequences, so we replace backslashes with forward slashes.
  "\\input{" ++ "/".intercalate file.components ++ "}"

variable {m} [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m]

def preprocessLatex (s : String) : String :=
  s

structure InferredUses where
  uses : Array String
  leanOk : Bool

def InferredUses.empty : InferredUses := { uses := #[], leanOk := true }

def InferredUses.merge (inferredUsess : Array InferredUses) : InferredUses :=
  { uses := inferredUsess.flatMap (·.uses), leanOk := inferredUsess.all (·.leanOk) }

def NodePart.inferUses (part : NodePart) (latexLabel : String) (used : NameSet) : m InferredUses := do
  let env ← getEnv
  let opts ← getOptions
  let uses := part.uses.foldl (·.insert ·) used |>.filter (· ∉ part.excludes)
  let mut usesLabels : Std.HashSet String := .ofArray <|
    uses.toArray.filterMap fun c => (findBlueprintNode? env opts c).map (·.latexLabel)
  usesLabels := usesLabels.erase latexLabel
  usesLabels := part.usesLabels.foldl (·.insert ·) usesLabels |>.filter (· ∉ part.excludesLabels)
  return { uses := usesLabels.toArray, leanOk := !uses.contains ``sorryAx }

/-- Infer the used constants of a node as (statement uses, proof uses). -/
def Node.inferUses (node : Node) : m (InferredUses × InferredUses) := do
  let (statementUsed, proofUsed) ← collectUsed node.name
  if let some proof := node.proof then
    return (
      ← node.statement.inferUses node.latexLabel statementUsed,
      ← proof.inferUses node.latexLabel proofUsed
    )
  else
    return (
      ← node.statement.inferUses node.latexLabel (statementUsed ∪ proofUsed),
      InferredUses.empty
    )

/-- Merges and converts an array of `NodePart` to LaTeX. It is assumed that `part ∈ allParts`. -/
def NodePart.toLatex (part : NodePart) (allParts : Array NodePart := #[part]) (inferredUses : InferredUses)
    (title : Option String := none) (additionalContent : String := "") (defaultText : String := "") : m Latex := do
  let mut out := ""
  out := out ++ "\\begin{" ++ part.latexEnv ++ "}"
  if let some title := title then
    out := out ++ s!"[{preprocessLatex title}]"
  out := out ++ "\n"

  -- Take union of uses
  unless inferredUses.uses.isEmpty do
    out := out ++ "\\uses{" ++ ",".intercalate inferredUses.uses.toList ++ "}\n"

  out := out ++ additionalContent

  -- \leanok only if all parts are leanOk
  if inferredUses.leanOk then
    out := out ++ "\\leanok\n"

  -- If not specified, the main text defaults to the first non-empty text in the parts
  let text := if !part.text.isEmpty then part.text else
    allParts.findSome? (fun p => if !p.text.isEmpty then p.text else none) |>.getD defaultText
  let textLatex := (preprocessLatex text).trimAscii
  unless textLatex.isEmpty do
    out := out ++ textLatex ++ "\n"

  out := out ++ "\\end{" ++ part.latexEnv ++ "}\n"
  return out

def isMathlibOk (name : Name) : m Bool := do
  return isLibraryDecl (← getEnv) name

/-- Whether a node is sorry-free (both statement and proof have no `sorryAx`). -/
def Node.isLeanOk (node : Node) : m Bool := do
  let (stmtUses, proofUses) ← node.inferUses
  return stmtUses.leanOk && proofUses.leanOk

/-- Progress statistics for blueprint nodes. -/
structure ProgressStats where
  total : Nat
  sorryFree : Nat
  containsSorry : Nat
  notReady : Nat

instance : ToString ProgressStats where
  toString s :=
    -- Round to nearest, then adjust the last category so percentages sum to 100
    let round (n : Nat) : Nat :=
      if s.total == 0 then 0 else (n * 100 + s.total / 2) / s.total
    let p1 := round s.sorryFree
    let p2 := round s.containsSorry
    let p3 := if s.total == 0 then 0 else 100 - p1 - p2
    let header := "Blueprint Progress"
    let tw := s!"{s.total}".length
    let pad (n : Nat) := "".pushn ' ' (tw - s!"{n}".length)
    let ppad (p : Nat) := "".pushn ' ' (3 - s!"{p}".length)
    let totalPad := "".pushn ' ' (tw + 1)
    let lines := #[
      s!"Total:        {totalPad}{s.total} nodes",
      s!"Formalized:   {pad s.sorryFree}{s.sorryFree}/{s.total} {ppad p1}({p1}%)",
      s!"Incomplete:   {pad s.containsSorry}{s.containsSorry}/{s.total} {ppad p2}({p2}%)",
      s!"Not ready:    {pad s.notReady}{s.notReady}/{s.total} {ppad p3}({p3}%)"
    ]
    let maxWidth := lines.foldl (fun acc l => max acc l.length) header.length
    let separator := "".pushn '─' maxWidth
    header ++ "\n" ++ separator ++ "\n" ++ "\n".intercalate lines.toList

/-- Progress report with aggregate stats and optional per-module breakdown. -/
structure ProgressReport where
  aggregate : ProgressStats
  byModule : Array (Name × ProgressStats)
  showByModule : Bool := true

instance : ToString ProgressReport where
  toString r :=
    let agg := toString r.aggregate
    if !r.showByModule || r.byModule.isEmpty then
      agg
    else
      -- Only show modules that have blueprint nodes
      let modules := r.byModule.filter (·.2.total > 0)
      if modules.isEmpty then agg
      else
        -- Align columns: find max width of module name and fraction
        let maxNameWidth := modules.foldl (fun acc (mod, _) => max acc (toString mod).length) 0
        let maxFracWidth := modules.foldl (fun acc (_, s) =>
          max acc s!"{s.sorryFree}/{s.total}".length) 0
        let moduleLines := modules.map fun (mod, s) =>
          let name := toString mod
          let frac := s!"{s.sorryFree}/{s.total}"
          let namePad := "".pushn ' ' (maxNameWidth - name.length)
          let fracPad := "".pushn ' ' (maxFracWidth - frac.length)
          let pct := if s.total == 0 then "0" else toString ((s.sorryFree * 100 + s.total / 2) / s.total)
          s!"  {name}{namePad}  {fracPad}{frac}  ({pct}%)"
        let allLines := #[agg, "", "By module:"] ++ moduleLines
        "\n".intercalate allLines.toList

def ProgressStats.merge (a b : ProgressStats) : ProgressStats :=
  { total := a.total + b.total
    sorryFree := a.sorryFree + b.sorryFree
    containsSorry := a.containsSorry + b.containsSorry
    notReady := a.notReady + b.notReady }

def ProgressStats.empty : ProgressStats :=
  { total := 0, sorryFree := 0, containsSorry := 0, notReady := 0 }

/-- Compute progress statistics for an array of blueprint nodes.
Categories are mutually exclusive: a node is either formalized (sorry-free),
incomplete (contains sorry), or not ready. These three sum to `total`. -/
def computeProgress (nodes : Array Node) : m ProgressStats := do
  let mut sorryFree := 0
  let mut containsSorry := 0
  let mut notReadyCount := 0
  for node in nodes do
    if node.notReady then
      notReadyCount := notReadyCount + 1
    else if ← node.isLeanOk then
      sorryFree := sorryFree + 1
    else
      containsSorry := containsSorry + 1
  return {
    total := nodes.size
    sorryFree
    containsSorry
    notReady := notReadyCount
  }

def NodeWithPos.toLatex (node : NodeWithPos) : m Latex := do
  -- In the output, we merge the Lean nodes corresponding to the same LaTeX label.
  let env ← getEnv
  let opts ← getOptions
  -- Auto-nodes (from `blueprint.all`) are materialized during extraction and don't register a
  -- `latexLabel → name` mapping the way `@[blueprint]` does, so fall back to this node's own name.
  let labelNames := getLeanNamesOfLatexLabel env node.latexLabel
  let allLeanNames := if labelNames.isEmpty then #[node.name] else labelNames
  let allNodes := allLeanNames.filterMap fun name => findBlueprintNode? env opts name

  let mut addLatex := ""
  addLatex := addLatex ++ "\\label{" ++ node.latexLabel ++ "}\n"

  addLatex := addLatex ++ "\\lean{" ++ ",".intercalate (allLeanNames.map toString).toList ++ "}\n"
  if allNodes.any (·.notReady) then
    addLatex := addLatex ++ "\\notready\n"
  if let some d := allNodes.findSome? (·.discussion) then
    addLatex := addLatex ++ "\\discussion{" ++ toString d ++ "}\n"
  if ← allNodes.allM (isMathlibOk ·.name) then
    addLatex := addLatex ++ "\\mathlibok\n"

  -- position string as annotation
  let posStr := match node.file, node.location with
    | some file, some location => s!"{file}:{location.range.pos.line}.{location.range.pos.column}-{location.range.endPos.line}.{location.range.endPos.column}"
    | _, _ => ""
  addLatex := addLatex ++ s!"% at {posStr}\n"

  let inferredUsess ← allNodes.mapM (·.inferUses)
  let statementUses := InferredUses.merge (inferredUsess.map (·.1))
  let proofUses := InferredUses.merge (inferredUsess.map (·.2))

  let statementLatex ← node.statement.toLatex (allNodes.map (·.statement)) statementUses (allNodes.findSome? (·.title)) addLatex
  match node.proof with
  | none => return statementLatex
  | some proof =>
    let proofDocString := getProofDocString env node.name
    let proofLatex ← proof.toLatex (allNodes.filterMap (·.proof)) proofUses (defaultText := proofDocString)
    return statementLatex ++ proofLatex

/-- `LatexArtifact` represents an auxiliary output file for a single node,
containing its label (which is its filename) and content. -/
structure LatexArtifact where
  id : String
  content : Latex

/-- `LatexOutput` represents the extracted LaTeX from a module, consisting of a header file and auxiliary files. -/
structure LatexOutput where
  /-- The header file requires the path to the artifacts directory. -/
  header : System.FilePath → Latex
  artifacts : Array LatexArtifact

def NodeWithPos.toLatexArtifact (node : NodeWithPos) : m LatexArtifact := do
  return { id := node.latexLabel, content := ← node.toLatex }

def BlueprintContent.toLatex : BlueprintContent → m Latex
  | .node n => return "\\inputleannode{" ++ n.latexLabel ++ "}"
  | .modDoc d => return d.doc

def latexPreamble : m Latex := do
  return "%%% This file is automatically generated by LeanArchitect. %%%

%%% Macro definitions for \\inputleannode, \\inputleanmodule %%%

\\makeatletter

% \\newleannode{name}{latex} defines a new Lean node
\\providecommand{\\newleannode}[2]{%
  \\expandafter\\gdef\\csname leannode@#1\\endcsname{#2}}
% \\inputleannode{name} inputs a Lean node
\\providecommand{\\inputleannode}[1]{%
  \\csname leannode@#1\\endcsname}

% \\newleanmodule{module}{latex} defines a new Lean module
\\providecommand{\\newleanmodule}[2]{%
  \\expandafter\\gdef\\csname leanmodule@#1\\endcsname{#2}}
% \\inputleanmodule{module} inputs a Lean module
\\providecommand{\\inputleanmodule}[1]{%
  \\csname leanmodule@#1\\endcsname}

\\makeatother

%%% Start of main content %%%"

private def dedupContentsByLatexLabel (contents : Array BlueprintContent) : Array BlueprintContent := Id.run do
  let mut seen : Std.HashSet String := ∅
  let mut result : Array BlueprintContent := #[]
  for content in contents do
    match content with
    | .node n =>
      if seen.contains n.latexLabel then
        continue
      seen := seen.insert n.latexLabel
      result := result.push content
    | .modDoc _ =>
      result := result.push content
  return result

/-- Convert a module to a header file and artifacts. The header file requires the path to the artifacts directory. -/
private def moduleToLatexOutputAux (module : Name) (contents : Array BlueprintContent) : m LatexOutput := do
  -- First deduplicate contents by LaTeX label
  let contents' := dedupContentsByLatexLabel contents
  -- Artifact files
  let artifacts : Array LatexArtifact := ← contents'.filterMapM fun
    | .node n => n.toLatexArtifact
    | _ => pure none
  -- Header file
  let preamble ← latexPreamble
  let headerModuleLatex ← contents'.mapM BlueprintContent.toLatex
  let header (artifactsDir : System.FilePath) : Latex :=
    preamble ++ "\n\n" ++
      "\n\n".intercalate (artifacts.map fun ⟨id, _⟩ => "\\newleannode{" ++ id ++ "}{" ++ Latex.input (artifactsDir / id) ++ "}").toList ++ "\n\n" ++
      "\\newleanmodule{" ++ module.toString ++ "}{\n" ++ "\n\n".intercalate headerModuleLatex.toList ++ "\n}"
  return { header, artifacts }

/-- Convert imported module to LaTeX (header file, artifact files). -/
def moduleToLatexOutput (module : Name) : CoreM LatexOutput := do
  let contents ← getBlueprintContents module
  moduleToLatexOutputAux module contents

/-- Convert current module to LaTeX (header file, artifact files). -/
def mainModuleToLatexOutput : CoreM LatexOutput := do
  let contents ← getMainModuleBlueprintContents
  moduleToLatexOutputAux (← getMainModule) contents

/-- Shows the blueprint LaTeX of the current module (`#show_blueprint`) or
a blueprint node (`#show_blueprint lean_name` or `#show_blueprint "latex_label"`). -/
syntax (name := show_blueprint) "#show_blueprint" (ppSpace (ident <|> str))? : command

open Elab Command in
@[command_elab show_blueprint] def elabShowBlueprint : CommandElab
  | `(command| #show_blueprint) => do
    let output ← liftCoreM mainModuleToLatexOutput
    output.artifacts.forM fun art => logInfo m!"LaTeX of node {art.id}:\n{art.content}"
    logInfo m!"LaTeX of current module:\n{output.header ""}"
  | `(command| #show_blueprint $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let env ← getEnv
    let opts ← getOptions
    let some node := findBlueprintNode? env opts name | throwError "{name} does not have @[blueprint] attribute"
    let art ← (← liftCoreM node.toNodeWithPos).toLatexArtifact
    logInfo m!"{art.content}"
  | `(command| #show_blueprint $label:str) => do
    let env ← getEnv
    let names := getLeanNamesOfLatexLabel env label.getString
    if names.isEmpty then throwError "no @[blueprint] nodes with label {label}"
    for name in names do
      elabCommand <| ← `(command| #show_blueprint $(mkIdent name))
  | _ => throwUnsupportedSyntax

end ToLatex

section ToJson

private def rangeToJson (range : DeclarationRange) : Json :=
  json% {
    "pos": $(range.pos),
    "endPos": $(range.endPos)
  }

private def locationToJson (location : DeclarationLocation) : Json :=
  json% {
    "module": $(location.module),
    "range": $(rangeToJson location.range)
  }

def NodeWithPos.toJson (node : NodeWithPos) : Json :=
  json% {
    "name": $(node.name),
    "latexLabel": $(node.latexLabel),
    "statement": $(node.statement),
    "proof": $(node.proof),
    "notReady": $(node.notReady),
    "discussion": $(node.discussion),
    "title": $(node.title),
    "hasLean": $(node.hasLean),
    "file": $(node.file),
    "location": $(node.location.map locationToJson)
  }

def BlueprintContent.toJson : BlueprintContent → Json
  | .node n => json% {"type": "node", "data": $(n.toJson)}
  | .modDoc d => json% {"type": "moduleDoc", "data": $(d.doc)}

def moduleToJson (module : Name) : CoreM Json := do
  return Json.arr <|
    (← getBlueprintContents module).map BlueprintContent.toJson

def mainModuleToJson : CoreM Json := do
  return Json.arr <|
    (← getMainModuleBlueprintContents).map BlueprintContent.toJson

/-- Shows the blueprint JSON of the current module (`#show_blueprint_json`) or
a single Lean declaration (`#show_blueprint_json name`). -/
syntax (name := show_blueprint_json) "#show_blueprint_json" (ppSpace (ident <|> str))? : command

open Elab Command in
@[command_elab show_blueprint_json] def elabShowBlueprintJson : CommandElab
  | `(command| #show_blueprint_json) => do
    let json ← liftCoreM mainModuleToJson
    logInfo m!"{json}"
  | `(command| #show_blueprint_json $id:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let env ← getEnv
    let opts ← getOptions
    let some node := findBlueprintNode? env opts name | throwError "{name} does not have @[blueprint] attribute"
    let json := (← liftCoreM node.toNodeWithPos).toJson
    logInfo m!"{json}"
  | `(command| #show_blueprint_json $label:str) => do
    let env ← getEnv
    let names := getLeanNamesOfLatexLabel env label.getString
    if names.isEmpty then throwError "no @[blueprint] nodes with label {label}"
    for name in names do
      elabCommand <| ← `(command| #show_blueprint_json $(mkIdent name))
  | _ => throwUnsupportedSyntax

end ToJson

section Progress

/-- Shows blueprint progress statistics.
- `#blueprint_progress` shows project-wide statistics with per-module breakdown.
- `#blueprint_progress nobreakdown` shows project-wide statistics without breakdown.
- `#blueprint_progress local` shows current module statistics with per-module breakdown.
- `#blueprint_progress local nobreakdown` shows current module statistics without breakdown. -/
declare_syntax_cat blueprintProgressOpt
syntax &"local" : blueprintProgressOpt
syntax "nobreakdown" : blueprintProgressOpt
syntax (name := blueprint_progress) "#blueprint_progress" (ppSpace blueprintProgressOpt)* : command

open Elab Command in
private def collectAllProgress : CommandElabM (ProgressStats × Array (Name × ProgressStats)) := do
  let env ← getEnv
  let opts ← getOptions
  let mut aggregate := ProgressStats.empty
  let mut byModule : Array (Name × ProgressStats) := #[]
  for mod in env.allImportedModuleNames do
    if let some modIdx := env.getModuleIdx? mod then
      let nodes := (getModuleBlueprintNodes env opts modIdx).map (·.2)
      let modStats ← liftCoreM (computeProgress nodes)
      aggregate := aggregate.merge modStats
      byModule := byModule.push (mod, modStats)
  let currentNodes := (getLocalBlueprintNodes env opts).map (·.2)
  let currentStats ← liftCoreM (computeProgress currentNodes)
  aggregate := aggregate.merge currentStats
  byModule := byModule.push (← liftCoreM getMainModule, currentStats)
  return (aggregate, byModule)

open Elab Command in
private def collectLocalProgress : CommandElabM (ProgressStats × Array (Name × ProgressStats)) := do
  let env ← getEnv
  let opts ← getOptions
  let nodes := (getLocalBlueprintNodes env opts).map (·.2)
  let stats ← liftCoreM (computeProgress nodes)
  let modName ← liftCoreM getMainModule
  return (stats, #[(modName, stats)])

open Elab Command in
@[command_elab blueprint_progress] def elabBlueprintProgress : CommandElab
  | `(command| #blueprint_progress $[$opts:blueprintProgressOpt]*) => do
    let optStrs := opts.map (·.raw.getSubstring?.get!.toString.trimAscii.toString)
    let isLocal := optStrs.contains "local"
    let noBreakdown := optStrs.contains "nobreakdown"
    let (aggregate, byModule) ← if isLocal then collectLocalProgress else collectAllProgress
    if noBreakdown then
      logInfo m!"{aggregate}"
    else
      let report : ProgressReport := { aggregate, byModule }
      logInfo m!"{report}"
  | _ => throwUnsupportedSyntax

end Progress

section Shared
open Lean

/-- Classification of a single blueprint node's formalization status. -/
inductive NodeStatus where
  | formalized | incomplete | notReady

instance : ToString NodeStatus where
  toString
    | .formalized => "Formalized"
    | .incomplete => "Incomplete"
    | .notReady => "Not ready"

/-- A blueprint node entry with status and dependency completion data.
Used uniformly for blocking deps, reverse deps, unblocked nodes, and incomplete nodes. -/
structure NodeEntry where
  name : Name
  status : NodeStatus
  depDone : Nat
  depTotal : Nat
  module : Name

/-- Compute the percentage of formalized deps, rounding to nearest. -/
private def depPct (done total : Nat) : Nat :=
  if total == 0 then 100 else (done * 100 + total / 2) / total

/-- Column widths for aligned dep-fraction formatting. -/
structure DepFracWidths where
  dw : Nat  -- max width of numerator
  tw : Nat  -- max width of denominator
  pw : Nat  -- max width of percentage

/-- Compute dep-fraction column widths from an array of `NodeEntry`. -/
def DepFracWidths.compute (entries : Array NodeEntry) : DepFracWidths where
  dw := entries.foldl (fun acc e => max acc s!"{e.depDone}".length) 0
  tw := entries.foldl (fun acc e => max acc s!"{e.depTotal}".length) 0
  pw := entries.foldl (fun acc e => max acc s!"{depPct e.depDone e.depTotal}".length) 0

/-- Format a dependency fraction with aligned `/` and `%` columns. -/
def fmtDepFrac (done total : Nat) (w : DepFracWidths) : String :=
  let pct := depPct done total
  let dp := "".pushn ' ' (w.dw - s!"{done}".length)
  let tp := "".pushn ' ' (w.tw - s!"{total}".length)
  let pp := "".pushn ' ' (w.pw - s!"{pct}".length)
  s!"{dp}{done}/{tp}{total}  {pp}({pct}%)"

/-- Format a list of `NodeEntry` as aligned rows: `name  frac  status  module` (for CLI). -/
private def fmtNodeEntryList (entries : Array NodeEntry) : String :=
  let maxNameWidth := entries.foldl (fun acc e => max acc (toString e.name).length) 0
  let statusWidth := entries.foldl (fun acc e => max acc (toString e.status).length) 0
  let fw := DepFracWidths.compute entries
  let lines := entries.map fun e =>
    let nameStr := toString e.name
    let namePad := "".pushn ' ' (maxNameWidth - nameStr.length)
    let statusStr := toString e.status
    let statusPad := "".pushn ' ' (statusWidth - statusStr.length)
    s!"  {nameStr}{namePad}  {fmtDepFrac e.depDone e.depTotal fw}  {statusStr}{statusPad}  {e.module}"
  "\n".intercalate lines.toList

/-- Format a list of `NodeEntry` as aligned `MessageData` rows: `name  frac  status` (for interactive). -/
def fmtNodeEntryListMsg (entries : Array NodeEntry) (header : MessageData) : MessageData :=
  let maxNameWidth := entries.foldl (fun acc e => max acc (toString e.name).length) 0
  let fw := DepFracWidths.compute entries
  entries.foldl (init := header) fun acc e =>
    let namePad := "".pushn ' ' (maxNameWidth - (toString e.name).length)
    acc ++ m!"\n  {Expr.const e.name []}{namePad}  {fmtDepFrac e.depDone e.depTotal fw}  {e.status}"

/-- Look up the module a constant was defined in.
Falls back to `env.header.mainModule` for constants defined in the current file. -/
private def getModuleOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some idx => env.allImportedModuleNames[idx.toNat]!
  | none => env.header.mainModule

end Shared

section Status

variable {m} [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m]

/-- Classify a single blueprint node as formalized, incomplete, or not ready. -/
def classifyNode (node : Node) : m NodeStatus := do
  if node.notReady then return .notReady
  if ← node.isLeanOk then return .formalized
  return .incomplete

/-- Status report for a specific blueprint node and its dependency subtree. -/
structure StatusReport where
  name : Name
  selfStatus : NodeStatus
  depStats : ProgressStats
  blocking : Array NodeEntry

def formatStatusReport (r : StatusReport) : String :=
  let header := s!"{r.name}\nStatus: {r.selfStatus}"
  if r.depStats.total == 0 then
    header ++ "\n\nNo dependencies."
  else
    let s := r.depStats
    let round (n : Nat) : Nat :=
      if s.total == 0 then 0 else (n * 100 + s.total / 2) / s.total
    let p1 := round s.sorryFree
    let p2 := round s.containsSorry
    let p3 := if s.total == 0 then 0 else 100 - p1 - p2
    let tw := s!"{s.total}".length
    let pad (n : Nat) := "".pushn ' ' (tw - s!"{n}".length)
    let ppad (p : Nat) := "".pushn ' ' (3 - s!"{p}".length)
    let depSection := s!"\n\nDependencies ({s.total} nodes):"
      ++ s!"\n  Formalized:   {pad s.sorryFree}{s.sorryFree}/{s.total} {ppad p1}({p1}%)"
      ++ s!"\n  Incomplete:   {pad s.containsSorry}{s.containsSorry}/{s.total} {ppad p2}({p2}%)"
      ++ s!"\n  Not ready:    {pad s.notReady}{s.notReady}/{s.total} {ppad p3}({p3}%)"
    let blockingSection :=
      if r.blocking.isEmpty then ""
      else
        fmtNodeEntryList r.blocking
        |> "\n\nBlocking ({r.blocking.size} nodes):\n".append
    header ++ depSection ++ blockingSection

instance : ToString StatusReport where
  toString := formatStatusReport

open Lean in
instance : ToMessageData StatusReport where
  toMessageData r :=
    let nameMsg := m!"{Expr.const r.name []}"
    let header := m!"{nameMsg}\nStatus: {r.selfStatus}"
    if r.depStats.total == 0 then
      header ++ m!"\n\nNo dependencies."
    else
      let s := r.depStats
      let round (n : Nat) : Nat :=
        if s.total == 0 then 0 else (n * 100 + s.total / 2) / s.total
      let p1 := round s.sorryFree
      let p2 := round s.containsSorry
      let p3 := if s.total == 0 then 0 else 100 - p1 - p2
      let tw := s!"{s.total}".length
      let pad (n : Nat) := "".pushn ' ' (tw - s!"{n}".length)
      let ppad (p : Nat) := "".pushn ' ' (3 - s!"{p}".length)
      let depSection := m!"\n\nDependencies ({s.total} nodes):"
        ++ m!"\n  Formalized:   {pad s.sorryFree}{s.sorryFree}/{s.total} {ppad p1}({p1}%)"
        ++ m!"\n  Incomplete:   {pad s.containsSorry}{s.containsSorry}/{s.total} {ppad p2}({p2}%)"
        ++ m!"\n  Not ready:    {pad s.notReady}{s.notReady}/{s.total} {ppad p3}({p3}%)"
      let blockingSection :=
        if r.blocking.isEmpty then m!""
        else fmtNodeEntryListMsg r.blocking m!"\n\nBlocking ({r.blocking.size} nodes):"
      header ++ depSection ++ blockingSection

/-- Collect explicit uses from a NodePart, resolving both name-based and label-based references. -/
private def collectExplicitUses (env : Environment) (part : NodePart) : NameSet :=
  let excludeNames := part.excludes.foldl (·.insert ·) NameSet.empty
  let names := part.uses.foldl (·.insert ·) NameSet.empty |>.filter (!excludeNames.contains ·)
  -- Resolve usesLabels to names
  let labelNames := part.usesLabels.foldl (init := NameSet.empty) fun acc label =>
    (getLeanNamesOfLatexLabel env label).foldl (·.insert ·) acc
  -- Resolve excludesLabels to names and filter
  let excludeLabelNames := part.excludesLabels.foldl (init := NameSet.empty) fun acc label =>
    (getLeanNamesOfLatexLabel env label).foldl (·.insert ·) acc
  let labelNames := labelNames.filter (!excludeLabelNames.contains ·)
  names.union labelNames

/-- Collect all blueprint dependencies of a node (both formalized and non-formalized). -/
private def collectAllBlueprintDeps (name : Name) : m NameSet := do
  let env ← getEnv
  let opts ← getOptions
  let some node := findBlueprintNode? env opts name
    | throwError "no @[blueprint] node with name {name}"
  let (typeUsed, valueUsed) ← collectUsed name
  let mut allUsed := typeUsed.union valueUsed |>.erase ``sorryAx
  allUsed := (collectExplicitUses env node.statement).foldl (·.insert ·) allUsed
  if let some proof := node.proof then
    allUsed := (collectExplicitUses env proof).foldl (·.insert ·) allUsed
  allUsed := allUsed.erase name
  return allUsed.filter fun n => isBlueprintNode env opts n

/-- Compute the formalization status of a specific blueprint node and its dependency subtree. -/
def computeStatus (name : Name) : m StatusReport := do
  let env ← getEnv
  let opts ← getOptions
  let some node := findBlueprintNode? env opts name
    | throwError "no @[blueprint] node with name {name}"
  let selfStatus ← classifyNode node
  -- Collect all blueprint dependencies
  let allDeps ← collectAllBlueprintDeps name
  let depNodes := allDeps.toArray.filterMap fun n => findBlueprintNode? env opts n
  let depStats ← computeProgress depNodes
  -- Collect blocking (non-formalized) dependencies
  let mut blocking : Array NodeEntry := #[]
  for node in depNodes do
    let status ← classifyNode node
    unless status matches .formalized do
      let bDeps := (← collectAllBlueprintDeps node.name).toArray.filterMap fun n =>
        findBlueprintNode? env opts n
      let bStats ← computeProgress bDeps
      blocking := blocking.push {
        name := node.name, status
        depDone := bStats.sorryFree, depTotal := bStats.total
        module := getModuleOf env node.name
      }
  -- Sort blocking: notReady first, then incomplete, alphabetical within each
  let sortedBlocking := blocking.qsort fun a b =>
    match a.status, b.status with
    | .notReady, .incomplete => true
    | .incomplete, .notReady => false
    | _, _ => a.name.toString < b.name.toString
  return { name, selfStatus, depStats, blocking := sortedBlocking }

/-- Shows formalization status of a specific blueprint node and its dependency subtree.
- `#blueprint_status name` shows the status of `name` and its transitive dependencies. -/
syntax (name := blueprint_status) "#blueprint_status" ppSpace ident : command

open Elab Command in
@[command_elab blueprint_status] def elabBlueprintStatus : CommandElab
  | `(command| #blueprint_status $id) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let env ← getEnv
    let opts ← getOptions
    unless isBlueprintNode env opts name do
      throwError "'{name}' is not a @[blueprint] node"
    let report ← liftCoreM (computeStatus name)
    logInfo m!"{report}"
  | _ => throwUnsupportedSyntax

end Status

section Next

variable {m} [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m]

/-- Report listing all incomplete blueprint nodes. -/
structure IncompleteReport where
  nodes : Array NodeEntry

instance : ToString IncompleteReport where
  toString r :=
    if r.nodes.isEmpty then "No incomplete nodes."
    else
      let maxNameWidth := r.nodes.foldl (fun acc n => max acc (toString n.name).length) 0
      let fw := DepFracWidths.compute r.nodes
      let lines := r.nodes.map fun node =>
        let nameStr := toString node.name
        let pad := "".pushn ' ' (maxNameWidth - nameStr.length)
        s!"  {nameStr}{pad}  {fmtDepFrac node.depDone node.depTotal fw}  {node.module}"
      s!"Incomplete ({r.nodes.size} nodes):\n" ++ "\n".intercalate lines.toList

open Lean in
instance : ToMessageData IncompleteReport where
  toMessageData r :=
    if r.nodes.isEmpty then m!"No incomplete nodes."
    else
      let maxNameWidth := r.nodes.foldl (fun acc n => max acc (toString n.name).length) 0
      let fw := DepFracWidths.compute r.nodes
      r.nodes.foldl (init := m!"Incomplete ({r.nodes.size} nodes):") fun acc node =>
        let pad := "".pushn ' ' (maxNameWidth - (toString node.name).length)
        acc ++ m!"\n  {Expr.const node.name []}{pad}  {fmtDepFrac node.depDone node.depTotal fw}"

/-- Collect all incomplete blueprint nodes with their dependency completion fraction. -/
def collectIncomplete (moduleNodes : Array (Name × Array Node)) : m IncompleteReport := do
  let env ← getEnv
  let mut result : Array NodeEntry := #[]
  for (mod, nodes) in moduleNodes do
    for node in nodes do
      if node.notReady then continue
      unless env.contains node.name do continue
      let status ← classifyNode node
      if status matches .formalized then continue
      let report ← computeStatus node.name
      let depDone := report.depStats.sorryFree
      let depTotal := report.depStats.total
      result := result.push { name := node.name, status, module := mod, depDone, depTotal }
  -- Sort by percentage descending (most ready first), then by name
  let sortedNodes := result.qsort fun a b =>
    let aPct := depPct a.depDone a.depTotal
    let bPct := depPct b.depDone b.depTotal
    if aPct != bPct then aPct > bPct
    else a.name.toString < b.name.toString
  return { nodes := sortedNodes }

/-- Shows incomplete blueprint nodes sorted by dependency completion.
- `#blueprint_incomplete` shows incomplete nodes across all modules.
- `#blueprint_incomplete local` shows incomplete nodes in the current module only. -/
declare_syntax_cat blueprintIncompleteOpt
syntax &"local" : blueprintIncompleteOpt
syntax (name := blueprint_incomplete) "#blueprint_incomplete" (ppSpace blueprintIncompleteOpt)* : command

open Elab Command in
private def collectAllModuleNodes : CommandElabM (Array (Name × Array Node)) := do
  let env ← getEnv
  let opts ← getOptions
  let mut result : Array (Name × Array Node) := #[]
  for mod in env.allImportedModuleNames do
    if let some modIdx := env.getModuleIdx? mod then
      let nodes := (getModuleBlueprintNodes env opts modIdx).map (·.2)
      result := result.push (mod, nodes)
  let currentNodes := (getLocalBlueprintNodes env opts).map (·.2)
  result := result.push (← liftCoreM getMainModule, currentNodes)
  return result

open Elab Command in
private def collectLocalModuleNodes : CommandElabM (Array (Name × Array Node)) := do
  let env ← getEnv
  let opts ← getOptions
  let nodes := (getLocalBlueprintNodes env opts).map (·.2)
  let modName ← liftCoreM getMainModule
  return #[(modName, nodes)]

open Elab Command in
@[command_elab blueprint_incomplete] def elabBlueprintIncomplete : CommandElab
  | `(command| #blueprint_incomplete $[$opts:blueprintIncompleteOpt]*) => do
    let optStrs := opts.map (·.raw.getSubstring?.get!.toString.trimAscii.toString)
    let isLocal := optStrs.contains "local"
    let moduleNodes ← if isLocal then collectLocalModuleNodes else collectAllModuleNodes
    let report ← liftCoreM (collectIncomplete moduleNodes)
    logInfo m!"{report}"
  | _ => throwUnsupportedSyntax

end Next

section Impact

variable {m} [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m]

/-- Impact report: reverse dependencies and nodes that would be unblocked. -/
structure ImpactReport where
  name : Name
  selfStatus : NodeStatus
  reverseDeps : Array NodeEntry
  wouldUnblock : Array NodeEntry

def formatImpactReport (r : ImpactReport) : String :=
  let header := s!"{r.name}\nStatus: {r.selfStatus}"
  let revSection :=
    if r.reverseDeps.isEmpty then "\n\nNo nodes depend on this."
    else
      fmtNodeEntryList r.reverseDeps
      |> "\n\nDepended on by ({r.reverseDeps.size} nodes):\n".append
  let unblockSection :=
    if r.wouldUnblock.isEmpty then ""
    else
      fmtNodeEntryList r.wouldUnblock
      |> "\n\nWould unblock ({r.wouldUnblock.size} nodes):\n".append
  header ++ revSection ++ unblockSection

instance : ToString ImpactReport where
  toString := formatImpactReport

open Lean in
instance : ToMessageData ImpactReport where
  toMessageData r :=
    let header := m!"{Expr.const r.name []}\nStatus: {r.selfStatus}"
    let revSection :=
      if r.reverseDeps.isEmpty then m!"\n\nNo nodes depend on this."
      else
        fmtNodeEntryListMsg r.reverseDeps
          m!"\n\nDepended on by ({r.reverseDeps.size} nodes):"
    let unblockSection :=
      if r.wouldUnblock.isEmpty then m!""
      else
        fmtNodeEntryListMsg r.wouldUnblock
          m!"\n\nWould unblock ({r.wouldUnblock.size} nodes):"
    header ++ revSection ++ unblockSection

/-- Compute the impact of formalizing a specific blueprint node: which nodes depend on it
and which would become actionable. -/
def computeImpact (targetName : Name) (moduleNodes : Array (Name × Array Node)) : m ImpactReport := do
  let env ← getEnv
  let opts ← getOptions
  let some targetNode := findBlueprintNode? env opts targetName
    | throwError "no @[blueprint] node with name {targetName}"
  let selfStatus ← classifyNode targetNode
  let mut reverseDeps : Array NodeEntry := #[]
  let mut wouldUnblock : Array NodeEntry := #[]
  for (mod, nodes) in moduleNodes do
    for node in nodes do
      if node.name == targetName then continue
      unless env.contains node.name do continue
      -- Check if targetName is among ALL blueprint dependencies (not just blocking)
      let deps ← collectAllBlueprintDeps node.name
      unless deps.contains targetName do continue
      let status ← classifyNode node
      let report ← computeStatus node.name
      let depDone := report.depStats.sorryFree
      let depTotal := report.depStats.total
      reverseDeps := reverseDeps.push { name := node.name, status, depDone, depTotal, module := mod }
      -- Would unblock: incomplete node whose only blocking dep is the target
      if status matches .incomplete then
        if report.blocking.size == 1 && report.blocking.back?.any (·.name == targetName) then
          wouldUnblock := wouldUnblock.push { name := node.name, status, depDone, depTotal, module := mod }
  -- Sort reverse deps: notReady first, then incomplete, alphabetical within each
  let sortedRevDeps := reverseDeps.qsort fun a b =>
    match a.status, b.status with
    | .notReady, NodeStatus.incomplete => true
    | NodeStatus.incomplete, .notReady => false
    | _, _ => a.name.toString < b.name.toString
  -- Sort would-unblock alphabetically
  let sortedUnblock := wouldUnblock.qsort fun a b => a.name.toString < b.name.toString
  return { name := targetName, selfStatus, reverseDeps := sortedRevDeps, wouldUnblock := sortedUnblock }

/-- Shows the impact of formalizing a specific blueprint node: which nodes depend on it
and which would become actionable.
- `#blueprint_impact name` searches all imported modules.
- `#blueprint_impact name local` searches only the current module. -/
declare_syntax_cat blueprintImpactOpt
syntax &"local" : blueprintImpactOpt
syntax (name := blueprint_impact) "#blueprint_impact" ppSpace ident (ppSpace blueprintImpactOpt)* : command

open Elab Command in
@[command_elab blueprint_impact] def elabBlueprintImpact : CommandElab
  | `(command| #blueprint_impact $id $[$opts:blueprintImpactOpt]*) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let env ← getEnv
    let leanOpts ← getOptions
    unless isBlueprintNode env leanOpts name do
      throwError "'{name}' is not a @[blueprint] node"
    let optStrs := opts.map (·.raw.getSubstring?.get!.toString.trimAscii.toString)
    let isLocal := optStrs.contains "local"
    let moduleNodes ← if isLocal then collectLocalModuleNodes else collectAllModuleNodes
    let report ← liftCoreM (computeImpact name moduleNodes)
    logInfo m!"{report}"
  | _ => throwUnsupportedSyntax

end Impact

open IO

def moduleToRelPath (module : Name) (ext : String) : System.FilePath :=
  modToFilePath "module" module ext

def libraryToRelPath (library : Name) (ext : String) : System.FilePath :=
  System.mkFilePath ["library", library.toString (escape := false)] |>.addExtension ext

/-- Write `latex` to the appropriate blueprint tex file. Returns the list of paths to auxiliary output files (note: the returned paths are currently discarded). -/
def outputLatexResults (basePath : System.FilePath) (module : Name) (latex : LatexOutput) : IO (Array System.FilePath) := do
  let filePath := basePath / moduleToRelPath module "tex"
  let artifactsDir := basePath / moduleToRelPath module "artifacts"
  if let some d := filePath.parent then FS.createDirAll d
  FS.writeFile filePath (latex.header artifactsDir)

  latex.artifacts.mapM fun art => do
    let path := artifactsDir / (art.id ++ ".tex")
    if let some d := path.parent then FS.createDirAll d
    FS.writeFile path art.content
    return path

/-- Write `json` to the appropriate blueprint json file. -/
def outputJsonResults (basePath : System.FilePath) (module : Name) (json : Json) : IO Unit := do
  let filePath := basePath / moduleToRelPath module "json"
  if let some d := filePath.parent then FS.createDirAll d
  FS.writeFile filePath json.pretty

/-- Write to an appropriate index tex file that \inputs all modules in a library. -/
def outputLibraryLatex (basePath : System.FilePath) (library : Name) (modules : Array Name) : IO Unit := do
  FS.createDirAll basePath
  let latex : Latex := "\n\n".intercalate
    (modules.map fun mod => Latex.input (basePath / moduleToRelPath mod "tex")).toList
  let filePath := basePath / libraryToRelPath library "tex"
  if let some d := filePath.parent then FS.createDirAll d
  FS.writeFile filePath latex

/-- Write to an appropriate index json file containing paths to json files of all modules in a library. -/
def outputLibraryJson (basePath : System.FilePath) (library : Name) (modules : Array Name) : IO Unit := do
  FS.createDirAll basePath
  let json : Json := Json.mkObj [("modules", toJson (modules.map fun mod => moduleToRelPath mod "json"))]
  let content := json.pretty
  let filePath := basePath / libraryToRelPath library "json"
  if let some d := filePath.parent then FS.createDirAll d
  FS.writeFile filePath content

end Architect
