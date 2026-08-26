module

public import Architect.Output

public meta section

namespace Architect

/-!
Loading the analysis result of a module.
-/

open Lean

/-- This is copied from `DocGen4.envOfImports`. -/
def envOfImports (imports : Array Name) : IO Environment := do
  -- needed for modules which use syntax registered with `initialize add_parser_alias ..`
  unsafe Lean.enableInitializersExecution
  importModules (imports.map (Import.mk · false true false)) Options.empty (leakEnv := true) (loadExts := true)

/-- This is copied from `DocGen4.load`, except for separate handling of `options`. -/
def runEnvOfImports (imports : Array Name) (options : Options) (x : CoreM α) : IO α := do
  initSearchPath (← findSysroot)
  let env ← envOfImports imports
  let config := {
    maxHeartbeats := 100000000,
    options := options
      |>.set `debug.skipKernelTC true
      |>.set `Elab.async false,
    fileName := default,
    fileMap := default,
  }

  Prod.fst <$> x.toIO config { env }

/-- Outputs the blueprint of a module. -/
def latexOutputOfImportModule (module : Name) (options : Options) : IO LatexOutput :=
  runEnvOfImports #[module] options (moduleToLatexOutput module)

/-- Outputs the JSON data for the blueprint of a module. -/
def jsonOfImportModule (module : Name) (options : Options) : IO Json :=
  runEnvOfImports #[module] options (moduleToJson module)

/-- Computes blueprint progress report across modules.
If `localOnly` is true, only counts nodes defined in the given modules.
Otherwise, also includes nodes from all their imports. -/
def progressOfImportModules (modules : Array Name) (options : Options) (localOnly : Bool := false) : IO ProgressReport :=
  runEnvOfImports modules options do
    let env ← getEnv
    let opts ← getOptions
    let mut aggregate := ProgressStats.empty
    let mut byModule : Array (Name × ProgressStats) := #[]
    let targetModules := if localOnly then modules
      else env.allImportedModuleNames
    for mod in targetModules do
      if let some modIdx := env.getModuleIdx? mod then
        let nodes := (getModuleBlueprintNodes env opts modIdx).map (·.2)
        let modStats ← computeProgress nodes
        aggregate := aggregate.merge modStats
        byModule := byModule.push (mod, modStats)
    return { aggregate, byModule }

/-- Computes the status of a specific blueprint node and its dependency subtree. -/
def statusOfImportModules (modules : Array Name) (constName : Name) (options : Options) : IO StatusReport :=
  runEnvOfImports modules options (computeStatus constName)

/-- Computes incomplete blueprint nodes across modules.
If `localOnly` is true, only considers nodes defined in the given modules. -/
def incompleteOfImportModules (modules : Array Name) (options : Options) (localOnly : Bool := false) : IO IncompleteReport :=
  runEnvOfImports modules options do
    let env ← getEnv
    let opts ← getOptions
    let mut moduleNodes : Array (Name × Array Node) := #[]
    let targetModules := if localOnly then modules else env.allImportedModuleNames
    for mod in targetModules do
      if let some modIdx := env.getModuleIdx? mod then
        let nodes := (getModuleBlueprintNodes env opts modIdx).map (·.2)
        moduleNodes := moduleNodes.push (mod, nodes)
    collectIncomplete moduleNodes

/-- Computes the impact of formalizing a specific blueprint node across modules.
If `localOnly` is true, only considers nodes defined in the given modules. -/
def impactOfImportModules (modules : Array Name) (constName : Name) (options : Options) (localOnly : Bool := false) : IO ImpactReport :=
  runEnvOfImports modules options do
    let env ← getEnv
    let opts ← getOptions
    let mut moduleNodes : Array (Name × Array Node) := #[]
    let targetModules := if localOnly then modules else env.allImportedModuleNames
    for mod in targetModules do
      if let some modIdx := env.getModuleIdx? mod then
        let nodes := (getModuleBlueprintNodes env opts modIdx).map (·.2)
        moduleNodes := moduleNodes.push (mod, nodes)
    computeImpact constName moduleNodes

end Architect
