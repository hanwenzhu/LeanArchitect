import Architect
import Lean
import Cli

/-!
This executable extracts the blueprint data from a module, or
collates the blueprint data from multiple modules into a LaTeX file.
-/

open Lean Cli Architect

def outputBaseDir (buildDir : System.FilePath) : System.FilePath :=
  buildDir / "blueprint"

def runSingleCmd (p : Parsed) : IO UInt32 := do
  let buildDir := match p.flag? "build" with
    | some dir => dir.as! String
    | none => ".lake/build"
  let baseDir := outputBaseDir buildDir
  let module := p.positionalArg! "module" |>.as! String |>.toName
  let isJson := p.hasFlag "json"
  let options : LeanOptions ← match p.flag? "options" with
    | some o => IO.ofExcept (Json.parse (o.as! String) >>= fromJson?)
    | none => pure (∅ : LeanOptions)
  if isJson then
    let json ← jsonOfImportModule module options.toOptions
    outputJsonResults baseDir module json
  else
    let latexOutput ← latexOutputOfImportModule module options.toOptions
    discard <| outputLatexResults baseDir module latexOutput
  return 0

def runIndexCmd (p : Parsed) : IO UInt32 := do
  let buildDir := match p.flag? "build" with
    | some dir => dir.as! String
    | none => ".lake/build"
  let baseDir := outputBaseDir buildDir
  let library := p.positionalArg! "library" |>.as! String |>.toName
  let modules := p.positionalArg! "modules" |>.as! (Array String) |>.map (·.toName)
  let isJson := p.hasFlag "json"
  if isJson then
    outputLibraryJson baseDir library modules
  else
    outputLibraryLatex baseDir library modules
  return 0

def runProgressCmd (p : Parsed) : IO UInt32 := do
  let modules := p.variableArgsAs! String |>.map (·.toName)
  let options : LeanOptions ← match p.flag? "options" with
    | some o => IO.ofExcept (Json.parse (o.as! String) >>= fromJson?)
    | none => pure (∅ : LeanOptions)
  let localOnly := p.hasFlag "local"
  let noBreakdown := p.hasFlag "nobreakdown"
  let stats ← progressOfImportModules modules options.toOptions localOnly
  let stats := { stats with showByModule := !noBreakdown }
  IO.println s!"{stats}"
  return 0

def singleCmd := `[Cli|
  single VIA runSingleCmd;
  "Only extract the blueprint for the module it was given, might contain broken \\input{}s unless all blueprint files are extracted."

  FLAGS:
    j, json; "Output JSON instead of LaTeX."
    b, build : String; "Build directory."
    o, options : String; "LeanOptions in JSON to pass to running the module."

  ARGS:
    module : String; "The module to extract the blueprint for."
]

def indexCmd := `[Cli|
  index VIA runIndexCmd;
  "Collates the LaTeX outputs of modules in a library from `single` into a LaTeX file with \\input{}s pointing to the modules."

  FLAGS:
    j, json; "Output JSON instead of LaTeX."
    b, build : String; "Build directory."

  ARGS:
    library : String; "The library to index."
    modules : Array String; "The modules in the library."
]

def progressCmd := `[Cli|
  progress VIA runProgressCmd;
  "Output progress statistics for the blueprint nodes in one or more modules."

  FLAGS:
    l, "local"; "Only count nodes defined in the given modules, excluding imports."
    n, "nobreakdown"; "Hide the per-module breakdown."
    o, options : String; "LeanOptions in JSON to pass to running the modules."

  ARGS:
    ...modules : String; "The modules to compute blueprint progress for."
]

def runStatusCmd (p : Parsed) : IO UInt32 := do
  let modules := p.variableArgsAs! String |>.map (·.toName)
  let name := (p.positionalArg! "name" |>.as! String).toName
  let options : LeanOptions ← match p.flag? "options" with
    | some o => IO.ofExcept (Json.parse (o.as! String) >>= fromJson?)
    | none => pure (∅ : LeanOptions)
  let report ← statusOfImportModules modules name options.toOptions
  IO.println s!"{report}"
  return 0

def statusCmd := `[Cli|
  status VIA runStatusCmd;
  "Show formalization status of a specific blueprint node and its dependency subtree."

  FLAGS:
    o, options : String; "LeanOptions in JSON to pass to running the modules."

  ARGS:
    name : String; "The fully qualified Lean name of the declaration."
    ...modules : String; "The modules to load (the declaration must be reachable from these)."
]

def runIncompleteCmd (p : Parsed) : IO UInt32 := do
  let modules := p.variableArgsAs! String |>.map (·.toName)
  let options : LeanOptions ← match p.flag? "options" with
    | some o => IO.ofExcept (Json.parse (o.as! String) >>= fromJson?)
    | none => pure (∅ : LeanOptions)
  let localOnly := p.hasFlag "local"
  let report ← incompleteOfImportModules modules options.toOptions localOnly
  IO.println s!"{report}"
  return 0

def incompleteCmd := `[Cli|
  incomplete VIA runIncompleteCmd;
  "Show incomplete blueprint nodes sorted by dependency completion."

  FLAGS:
    l, "local"; "Only consider nodes defined in the given modules, excluding imports."
    o, options : String; "LeanOptions in JSON to pass to running the modules."

  ARGS:
    ...modules : String; "The modules to search for incomplete nodes."
]

def runImpactCmd (p : Parsed) : IO UInt32 := do
  let modules := p.variableArgsAs! String |>.map (·.toName)
  let name := (p.positionalArg! "name" |>.as! String).toName
  let options : LeanOptions ← match p.flag? "options" with
    | some o => IO.ofExcept (Json.parse (o.as! String) >>= fromJson?)
    | none => pure (∅ : LeanOptions)
  let localOnly := p.hasFlag "local"
  let report ← impactOfImportModules modules name options.toOptions localOnly
  IO.println s!"{report}"
  return 0

def impactCmd := `[Cli|
  impact VIA runImpactCmd;
  "Show which nodes depend on a given blueprint node and which would be unblocked by formalizing it."

  FLAGS:
    l, "local"; "Only consider nodes defined in the given modules, excluding imports."
    o, options : String; "LeanOptions in JSON to pass to running the modules."

  ARGS:
    name : String; "The fully qualified Lean name of the declaration."
    ...modules : String; "The modules to load (the declaration must be reachable from these)."
]

def blueprintCmd : Cmd := `[Cli|
  "LeanArchitect" NOOP;
  "A blueprint generator for Lean 4."

  SUBCOMMANDS:
    singleCmd;
    indexCmd;
    progressCmd;
    statusCmd;
    incompleteCmd;
    impactCmd
]

def main (args : List String) : IO UInt32 :=
  blueprintCmd.validate args
