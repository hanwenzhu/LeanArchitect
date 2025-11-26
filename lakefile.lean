import Lake
open System Lake DSL

package LeanArchitect

lean_lib Architect

@[default_target]
lean_exe extract_blueprint where
  root := `Main
  supportInterpreter := true

/-- Utility script used for converting from existing blueprint format. -/
@[default_target]
lean_exe add_position_info where
  root := `scripts.convert.add_position_info
  supportInterpreter := true

require batteries from git
  "https://github.com/leanprover-community/batteries" @ "v4.25.0"

require Cli from git
  "https://github.com/mhuisi/lean4-cli" @ "v4.25.0"

def buildModuleBlueprint (mod : Module) (ext : String) (extractArgs : Array String) : FetchM (Job Unit) := do
  let exeJob ← extract_blueprint.fetch
  let modJob ← mod.leanArts.fetch
  let buildDir := (← getRootPackage).buildDir
  let mainFile := mod.filePath (buildDir / "blueprint" / "module") ext
  let leanOptions := Lean.toJson mod.leanOptions |>.compress
  exeJob.bindM fun exeFile => do
    modJob.mapM fun _ => do
      -- The output is a main file plus a list of auxiliary files
      buildFileUnlessUpToDate' mainFile do
        proc {
          cmd := exeFile.toString
          args := #["single", "--build", buildDir.toString, "--options", leanOptions, mod.name.toString] ++ extractArgs
          env := ← getAugmentedEnv
        }

/-- A facet to extract the blueprint for a module. -/
module_facet blueprint (mod : Module) : Unit := do
  buildModuleBlueprint mod "tex" #[]

/-- A facet to extract JSON data of blueprint for a module. -/
module_facet blueprintJson (mod : Module) : Unit := do
  buildModuleBlueprint mod "json" #["--json"]

def buildLibraryBlueprint (lib : LeanLib) (moduleFacet : Lean.Name) (ext : String) (extractArgs : Array String) : FetchM (Job Unit) := do
  let mods ← (← lib.modules.fetch).await
  let moduleJobs := Job.collectArray <| ← mods.mapM (fetch <| ·.facet moduleFacet)
  let exeJob ← extract_blueprint.fetch
  let buildDir := (← getRootPackage).buildDir
  let outputFile := buildDir / "blueprint" / "library" / lib.name.toString |>.addExtension ext
  exeJob.bindM fun exeFile => do
    moduleJobs.mapM fun _ => do
      buildFileUnlessUpToDate' outputFile do
        logInfo "Blueprint indexing"
        proc {
          cmd := exeFile.toString
          args := #["index", "--build", buildDir.toString, lib.name.toString, ",".intercalate (mods.map (·.name.toString)).toList] ++ extractArgs
          env := ← getAugmentedEnv
        }

/-- A facet to extract the blueprint for a library. -/
library_facet blueprint (lib : LeanLib) : Unit := do
  buildLibraryBlueprint lib `blueprint "tex" #[]

/-- A facet to extract the JSON data for the blueprint for a library. -/
library_facet blueprintJson (lib : LeanLib) : Unit := do
  buildLibraryBlueprint lib `blueprintJson "json" #["--json"]

/-- A facet to extract the blueprint for each library in a package. -/
package_facet blueprint (pkg : Package) : Unit := do
  let libJobs := Job.collectArray <| ← pkg.leanLibs.mapM (fetch <| ·.facet `blueprint)
  let _ ← libJobs.await
  return .nil

/-- A facet to extract the blueprint JSON data for each library in a package. -/
package_facet blueprintJson (pkg : Package) : Unit := do
  let libJobs := Job.collectArray <| ← pkg.leanLibs.mapM (fetch <| ·.facet `blueprintJson)
  let _ ← libJobs.await
  return .nil

open IO.Process in
/-- Run a command, print all outputs, and throw an error if it fails. -/
private def runCmd (cmd : String) (args : Array String) : ScriptM Unit := do
  let child ← spawn { cmd, args, stdout := .inherit, stderr := .inherit, stdin := .null }
  let exitCode ← child.wait
  if exitCode != 0 then
    throw <| IO.userError s!"Error running command {cmd} {args.toList}"

/-- A script to convert an existing blueprint to LeanArchitect format,
modifying the Lean and LaTeX source files in place. -/
script blueprintConvert (args : List String) do
  let architect ← Architect.get
  let convertScript := architect.srcDir / "scripts" / "convert" / "main.py"
  let libs := (← getRootPackage).leanLibs
  let rootMods := libs.flatMap (·.rootModules)
  if h : rootMods.size = 0 then
    IO.eprintln "No root modules found for any library"
    return 1
  else  -- this else is needed for rootMods[0] to work
  IO.eprintln "Building libraries"
  for lib in libs do
    runCmd (← getLake).toString #["build", lib.name.toString]
  let leanOptions := Lean.toJson (← getRootPackage).leanOptions |>.compress
  IO.eprintln "Calling Python script to convert blueprint to LeanArchitect format"
  runCmd "python3" <|
    #[convertScript.toString] ++
    #["--libraries"] ++ libs.map (·.name.toString) ++
    #["--modules"] ++ rootMods.map (·.name.toString) ++
    #["--root_file", rootMods[0].leanFile.toString] ++
    #["--options", leanOptions] ++
    args
  return 0
