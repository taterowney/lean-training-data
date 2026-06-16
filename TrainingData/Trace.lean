module

public import TrainingData.Utils.Frontend
public import TrainingData.Environment.CacheImports
public import TrainingData.InfoTree.Basic
public import TrainingData.Normalize
public import Cli
public import TrainingData.Utils.MLList
public import TrainingData.Utils.Dependencies


public section

open Lean IO System Lean.Elab.IO


/-- Recursively traces the modules starting from a root module, optionally skipping meta modules. -/
unsafe def traceProject (root : Name) (skipMeta := true)
  (predicate : Name → Bool := fun n => root.getRoot.isPrefixOf n && (!skipMeta || (!n.components.contains `Tactic && !n.components.contains `Lean && !n.components.contains `Std && !n.components.contains `Util))) :
  IO $ MLList IO (Name × MLList IO CompilationStep) := do
  enableInitializersExecution
  initMetaSearchPath

  let out := MLList.ofArray (m := IO) (← collectDependenciesInProject root predicate) |>.mapM
    fun (root, imports, src) => do
      enableInitializersExecution
      let env ← importModules' imports {} (loadExts := true) (level := OLeanLevel.exported)
      let src := removeHeader (← src)
      return (root, processInput' src env (fileName := root.toString))
  pure out

unsafe def traceModules (mods : Array Name) :
  IO $ MLList IO (Name × MLList IO CompilationStep) := do
  enableInitializersExecution
  initMetaSearchPath

  let out := MLList.ofArray (m := IO) (← mods.mapM collectModuleParsed) |>.mapM
    fun (root, imports, src) => do
      enableInitializersExecution
      let env ← importModules' imports {} (loadExts := true) (level := OLeanLevel.exported)
      let src := removeHeader (← src)
      return (root, processInput' src env (fileName := root.toString))
  pure out
