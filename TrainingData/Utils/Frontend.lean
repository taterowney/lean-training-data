module
/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
public import Lean.Elab.Frontend
public import Lean.Attributes
public import TrainingData.Utils.MLList
public import TrainingData.Utils.FindSource
public import Lake

public section

/-!
# Compiling Lean sources to obtain `Environment`, `Message`s and `InfoTree`s.

The main entry point is

```
def processInput (input : String) (env? : Option Environment := none)
    (opts : Options := {}) (fileName : Option String := none) (info : Bool := true) :
    IO (Environment × List Message × List InfoTree) :=
  ...
```

which attempts to compile Lean source code, returning an `Environment`,
along with any generated `Message`s and `InfoTree`s.

The optional argument `env?` allows specifying an existing `Environment`, for partial compilation.
If this is non-empty, then the source code may not contain any `import` statements.

You may suppress the generation of `InfoTree`s using `info := false`.

For finer-grained control of compilation, we define a `CompilationStep` structure
which contains information about the results of each command.

You can use `processInput'` to obtain a monadic lazy list of `CompilationStep`s.

The functions `compileModule : Name → IO (List CompilationStep)` and
`moduleInfoTrees : Name → IO (List InfoTree)` are useful for compiling single modules from source.
-/

set_option autoImplicit true

open Lean Elab Frontend Meta



private def isInternal' (declName : Name) : Bool :=
  declName.isInternal ||
  match declName with
  | .str _ s => "match_".isPrefixOf s || "proof_".isPrefixOf s
  | _        => true

-- from Lean.Server.Completion
private def isBlackListed {m} [Monad m] [MonadEnv m] (declName : Name) : m Bool := do
  if declName == ``sorryAx then return true
  if declName matches .str _ "inj" then return true
  if declName matches .str _ "noConfusionType" then return true
  let env ← getEnv
  pure $ isInternal' declName
   || isAuxRecursor env declName
   || isNoConfusion env declName
  <||> isRec declName <||> isMatcher declName
namespace Lean.Elab.IO

/--
Results from processing a command.

Contains the `Environment` before and after,
the `src : Substring` and `stx : Syntax` of the command,
and any `Message`s and `InfoTree`s produced while processing.
-/
structure CompilationStep where
  fileName : String
  fileMap : FileMap
  src : Substring.Raw
  stx : Syntax
  before : Environment
  after : Environment
  msgs : List Message
  trees : List InfoTree

namespace CompilationStep

/--
Process one command, returning a `CompilationStep` and
`done : Bool`, indicating whether this was the last command.
-/
def one : FrontendM (CompilationStep × Bool) := do
  let s := (← get).commandState
  let before := s.env
  let done ← processCommand
  let stx := (← get).commands.back!
  let src := Substring.Raw.mk (← read).inputCtx.inputString (← get).cmdPos (← get).parserState.pos
  let s' := (← get).commandState
  let after := s'.env
  -- In Lean 4 v4.28.0+, `elabCommandTopLevel` resets both `messages` and `infoState`
  -- at the start of each command, so these already contain only this command's data.
  let msgs := s'.messages.toList
  let trees := s'.infoState.trees.toList
  let ⟨_, fileName, fileMap, _, _⟩  := (← read).inputCtx
  return ({ fileName, fileMap, src, stx, before, after, msgs, trees }, done)

/-- Process all commands in the input. -/
partial def all : FrontendM (List CompilationStep) := do
  let (cmd, done) ← CompilationStep.one
  if done then
    return [cmd]
  else
    return cmd :: (← all)

def runCoreMBefore (c : CompilationStep) (x : CoreM α) : IO α :=
  (·.1) <$> Core.CoreM.toIO x { fileName := c.fileName, fileMap := c.fileMap } { env := c.before }

open Meta in
def runMetaMBefore (c : CompilationStep) (x : MetaM α) : IO α :=
  c.runCoreMBefore <| MetaM.run' x {} {}

/-- Return all new `ConstantInfo`s added during the processed command. -/
def diff (cmd : CompilationStep) : List ConstantInfo :=
  cmd.after.constants.map₂.toList.filterMap
    fun (c, i) => if cmd.before.constants.map₂.contains c then none else some i

/-- Data extracted from a `ConstantInfo`. -/
structure DeclInfo where
  name : Name
  type : Expr
  ppType : String
  docString : Option String

/-- Return info about each new declaration added during the processed command. -/
def newDecls (cmd : CompilationStep) : IO (List DeclInfo) := do
  cmd.diff.filterMapM fun ci => cmd.runMetaMBefore do
    if ← isBlackListed ci.name then
      pure none
    else pure <| some {
      name := ci.name
      type := ci.type
      ppType := toString (← Meta.ppExpr ci.type)
      docString := ← findDocString? cmd.after ci.name
    }

end CompilationStep

/--
Returns a monadic lazy list of `CompilationStep`s.
This needs to be provided with initial state, see `compilationSteps`.
-/
partial def compilationSteps_aux :  MLList FrontendM CompilationStep :=
  .squash fun _ => aux
where
  /-- Implementation of `compilationSteps_aux`.  -/
  aux := do
    let (cmd, done) ← CompilationStep.one
    if done then
      return .ofList [cmd]
    else
      return .cons cmd (← aux)

/-- Return the the `CompilationStep`s, as a monadic lazy list in `IO`. -/
def compilationSteps (inputCtx : Parser.InputContext) (parserState : Parser.ModuleParserState)
    (commandState : Command.State) : MLList IO CompilationStep :=
  compilationSteps_aux.runReaderT { inputCtx }
    |>.runStateRefT { commandState, parserState, cmdPos := parserState.pos }

/--
Process some text input, with or without an existing environment.
If there is no existing environment, we parse the input for headers (e.g. import statements),
and create a new environment.
Otherwise, we add to the existing environment.
Returns a list containing data about each processed command.

Be aware that Lean does not support compiling multiple files in the same sessions.
Often it works, but if the compiled files do anything complicated with initializers then
nothing is gauranteed.
-/
def processInput' (input : String) (env? : Option Environment := none)
    (opts : Options := {}) (fileName : Option String := none) (info : Bool := true) :
    MLList IO CompilationStep := unsafe do
  let fileName   := fileName.getD "<input>"
  let inputCtx   := Parser.mkInputContext input fileName
  let (parserState, commandState) ← match env? with
  | none => do
    enableInitializersExecution
    let (header, parserState, messages) ← Parser.parseHeader inputCtx
    let (env, messages) ← processHeader header opts messages inputCtx
    pure (parserState, (Command.mkState env messages opts))
  | some env => do
    pure ({ : Parser.ModuleParserState }, Command.mkState env {} opts)
  compilationSteps inputCtx parserState { commandState with infoState.enabled := info }

/--
Process some text input, with or without an existing environment.
If there is no existing environment, we parse the input for headers (e.g. import statements),
and create a new environment.
Otherwise, we add to the existing environment.
Returns the resulting environment, along with a list of messages and info trees.
-/
def processInput (input : String) (env? : Option Environment := none)
    (opts : Options := {}) (fileName : Option String := none) (info : Bool := true) :
    IO (Environment × List Message × List InfoTree) := do
  let steps ← processInput' input env? opts fileName info |>.force
  match steps.getLast? with
  | none => throw <| IO.userError "No commands found in input."
  | some { after, .. } =>
    return (after, steps.flatMap CompilationStep.msgs, steps.flatMap CompilationStep.trees)


/-- Implementation of `compileModule`, which is the cached version of this function. -/
def compileModule' (mod : Name) : MLList IO CompilationStep := do
  Lean.Elab.IO.processInput' (← moduleSource mod) none {} (← findLean' mod).toString

initialize compilationCache : IO.Ref <| Std.HashMap Name (List CompilationStep) ←
  IO.mkRef {}

/--
Compile the source file for the named module, returning the
resulting environment, any generated messages, and all info trees.

The results are cached, although be aware that compiling multiple files in the same session
is unsupported, and may lead to exciting results:
you should check all compiled files for error messages if attempting this.
-/
def compileModule (mod : Name) : IO (List CompilationStep) := do
  let m ← compilationCache.get
  match m[mod]? with
  | some r => return r
  | none => do
    let v ← compileModule' mod |>.force
    compilationCache.set (m.insert mod v)
    return v

/-- Compile the source file for the named module, returning all info trees. -/
def moduleInfoTrees (mod : Name) : IO (List InfoTree) := do
  let steps ← compileModule mod
  return steps.flatMap (fun c => c.trees)

end Lean.Elab.IO

end
