module
public import Mathlib.Tactic
public import Lean

public section
open Lean Meta Elab Expr Term Command

open Parser

/-- Turns a single command string into a `Syntax` object if it is syntactically correct. -/
def parseCommand (input : String) (env : Environment) : IO (TSyntax `command) := do
  let p := andthenFn whitespace (categoryParserFnImpl `command)
  let ictx := mkInputContext input "<input>"
  let s := p.run ictx { env, options := {} } (getTokenTable env) (mkParserState input)
  if !s.allErrors.isEmpty then
    throw <| IO.userError (s.toErrorMsg ictx)
  else if ictx.atEnd s.pos then
    return ⟨s.stxStack.back⟩
  else
    throw <| IO.userError ((s.mkError "end of input").toErrorMsg ictx)


/-- Parses a string of multiple commands, returning a list of pairs of the raw command string and its corresponding `Syntax` object. -/
partial def parseCommands (input : String) (env : Environment) (ignoreErrors := false) : IO (List (String × TSyntax `command)) := do
  let p := andthenFn whitespace (categoryParserFnImpl `command)
  let ictx := mkInputContext input "<input>"
  let mut s := mkParserState input
  let mut acc := []
  let mut oldPos := s.pos
  while !ictx.atEnd s.pos do
    s := p.run ictx { env, options := {} } (getTokenTable env) s
    let commandRaw := input.toRawSubstring.extract oldPos s.pos |>.toString
    if !s.allErrors.isEmpty then
      if ignoreErrors then
        break -- Can't continue parsing after an error, so just return what we have so far.
      else
        throw <| IO.userError (s.toErrorMsg ictx)
    else
      acc := (commandRaw, ⟨s.stxStack.back⟩) :: acc
      oldPos := s.pos
  return acc.reverse


/-- This looks so awful but I'm not sure how to make it better -/
def getDeclarationName (stx : TSyntax `command) : Name :=
  match stx with
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? def $name:ident $_* $[: $type]? := $_) => name.getId
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? theorem $name:ident $_* : $_ := $_) => name.getId
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? lemma $name:ident $_* : $_ := $_) => name.getId
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? abbrev $name:ident $_* $[: $type]? := $_) => name.getId
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? axiom $name:ident : $_) => name.getId
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? structure $name:ident $_* := $_) => name.getId
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? inductive $name:ident $_* := $_) => name.getId
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? class $name:ident $_* := $_) => name.getId
  | _ => .anonymous

/-- Return the type ascription (conclusion) of a declaration command, if any. -/
def getDeclarationConclusion (stx : TSyntax `command) : Option (TSyntax `term) :=
  match stx with
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? def $_:ident $_* : $type := $_) => some type
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? theorem $_:ident $_* : $type := $_) => some type
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? lemma $_:ident $_* : $type := $_) => some type
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? abbrev $_:ident $_* : $type := $_) => some type
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? axiom $_:ident : $type) => some type
  | _ => none

/-- Return the right-hand side (body / proof term) of a declaration command, if any. -/
def getDeclarationValue (stx : TSyntax `command) : Option (TSyntax `term) :=
  match stx with
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? def $_:ident $_* $[: $_]? := $value) => some value
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? theorem $_:ident $_* : $_ := $value) => some value
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? lemma $_:ident $_* : $_ := $value) => some value
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? abbrev $_:ident $_* $[: $_]? := $value) => some value
  | _ => none

/-- True iff the declaration's value is a literal `sorry` (term-mode or tactic-mode). -/
def hasValueSorry (stx : TSyntax `command) : Bool :=
  match getDeclarationValue stx with
  | some value => match value with
    | `(sorry) => true
    | `(by sorry) => true
    | _ => false
  | none => false

/-- Pretty-print the explicit binders of a `theorem` command as `name : type` strings. -/
def getExplicitHypothesesRepr (stx : TSyntax `command) : List String := Id.run do
  let hyps ← match stx with
  | `($[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? $[$modifiers]? theorem $_:ident $hyps* : $_ := $_) => pure hyps
  | _ => return []

  let mut result := #[]
  for hyp in hyps do
    if hyp.raw.getKind == ``Term.explicitBinder then
      let binderNames := hyp.raw[1].getArgs.map (fun arg => arg.getId.toString)
      let binderType := hyp.raw[2][1].prettyPrint.pretty'
      result := result ++ (binderNames.map (fun name => name ++ " : " ++ binderType))

  return result.toList

/-- Replace the value of a declaration with `sorry`. -/
def valueToSorryStx (decl : TSyntax `command) : CommandElabM <| TSyntax `command :=
  match decl with
  | `($[$modifiers1]? $[$modifiers2]? $[$modifiers3]? $[$modifiers4]? $[$modifiers5]? $[$modifiers6]? $[$modifiers7]? def $name:ident $params* := $_) => `($[$modifiers1]? $[$modifiers2]? $[$modifiers3]? $[$modifiers4]? $[$modifiers5]? $[$modifiers6]? $[$modifiers7]? def $name $params* := sorry)
  | `($[$modifiers1]? $[$modifiers2]? $[$modifiers3]? $[$modifiers4]? $[$modifiers5]? $[$modifiers6]? $[$modifiers7]? def $name:ident $params* : $type := $_) => `($[$modifiers1]? $[$modifiers2]? $[$modifiers3]? $[$modifiers4]? $[$modifiers5]? $[$modifiers6]? $[$modifiers7]? def $name $params* : $type := sorry)
  | `($[$modifiers1]? $[$modifiers2]? $[$modifiers3]? $[$modifiers4]? $[$modifiers5]? $[$modifiers6]? $[$modifiers7]? theorem $name:ident $params* : $type := $value) => `($[$modifiers1]? $[$modifiers2]? $[$modifiers3]? $[$modifiers4]? $[$modifiers5]? $[$modifiers6]? $[$modifiers7]? theorem $name $params* : $type := sorry)
  | `($[$modifiers1]? $[$modifiers2]? $[$modifiers3]? $[$modifiers4]? $[$modifiers5]? $[$modifiers6]? $[$modifiers7]? lemma $name:ident $params* : $type := $value) => `($[$modifiers1]? $[$modifiers2]? $[$modifiers3]? $[$modifiers4]? $[$modifiers5]? $[$modifiers6]? $[$modifiers7]? lemma $name $params* : $type := sorry)
  | `($[$modifiers1]? $[$modifiers2]? $[$modifiers3]? $[$modifiers4]? $[$modifiers5]? $[$modifiers6]? $[$modifiers7]? abbrev $name:ident $params* := $_) => `($[$modifiers1]? $[$modifiers2]? $[$modifiers3]? $[$modifiers4]? $[$modifiers5]? $[$modifiers6]? $[$modifiers7]? abbrev $name $params* := sorry)
  | `($[$modifiers1]? $[$modifiers2]? $[$modifiers3]? $[$modifiers4]? $[$modifiers5]? $[$modifiers6]? $[$modifiers7]? abbrev $name:ident $params* : $type := $value) => `($[$modifiers1]? $[$modifiers2]? $[$modifiers3]? $[$modifiers4]? $[$modifiers5]? $[$modifiers6]? $[$modifiers7]? abbrev $name $params* : $type := sorry)
  | _ => pure decl

/-- Replace the value of a declaration with `sorry`. -/
def valueToSorry (command : String) : CommandElabM String := do
  let stx ← parseCommand command (← getEnv)
  let stxSorry ← valueToSorryStx stx
  pure stxSorry.raw.prettyPrint.pretty'


/-- Parses a string containing one or more Lean declarations (theorems, defs, etc.) without actually elaborating (running) them.

For each declaration, returns a tuple of the declaration's raw code, name, hypotheses, conclusion, value, and whether its value is a sorry. -/
def parseDeclarations (commands : String) : CommandElabM <| Array (String × String × Array String × String × String × Bool) := do
  let cmds := (← parseCommands commands (← getEnv) (ignoreErrors := true)).toArray

  cmds.mapM fun (cmdRaw, cmdStx) => do
    let name := getDeclarationName cmdStx
    let conclusion := getDeclarationConclusion cmdStx
    let value := getDeclarationValue cmdStx
    let isSorry := hasValueSorry cmdStx
    let hypsRepr := getExplicitHypothesesRepr cmdStx |>.toArray
    pure (cmdRaw, name.toString, hypsRepr, conclusion.bind (fun stx => some stx.raw.prettyPrint.pretty') |>.getD "", value.bind (fun stx => some stx.raw.prettyPrint.pretty') |>.getD "", isSorry)



end
