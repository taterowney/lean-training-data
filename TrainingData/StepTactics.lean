import TrainingData.Frontend
import TrainingData.InfoTree.Basic
import TrainingData.Trace
import TrainingData.Normalize
import Cli

open Lean IO System Lean.Elab.IO

def printAndFlush (s : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn s
  out.flush


namespace Lean.Elab.IO

unsafe def traceTacticInfos (root : Name) : IO UInt32 := do
  initSearchPath (← findSysroot)
  IO.eprintln s!"[step_tactics] collecting dependencies for {root}..."
  (← IO.getStderr).flush
  let mods ← traceModules root
  IO.eprintln s!"[step_tactics] processing modules..."
  (← IO.getStderr).flush
  for (mod, steps) in mods do
    IO.eprintln s!"[step_tactics] module {mod}"
    (← IO.getStderr).flush
    for step in steps do
      for tree in step.trees do
        for (ti, ctx) in tree.tactics do
          try
            let (context, goal_before, goal_after) ← ti.pretty' ctx
            let tactic := (← ti.pp ctx).pretty (width := 100000000)
            let kind := (ti.name?.getD .anonymous).toString
            let out := Json.mkObj [
              ("module", mod.toString),
              ("declaration", ctx.parentDecl?.getD .anonymous |>.toString),
              ("tactic", tactic),
              ("tactic_kind", kind),
              ("context", context.toJson),
              ("goal_before", goal_before),
              ("goal_after", goal_after)
            ]
            printAndFlush out.compress
          catch _ => continue
  return 0

end Lean.Elab.IO

open Cli

unsafe def stepTacticsMain (p : Parsed) : IO UInt32 := do
  let root := p.positionalArg? "module" |>.map (·.as! String) |>.getD "Mathlib"
  Lean.Elab.IO.traceTacticInfos root.toName

unsafe def mainCmd : Cmd := `[Cli|
  "step_tactics" VIA stepTacticsMain;
  "Emit per-tactic training data (context, goal before/after, tactic text) as JSON lines."

  ARGS:
    ...module : String; "Root module to trace (default: Mathlib)."
]

/-- `lake exe step_tactics` -/
def main (args : List String) : IO UInt32 :=
  unsafe mainCmd.validate args
