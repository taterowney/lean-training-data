module

public import Lake
public import Lean.Attributes
import Lean

public section

open Lean System Lake



namespace System.FilePath

/--
Return the path of `path` relative to `parent`.
-/
def relativeTo (path parent : FilePath) : Option FilePath :=
  let rec componentsRelativeTo (pathComps parentComps : List String) : Option FilePath :=
    match pathComps, parentComps with
    | _, [] => mkFilePath pathComps
    | [], _ => none
    | (h₁ :: t₁), (h₂ :: t₂) =>
      if h₁ == h₂ then
        componentsRelativeTo t₁ t₂
      else
        none

    componentsRelativeTo path.components parent.components


/--
Convert a relative path to an absolute path.
-/
def toAbsolute (path : FilePath) : IO FilePath := do
  if path.isAbsolute then
    pure path
  else
    let cwd ← IO.currentDir
    pure $ cwd / path

end System.FilePath

/-- Initialize the search path with `Lean.findSysroot`, setting the path correctly for loading modules via metaprogramming, etc. Run this if experiencing errors to the effect of "couldn't find xxx in search paths ..." -/
def initMetaSearchPath := do initSearchPath (← findSysroot)

-- -- TODO allow finding Lean 4 sources from the toolchain.
-- def findLean (mod : Name) : IO FilePath := do
--   return FilePath.mk ((← findOLean mod).toString.replace ".lake/build/lib/lean" "") |>.withExtension "lean"

def packagesDir : FilePath :=
  if Lake.defaultPackagesDir == "packages"  then
    ".lake" / Lake.defaultPackagesDir
  else
    Lake.defaultPackagesDir



/--
Return the *.lean file corresponding to a module name. Credit to LeanDojo.
-/
def findLean' (mod : Name) : IO FilePath := do
  let modStr := mod.toString
  if modStr.startsWith "«lake-packages»." then
    return FilePath.mk (modStr.replace "«lake-packages»" "lake-packages" |>.replace "." "/") |>.withExtension "lean"
  if modStr.startsWith "«.lake»." then
    return FilePath.mk (modStr.replace "«.lake»" ".lake" |>.replace "." "/") |>.withExtension "lean"
  if modStr == "Lake" then
    return packagesDir / "lean4/src/lean/lake/Lake.lean"
  let olean ← findOLean mod
  -- Remove a "build/lib/lean/" substring from the path.
  let lean := olean.toString.replace ".lake/build/lib/lean/" ""
    |>.replace "build/lib/lean/" "" |>.replace "lib/lean/Lake/" "lib/lean/lake/Lake/"
  let mut path := FilePath.mk lean |>.withExtension "lean"
  let leanLib ← getLibDir (← getBuildDir)
  if let some p := path.relativeTo leanLib then
    path := packagesDir / "lean4/src/lean" / p

  let cwd ← IO.currentDir
  if path.isAbsolute then
    match path.relativeTo cwd with
    | some relativePath => path := relativePath
    | none => pure ()

  unless ← path.pathExists do
    throw <| IO.userError s!"Could not find source file for module {mod}, expected at {path}"
  path.toAbsolute


/-- Read the source code of the named module. Implementation of `moduleSource`, which is the cached version of this function. -/
def moduleSource' (mod : Name) : IO String := do
  IO.FS.readFile (← findLean' mod)

initialize sourceCache : IO.Ref <| Std.HashMap Name String ←
  IO.mkRef {}

/-- Read the source code of the named module. The results are cached. -/
def moduleSource (mod : Name) : IO String := do
  let m ← sourceCache.get
  match m[mod]? with
  | some r => return r
  | none => do
    let v ← moduleSource' mod
    sourceCache.set (m.insert mod v)
    return v
