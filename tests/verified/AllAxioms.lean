import Lean

/-!
The axioms of every declaration of the repository.  The check imports the root modules of the
libraries `LeanExe`, `Examples`, `Demos`, `Verified`, `Library`, and `TestSupport`, walks the
constants that the declarations of those modules use, transitively, and fails when the walk
reaches an axiom other than `propext`, `Classical.choice`, and `Quot.sound`, such as `sorryAx`,
`Lean.ofReduceBool`, or an axiom that a file declares.  For each such axiom it prints a chain of
uses from a declaration of the repository to the axiom.  It covers the declarations that no
`#print axioms` names, which the build's audit of the reports does not.
Usage: lake env lean --run tests/verified/AllAxioms.lean
-/

open Lean

def roots : Array Name := #[`LeanExe, `Examples, `Demos, `Verified, `Library, `TestSupport]

def permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- Whether the module `m` belongs to the repository. -/
def ours (m : Name) : Bool := roots.any (·.isPrefixOf m)

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules (roots.map ({ module := · })) {} (trustLevel := 1024)
  let mut parent : Std.HashMap Name Name := {}
  let mut stack : Array Name := #[]
  let mut starts := 0
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if ours env.header.moduleNames[idx.toNat]! then
        stack := stack.push n
        parent := parent.insert n n
        starts := starts + 1
  let mut bad : Array Name := #[]
  let mut visited := 0
  while h : 0 < stack.size do
    let n := stack[stack.size - 1]
    stack := stack.pop
    visited := visited + 1
    match env.find? n with
    | none => pure ()
    | some ci =>
      if let .axiomInfo _ := ci then
        if !permitted.contains n then bad := bad.push n
      for d in ci.getUsedConstants do
        if !parent.contains d then
          parent := parent.insert d n
          stack := stack.push d
  IO.println s!"axioms: {starts} declarations of the repository, {visited} constants reached"
  if bad.isEmpty then
    IO.println "axioms: every declaration uses only propext, Classical.choice, and Quot.sound"
    return 0
  for a in bad do
    let mut chain := #[a]
    let mut c := a
    while parent[c]? != some c do
      c := parent[c]!
      chain := chain.push c
    IO.eprintln s!"fail: the axiom {a} is reached by {" ← ".intercalate (chain.toList.map toString)}"
  return 1
