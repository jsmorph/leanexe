import Lean

/-!
Prints, for each constant that each named module declares, the module, the constant's name, and
the hashes (`Expr.hash`) of its type and of its value, 0 for a constant without a value, sorted by
name, and a count per module on standard error.  Two builds whose lines are equal declare the same
constants with the same statements and the same proof terms, up to collisions of the hash.  The
modules must be built, and `LEAN_PATH` must reach their `.olean` files, as `lake env` sets it.
Usage: `lake env lean --run tools/DeclHashes.lean MODULE...`
-/

open Lean

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let mods := args.map String.toName
  let env ← importModules (mods.toArray.map fun m => { module := m }) {}
  for m in mods do
    let some idx := env.getModuleIdx? m | throw <| IO.userError s!"no module {m}"
    let names := env.header.moduleData[idx.toNat]!.constNames
    let mut values := 0
    for n in names.qsort (·.toString < ·.toString) do
      let some c := env.find? n | throw <| IO.userError s!"no constant {n}"
      let v := match c.value? (allowOpaque := true) with
        | some e => e.hash
        | none => 0
      if v != 0 then values := values + 1
      IO.println s!"{m} {n} {c.type.hash} {v}"
    IO.eprintln s!"{m}: {names.size} constants, {values} with values"
