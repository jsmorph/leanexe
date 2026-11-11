import TestSupport.Bare.Ctl
import LeanExe.Native.Bare

/-!
Writes the C text of the controller program around the step `ctlStep` of
`TestSupport.Bare.ctlCompiled`, function 2, translated with one page of `lx_mem`, from the state
0, as `native-bare emit-ctl` writes it (`tests/TestSupport/Bare/Emit.lean`), to `DIR/ctl.c`.
`clightn/check.sh` runs it with `lake env lean --run`.
-/

open LeanExe.Native LClight

def main (args : List String) : IO UInt32 := do
  let dir := args.headD "."
  let some t := translate 1 TestSupport.Bare.ctlCompiled.module
    | IO.eprintln "clightn: the module of ctlStep does not translate"; return 1
  match t.ctlText 2 0 with
  | .error e => IO.eprintln s!"clightn: {e}"; return 1
  | .ok text => IO.FS.writeFile s!"{dir}/ctl.c" text
  return 0
