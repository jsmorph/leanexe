import Lean

/-! Use Lean's ordinary command elaborator and kernel, with import-environment
leaking disabled. The pinned release's mark-persistent optimization crashes on
the large compiler-proof import graph in this environment. -/
open Lean

unsafe def main (args : List String) : IO UInt32 := do
  let [source, output] := args | throw (IO.userError "usage: Check.lean source.lean output.olean")
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile source
  let ctx := Parser.mkInputContext input source
  let (header, parserState, messages) ← Parser.parseHeader ctx
  let name := (System.FilePath.mk source).fileStem.getD "CheckedArtifact" |>.toName
  let opts := ({} : Options).set `maxHeartbeats (4000000 : Nat) |>.set `maxRecDepth (4096 : Nat)
    |>.set `Elab.async false
  let stderr ← IO.getStderr
  stderr.putStrLn s!"check: importing {name}"
  let (env, messages) ← Elab.processHeader header opts messages ctx (leakEnv := false) (mainModule := name)
  stderr.putStrLn s!"check: elaborating {name}"
  let state ← Elab.IO.processCommands ctx parserState (Elab.Command.mkState env messages opts)
  for message in state.commandState.messages.toList do
    IO.println (← message.toString)
  if state.commandState.messages.hasErrors then return 1
  stderr.putStrLn s!"check: writing {name}"
  writeModule state.commandState.env output
  return 0
