import Demos.RunningSum.Stream

def main : IO UInt32 := do
  match ← Demos.RunningSum.process.runStdio with
  | .returned status | .exited status => pure status.toUInt32
  | .trapped message => throw (IO.userError message)
