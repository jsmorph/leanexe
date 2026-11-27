module

public import Demos.RunningSum.Stream

@[expose] public section

@[extern "leanexe_running_sum_read_stdin"]
opaque readStdinSome (capacity : UInt64) : IO ByteArray

def main : IO UInt32 := do
  let streams ← LeanExe.Wasi.NativeHost.stdio
  let host := { streams with read := fun capacity => do
    return .returned 0 ⟨← readStdinSome capacity⟩ }
  match ← Demos.RunningSum.process.runFrom host Demos.RunningSum.initial with
  | .returned status | .exited status => pure status.toUInt32
  | .trapped message => throw (IO.userError message)
