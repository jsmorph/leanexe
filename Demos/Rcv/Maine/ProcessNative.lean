import Demos.Rcv.Maine.Process

/-! The Maine process on the real stdin and stdout, run as `Demos/Rcv/ProcessNative.lean` runs the
Oakland process.  Reads use Running sum's [POSIX reader](../../RunningSum/read.c), which returns
after one successful `read` of file descriptor 0, and writes use Lean's stdout stream with a flush
after each write.  `begin` runs first, and the steps run from its state while it runs. -/

@[extern "leanexe_running_sum_read_stdin"]
private opaque readStdinSome (capacity : UInt64) : IO ByteArray

def main : IO UInt32 := do
  let streams ← LeanExe.Wasi.NativeHost.stdio
  let host := { streams with read := fun capacity => do
    return .returned 0 ⟨← readStdinSome capacity⟩ }
  match ← Demos.Rcv.Maine.Process.begin.run host with
  | .returned first =>
    if first.running then
      match ← Demos.Rcv.Process.process.runFrom host first.state with
      | .returned status | .exited status => pure status.toUInt32
      | .trapped message => throw (IO.userError message)
    else pure first.status.toUInt32
  | .exited status => pure status.toUInt32
  | .trapped message => throw (IO.userError message)
