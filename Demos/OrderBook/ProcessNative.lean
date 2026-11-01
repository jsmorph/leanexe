import Demos.OrderBook.Process

/-! The order book's process on the real stdin and stdout.  Reads use Running sum's
[POSIX reader](../RunningSum/read.c), which returns after one successful `read` of file
descriptor 0, and writes use Lean's stdout stream with a flush after each write. -/

@[extern "leanexe_running_sum_read_stdin"]
private opaque readStdinSome (capacity : UInt64) : IO ByteArray

def main : IO UInt32 := do
  let streams ← LeanExe.Wasi.NativeHost.stdio
  let host := { streams with read := fun capacity => do
    return .returned 0 ⟨← readStdinSome capacity⟩ }
  match ← Demos.OrderBook.Process.process.runFrom host Demos.OrderBook.Process.initial with
  | .returned status | .exited status => pure status.toUInt32
  | .trapped message => throw (IO.userError message)
