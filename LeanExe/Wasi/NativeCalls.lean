import LeanExe.Wasi.Interpreter
import LeanExe.Wasi.CallTable
import Std.Time

/-!
Native service of the flat calls of `LeanExe.Wasi.Sys` for `Action.run`.  `clock_time_get` reads
the wall clock for clock 0 and the monotonic clock for clock 1 and returns errno 8 (`badf`) for the
CPU clocks 2 and 3, as Wasmtime 44 does; `Action.run` rejects other clock ids before the host.
`random_get` reads the operating system's random source, and `args_sizes_get` and `args_get` report
the given arguments.  An errno reply carries zero bytes of each region's size.  Other calls trap.
-/

namespace LeanExe.Wasi.NativeHost

/-- The low `width` bytes of `value`, least significant first. -/
def littleEndianBytes (width : Nat) (value : UInt64) : Bytes :=
  ⟨⟨(Array.range width).map fun index => (value >>> (8 * index).toUInt64).toUInt8⟩⟩

def zeros (width : Nat) : Bytes := ⟨⟨Array.replicate width 0⟩⟩

/-- The arguments, each followed by a zero byte. -/
def argumentBytes (arguments : List String) : Bytes :=
  ⟨arguments.foldl (fun buffer argument => (buffer ++ argument.toUTF8).push 0) ByteArray.empty⟩

def serve (arguments : List String) (call : Call) (args : List Arg) :
    IO (Transfer (List Bytes)) := do
  if call = .clockTimeGet then
    let id := (args.head?.map Arg.value).getD 0
    if id = 0 then
      let now ← Std.Time.Timestamp.now
      let nanos := now.toNanosecondsSinceUnixEpoch.val.toNat
      return .returned 0 [littleEndianBytes 8 (UInt64.ofNat nanos)]
    if id = 1 then
      return .returned 0 [littleEndianBytes 8 (UInt64.ofNat (← IO.monoNanosNow))]
    return .returned 8 [zeros 8]
  if call = .randomGet then
    let length := (args.head?.map Arg.capacity).getD 0
    return .returned 0 [⟨← IO.getRandomBytes length.toUSize⟩]
  if call = .argsSizesGet then
    return .returned 0 [littleEndianBytes 4 (UInt64.ofNat arguments.length),
      littleEndianBytes 4 (UInt64.ofNat (argumentBytes arguments).data.size)]
  if call = .argsGet then
    return .returned 0 [argumentBytes arguments]
  return .trapped s!"wasi {call.name}: the native host does not serve it" []

/-- `host` with the flat calls of `LeanExe.Wasi.Sys`, whose argument calls report `arguments`. -/
def withSys (host : NativeHost) (arguments : List String) : NativeHost :=
  { host with sys := serve arguments }

end LeanExe.Wasi.NativeHost
