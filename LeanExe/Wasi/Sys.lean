import LeanExe.Wasi.Action

/-!
Typed operations for flat WASI calls.  Each returns a structure whose `errno` field is the call's
errno, 0 on success; the other fields hold the call's results on success and are 0 or empty after
an errno.  An argument that does not fit the call's core type, a length of `2^32` or more, gives
errno 61 (`overflow`) without a call, and an enum value outside its enum gives errno 28 (`inval`)
without a call, since Wasmtime 44 traps on such a value.
-/

namespace LeanExe.Wasi

structure ClockResult where
  errno : UInt64
  time : UInt64

structure RandomResult where
  errno : UInt64
  bytes : Bytes

structure ArgsSizes where
  errno : UInt64
  count : UInt64
  size : UInt64

structure ArgsResult where
  errno : UInt64
  count : UInt64
  bytes : Bytes

/-- `clock_time_get id precision`: the time of clock `id` in nanoseconds.  The clocks are 0
(realtime), 1 (monotonic), 2 (process CPU time), and 3 (thread CPU time); an id of 4 or more gives
errno 28 without a call. -/
def clockTimeGet (id precision : UInt64) : Action ClockResult :=
  .sys .clockTimeGet [.word id, .word precision] fun reply => .pure ⟨reply.errno, reply.word 0⟩

/-- `random_get` into a fresh buffer of `length` bytes. -/
def randomGet (length : UInt64) : Action RandomResult :=
  .sys .randomGet [.space length] fun reply => .pure ⟨reply.errno, reply.bytes 0⟩

/-- `args_sizes_get`: the number of program arguments and the bytes they occupy with a zero byte
after each. -/
def argsSizesGet : Action ArgsSizes :=
  .sys .argsSizesGet [] fun reply => .pure ⟨reply.errno, reply.word 0, reply.word 1⟩

/-- The program arguments: `args_sizes_get`, then `args_get` into a buffer of the reported size.
`bytes` holds the arguments, each followed by a zero byte.  An errno of `args_sizes_get` ends the
operation with that errno; reported sizes whose buffer, with the argument pointers after it, would
reach `2^32` bytes give errno 61. -/
def args : Action ArgsResult :=
  .sys .argsSizesGet [] fun sizes =>
    if sizes.errno != 0 then .pure ⟨sizes.errno, 0, Bytes.empty⟩
    else if 4294967296 ≤ sizes.word 1 + 4 * sizes.word 0 + 3 then .pure ⟨61, 0, Bytes.empty⟩
    else .sys .argsGet [] fun got =>
      if got.errno != 0 then .pure ⟨got.errno, 0, Bytes.empty⟩
      else .pure ⟨0, sizes.word 0, got.bytes 0⟩

end LeanExe.Wasi
