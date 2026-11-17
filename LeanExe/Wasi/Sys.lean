import LeanExe.Wasi.Action
import LeanExe.Wasi.CallTable

/-!
Typed operations for flat WASI calls.  Each returns a structure whose `errno` field is the call's
errno, 0 on success; the other fields hold the call's results on success and are 0 or empty after
an errno.  An argument that does not fit the call's core type, a length of `2^32` or more, gives
errno 61 (`overflow`) without a call, and an enum value outside its enum or a flags value with a
bit outside its flags gives errno 28 (`inval`) without a call, since Wasmtime 44 traps on such a
value.  `LeanExe/Wasi/SysCalls.lean` holds the generated typed functions of the other flat calls,
whose results are the structures below or a record's fields.
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
  size : UInt64
  bytes : Bytes

/-- The errno and the result word of a call with one result word. -/
structure WordResult where
  errno : UInt64
  value : UInt64

/-- The errno and the buffer of a call with an output buffer. -/
structure BytesResult where
  errno : UInt64
  bytes : Bytes

/-- The errno, the buffer, and the number of the buffer's bytes that the call used, of a call with
an output buffer and a result word.  The bytes after `count` hold the buffer's earlier content. -/
structure BytesCountResult where
  errno : UInt64
  bytes : Bytes
  count : UInt64

/-- The result of `poll_oneoff`: the errno, the number of events, and the fields of the first
event, its userdata, its error, its type (0 for a clock, 1 for a read, 2 for a write), and the
`nbytes` and flags of its `fd_readwrite`.  Wasmtime 44 writes the events of the subscriptions that
are ready in the order of the subscriptions, so the first event's userdata tells which subscription
fired.  The fields are 0 after an errno. -/
structure PollResult where
  errno : UInt64
  count : UInt64
  userdata : UInt64
  error : UInt64
  type : UInt64
  nbytes : UInt64
  flags : UInt64

/-- A descriptor that a program holds: the preopened directory, `Handle.preopened`, or the
descriptor of a file that `withOpen` opens.  A typed function takes a `Handle` for each
descriptor parameter. -/
structure Handle where
  fd : UInt64

/-- The directory that the host preopens at descriptor 3. -/
def Handle.preopened : Handle := ⟨3⟩

/-- `withOpen dir dirflags path oflags rightsBase rightsInheriting fdflags onError body` calls
`path_open` for `path` under `dir`.  On a nonzero errno it runs `onError errno` and returns its
result with the word 0.  The errno is the host's, or, without a call, that of the first argument
that `Call.pathOpen` rejects, in the order of the arguments: 61 (`overflow`) for a `dir`,
`dirflags`, `oflags`, or `fdflags` of `2^32` or more and for a `path` of `2^32` bytes or more, and
28 (`inval`) for flags with a bit outside their masks: `dirflags` outside `0x1`, `oflags` outside
`0xf`, `rightsBase` and `rightsInheriting` outside `0x3fffffff`, and `fdflags` outside `0x1f`.
Otherwise it runs `body` with the new descriptor, and when `body` returns, it calls `fd_close` on
the descriptor and returns `body`'s result with the errno of `fd_close`.  A body that exits or
traps ends the process with the descriptor open, and Wasmtime closes it at exit.  Programs open
and close descriptors only through `withOpen`.

`verified_compile_wasi` reflects `withOpen` as one shape of the existing commands, which
`Verified.Wasi.Command.HandleCheck` recognizes.  With the argument variables `d`, `f`, `o`, `b`,
`i`, and `g` and the path variable `p`, the shape is

```
bind (sys Call.pathOpen (.flat 1 false) [d, f, o, b, i, g] [p])
  (ite (cmp .ne (proj (var 0) (fst here)) (word 0))
    (bind onError' (ret (mk (var 0) (word 0))))
    (bind (ret (proj (var 0) (snd here)))
      (bind body'
        (bind (sys Call.fdClose (.flat 0 false) [var 1] []) (ret (mk (var 1) (var 0)))))))
```

where `onError'` is the reflection of `onError` applied to the errno, the first component of the
open's result in variable 0, and `body'` the reflection of `body` applied to the handle in
variable 0.  The pairs are `mk` when the source type of `α` is an element (a word, a `Bool`, a
float, or a tuple of these), as for a structure whose `Flat` tuple holds only these, and `pair`
otherwise.  `α` must have a source type, so the compiler refuses a body that returns `Unit`. -/
def withOpen {α : Type} (dir : Handle) (dirflags : UInt64) (path : Bytes)
    (oflags rightsBase rightsInheriting fdflags : UInt64) (onError : UInt64 → Action α)
    (body : Handle → Action α) : Action (α × UInt64) :=
  .sys .pathOpen [.word dir.fd, .word dirflags, .bytes path, .word oflags, .word rightsBase,
      .word rightsInheriting, .word fdflags] fun opened =>
    if opened.errno != 0 then Action.bind (onError opened.errno) fun result => .pure (result, 0)
    else Action.bind (body ⟨opened.word 0⟩) fun result =>
      .sys .fdClose [.word (opened.word 0)] fun closed => .pure (result, closed.errno)

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
    if sizes.errno != 0 then .pure ⟨sizes.errno, 0, 0, Bytes.empty⟩
    else if 4294967296 ≤ sizes.word 1 + 4 * sizes.word 0 + 3 then .pure ⟨61, 0, 0, Bytes.empty⟩
    else .sys .argsGet [] fun got =>
      if got.errno != 0 then .pure ⟨got.errno, 0, 0, Bytes.empty⟩
      else .pure ⟨0, sizes.word 0, sizes.word 1, got.bytes 0⟩

/-- The environment variables: `environ_sizes_get`, then `environ_get` into a buffer of the reported
size, with the rules of `args`.  `bytes` holds the variables as `NAME=VALUE`, each followed by a
zero byte. -/
def environ : Action ArgsResult :=
  .sys .environSizesGet [] fun sizes =>
    if sizes.errno != 0 then .pure ⟨sizes.errno, 0, 0, Bytes.empty⟩
    else if 4294967296 ≤ sizes.word 1 + 4 * sizes.word 0 + 3 then .pure ⟨61, 0, 0, Bytes.empty⟩
    else .sys .environGet [] fun got =>
      if got.errno != 0 then .pure ⟨got.errno, 0, 0, Bytes.empty⟩
      else .pure ⟨0, sizes.word 0, sizes.word 1, got.bytes 0⟩

end LeanExe.Wasi
