# Verified WASI Manual

`verified_compile_wasi` compiles Lean actions to core WebAssembly with WASI Preview 1 imports for stdin reads, stdout and stderr writes, and exit.  The generated proofs relate execution of the exported functions to the original Lean actions, including their ordered I/O effects, returned values, and terminal outcomes.  [The verified compiler manual](verified-manual.md) describes the pure dialect used inside actions.  [The WASI design](verified-wasi-design.md) records the API and proof decisions.

## Writing actions

### Operations and results

`import LeanExe.Wasi` provides the compiler-independent API and native interpreter.  `import Verified.Wasi` also provides `verified_compile_wasi`.  The API lives in `LeanExe.Wasi` and uses `LeanExe.Bytes` for packed bytes.

| Operation | Type | Behavior |
|---|---|---|
| `readSome capacity` | `UInt64 → Action ReadResult` | Makes one stdin read when `capacity < 2^32`. |
| `writeStdoutSome bytes` | `Bytes → Action WriteResult` | Makes one write to stdout. |
| `writeStderrSome bytes` | `Bytes → Action WriteResult` | Makes one write to stderr. |
| `exit code` | `UInt64 → Action α` | Requests terminal exit with `code mod 2^32`. |
| `loop count init test step` | `UInt64 → σ → (UInt64 → σ → Bool) → (UInt64 → σ → Action σ) → Action σ` | Runs a bounded sequence of effectful steps. |

[The result definitions](../LeanExe/Wasi/Action.lean) give `ReadResult` the fields `errno : UInt64` and `bytes : Bytes`, and `WriteResult` the fields `errno : UInt64` and `count : UInt64`.  Zero errno means success.  A successful read may return fewer bytes than requested, and a successful write may report any count from zero through the offered length.  The operations perform no retries.  Stream hosts report EOF through empty success.  A zero-capacity read still invokes the host once, so its empty result supplies no EOF evidence.  The abstract host relation has no separate EOF state.

A read capacity of at least `2^32` returns errno 61 and empty bytes before allocation or host invocation.  A nonzero read errno returns empty bytes, and a nonzero write errno returns count zero.  The host model records committed prefixes on error or trap, so these public results do not prove zero device progress.  Returned errnos are bounded by the Preview 1 errno range, 0 through 76.

Actions use ordinary Lean `do` notation:

```lean
import Verified.Wasi

namespace StdioExample
open LeanExe LeanExe.Wasi

def copySome (capacity : UInt64) : Action UInt64 := do
  let input ← readSome capacity
  if input.errno != 0 then
    pure input.errno
  else
    let output ← writeStdoutSome input.bytes
    pure output.errno

def main : Action UInt64 := copySome 4096

verified_compile_wasi callable := [copySome, main]
verified_compile_wasi command (main := main) := [copySome, main]
end StdioExample
```

[The stdio example](../Verified/Examples/WasiStdio.lean) makes at most one read and one write.  It returns the write's errno even when the host reports a short successful write.  A complete stream copy requires an explicit loop and handling of short transfers.

`Action` describes effects and their continuations.  `let action := readSome n` binds a description.  Each `let result ← action` executes it once, so sequencing the same description twice makes two reads.  Reflection constructs typed code and its correspondence proof without executing guest I/O.  Native execution constructs and interprets continuations as the action runs.

### Packed bytes

| Expression | Meaning |
|---|---|
| `Bytes.empty` | Empty bytes. |
| `bytes.size` | Length as `UInt64`. |
| `bytes.get index` | Byte as `UInt64`, or zero outside the buffer. |
| `Bytes.build count element` | `count` bytes, with the low eight bits of `element index` at each index. |
| `bytes![0, 65, 255]` | A packed literal.  Each numeral must lie between 0 and 255. |

[The byte dialect](../LeanExe/Dialect/Bytes.lean) wraps a native `ByteArray`.  Compiled byte values occupy two `i64` words: the payload address and logical length.  The representation requires a length below `2^32`.  A compiled builder requesting at least `2^32` bytes takes a guest resource trap.  `Bytes.build` evaluates its pure callback in index order, with a `UInt64` index.

Nonempty literals have deduplicated raw data in the module's static pool, after its constant word arrays.  Each literal evaluation makes an owned copy, including evaluations inside pure helpers, builders, branches, and loops.  Empty literals and empty builders return canonical empty values without allocation.  These byte operations also belong to the pure verified compiler.

Ownership follows the pure compiler's rules.  Writes borrow their buffer.  Reads return owned bytes.  Passing bytes to an owned parameter or returning owned bytes transfers ownership, while returning borrowed bytes makes a copy.  Cleanup releases an unused owned allocation after its last use.  An empty argument may have a nonzero allocated root.  Cleanup tests the root, and borrowed representations protect the allocation's header and capacity even when its logical length is zero.  [The byte representation](../Verified/Bytes/Basic.lean) states these memory requirements.

### Control and helper functions

An action may return `Unit` or a value accepted by the pure dialect.  Structures use the same `Flat` representation as pure functions.  Pure expressions, `let` bindings, action bindings, conditionals, and calls to listed helpers compose inside actions.  An unlisted `@[inline]` helper unfolds at its use.  A dependent conditional is accepted when its branches do not use the proof of the condition.

`LeanExe.Wasi.loop count init test step` starts with index zero and state `init`.  At each index below `count`, it evaluates the pure `test index state`.  False returns the current state.  True executes `step index state`, takes its returned state, and increments the index.  Reaching `count` returns the state without another test.  Count zero skips both callbacks.  Exit or host trap in a step terminates the whole action.  Outer values captured by callbacks remain borrowed across iterations.

Effectful helper calls are acyclic.  Recursive effectful definitions are rejected.  Pure helpers retain the verified compiler's recursion and tail-loop rules.  General `IO` and `BaseIO` operations, arbitrary monadic recursion, and action values stored in runtime containers are outside the reflected dialect.

## Compilation and generated declarations

### Callable and command modules

The two command forms are:

```lean
verified_compile_wasi p := [pureHelper, actionHelper, action]
verified_compile_wasi p (main := main) := [pureHelper, actionHelper, main]
```

The compiler collects pure definitions first, preserving their relative order, then reflects effectful definitions in their relative order.  A pure helper's other listed pure callees must precede it among the pure definitions.  An effectful helper's listed effectful callees must precede it among the effectful definitions.  Pure helpers are available to every effectful definition.  The selected command `main` must appear among the effectful definitions and have type `Action UInt64` with no visible parameters.  Captured constant arrays become hidden borrowed table arguments.

Callable modules export each listed effectful definition under the last component of its Lean name.  They also export `alloc` and `release`, allocation counters `allocCount` and `freeCount`, linear memory `memory`, and the empty table `__indirect_function_table`.  Pure helpers compile internally.  Command modules export `_start : () → ()`, `memory`, and the empty table.  `_start` invokes the selected main, then passes a normally returned status to `proc_exit`.  An explicit exit in main or a helper terminates before that final exit.

The frontend rejects duplicate definitions, generated-name collisions within each of the pure and effectful groups, and callable names reserved by the runtime exports.  [The checked public examples](../Verified/Wasi/ReflectCommandCases.lean) include hidden tables, literals, byte ownership, records, computed call arguments, and both export forms.

The module has exactly three function imports from `wasi_snapshot_preview1`:

| Import | WebAssembly signature | Descriptor |
|---|---|---|
| `fd_read` | `(i32, i32, i32, i32) → i32` | 0: stdin. |
| `fd_write` | `(i32, i32, i32, i32) → i32` | 1: stdout, or 2: stderr. |
| `proc_exit` | `(i32) → ()` | None. |

[The ABI definitions](../Verified/Wasi/ABI.lean) reserve scratch bytes `[0,16)` for one iovec and transfer count.  The read wrapper checks capacity before narrowing it to 32 bits.  Heap and byte-representation premises prove that pointer and write-length narrowing preserves their values.  The module relocates pure calls and types by three positions, uses the shared allocator and release functions at indices 3 and 4, and passes a hidden depth through internal calls.  Public wrappers initialize depth to zero.  Effectful calls increment it, and guarded pure calls use the same depth.  Guarded calls enforce the depth limit of 1,000, and reflected effectful functions have at most 32 local positions.

A callable host configures stdio before invoking an export and may invoke another export after normal return.  Exit and trap terminate the instance's lifecycle.  Command hosts invoke `_start` once.  The modules provide no `_initialize` hook, which the pinned application ABI permits to be absent.

### Declarations

| Declaration | Statement or value |
|---|---|
| `p.program`, `p.funs` | Typed effect program and its action meanings. |
| `p.pure.program`, `p.pure.module` | Typed pure helpers and their import-free module. |
| `p.f.func`, `p.f.callee` | Typed effect function and its reference in the complete program. |
| `p.f.related` | The original Lean action corresponds to the typed function's meaning, including its result representation. |
| `p.literalPool` | Shared raw byte-literal pool. |
| `p.module` | Complete importing module. |
| `p.calls` | Universal cost-aware correctness for the compiled effectful callees. |
| `p.initial` | Allocator invariant, memory cap, borrowed constant tables, and static bytes in the modeled initial store. |
| `p.f.implements` | Callable form: execution of the exported wrapper refines the original Lean function applied to its native parameters. |
| `p.f.exported` | Callable form: the function's name and wrapper index occur in the module's exports. |
| `p.f.total` | Callable form: under resource and reached-host premises, execution returns or exits with an accepted status. |
| `p.start`, `p.exported` | Command form: execution of the exported `_start` refines native main followed by exit, and `_start` has the stated export index. |
| `p.total` | Command form: under resource and reached-host premises, `_start` exits with an accepted status. |
| `p.validity` | The module satisfies the repository's WebAssembly validity predicate. |
| `p.encoding`, `p.encoded`, `p.decoded` | Encoded byte list, its encoding equation, and decoding to exactly `p.module`. |
| `p.validBinary` | The encoded bytes satisfy the repository's binary-validity predicate. |
| `p.bytes` | One byte sequence encodes and decodes the module, satisfies binary validity, and has the generated native execution and total-execution refinements. |

The frontend proves instruction-profile, syntax, argument-placement, literal-coverage, and pool-separation obligations for the generated program.  Lean's kernel checks the reflection relations, finite checks, validity proofs, and applications of the universal compiler theorem.  [The public frontend](../Verified/Wasi/ReflectCommand.lean), [module validity rules](../LeanExe/Encoding/Spec/Validity.lean), and [binary correctness statement](../LeanExe/Encoding/Correctness.lean) define these claims.  File emission remains a separate operation through [the module emitter](../tools/Emit.lean).

## Execution proofs and their premises

### Results and traces

The exported-entry theorems quantify an initial store, host implementation, and native arguments.  They provide a fuel bound such that every modeled execution with at least that much fuel has one of the following classifications:

| Outcome | Proved relation |
|---|---|
| Normal return | A source execution returns the corresponding native value.  The machine words represent that value with owned result memory.  The allocator invariant and the caller's retained heap regions outside scratch survive. |
| Accepted exit or host trap | A source execution has the same terminal outcome, committed final world, and ordered I/O trace.  Accepted exit also has the designated exit marker and exact narrowed status. |
| Guest resource trap, when permitted | A source prefix has the same committed world and trace, with a residual action describing the remaining work. |

[The native result statement](../Verified/Wasi/NativeResult.lean) relates wrapper execution to native Lean actions.  [The command entry theorem](../Verified/Wasi/NativeCommand.lean) includes main's final exit.  Host relations may permit several replies.  Each sufficiently fueled target execution has a matching source execution or permitted source prefix with the same committed effects.

The target host state contains the abstract world and an append-only joint event journal.  Events record reads, offered writes and their committed counts, accepted exits, and rejected exit requests.  The final journal equals the initial journal followed by the source trace.  This preserves ordering even when stdout and stderr refer to the same host destination.  The world is proof and host state, not an extra argument passed by the source program.

### Resources, host assumptions, and total execution

| Premise | Requirement |
|---|---|
| Host implementation | The Talos host satisfies `hostSpec host` for the three imports, including reply bounds, trace updates, terminal exit behavior, and guest-memory preservation. |
| Heap and arguments | `Heap.At`, correctly represented argument words, and separation of consumed blocks from retained and borrowed memory. |
| Static input | The literal pool's bytes and region exist and lie apart from consumed blocks.  Hidden table arguments represent their declared constants. |
| Scratch separation | Every live region read through an argument lies apart from `[0,16)`, including the full allocation of an allocated-empty byte buffer. |
| Memory cap | At most 65,535 pages. |
| No guest resource failure | With `aborts = false`, `Heap.Within` supplies room for a budget and `Resource.CallPrefixBound` bounds every typed source resource prefix by that budget with its size and depth checks satisfied. |
| No reached host trap | A total-execution theorem also requires `host.NoTrapsAlong` the native action in its initial world. |

The budget is a proof-level natural number.  It accounts for allocation and copying in pure fragments, read-buffer capacity, helper calls, and loop iterations along host-permitted paths.  Executable lengths, loop counts, byte values, and statuses remain `UInt64`.  `p.f.callee`, `p.program`, and the source resource relations provide concrete terms for a resource proof.  The frontend exposes this typed prefix condition.  It does not synthesize a bound solely from the original input for every I/O program.

[The retained-buffer example](../Verified/Examples/WasiRetain.lean) performs up to two one-byte reads, writes the previous buffer at each iteration, and returns the last buffer.  [Its budget proof](../Verified/Examples/WasiRetainBudget.lean) bounds every host-reply path and resource prefix by 112 bytes: each read charges a 48-byte header and eight-byte minimum capacity.  [The total-execution application](../Verified/Examples/WasiRetainTotal.lean) proves that this budget fits the modeled initial store, supplies the generated representation and separation premises, and applies `compiled.retain.total` under a satisfying host and `NoTrapsAlong`.  [The mixed-depth example](../Verified/Examples/WasiDepth.lean) combines effectful helpers, a hidden constant table, and guarded pure recursion.  Its resource-prefix condition must cover the combined effectful and pure call depth below 1,000.

`NoTrapsAlong` quantifies only operations reachable through source prefixes.  Returned nonzero errnos remain ordinary results.  The premise excludes read and write traps and rejected exit requests along those paths.  Thus callable `.total` allows a native return or accepted exit, while command `.total` proves accepted exit.  A host that rejects some statuses can satisfy the premise for a program whose reached exits use accepted statuses.  [The reached-host condition](../LeanExe/Wasi/NoTrapPrefix.lean), [typed prefix bound](../Verified/Wasi/ResourcePrefix.lean), and [command total theorem](../Verified/Wasi/CommandTotal.lean) give the exact statements.

With `aborts = true`, `.implements` and `.start` permit guest allocation or depth failure after earlier I/O.  Their prefix classification retains those effects.  Normal-return ownership and heap-preservation postconditions apply to a returned store.  Terminal exit and trap require the host to discard the instance.

The host's memory rules preserve globals, memory limits and page count, and bytes outside scratch and a read's destination.  Read and write preserve the exit marker.  Accepted exit records its status and uses the designated exit trap.  Rejected exit preserves the previous marker and records its failure.  The guest wrapper follows `proc_exit` with `unreachable`, while the host API requires the import to terminate.  [The host assumptions](../Verified/Wasi/HostSpec.lean) distinguish accepted exit from arbitrary host traps.

### Initial store and external execution

`p.initial` proves properties of the store constructed from `p.module.initialStore`, with a supplied host world.  It initializes the allocator, constant arrays, and raw static bytes and proves the declared memory cap.  The exported-entry theorems can start there after their argument, host, separation, and resource premises have been established.  They can also apply after a prior normal call when its postconditions establish the next call's premises.

The proofs use Lean's kernel, the project's definitions of source actions and memory representations, Talos's execution semantics, and the binary decoder.  Their axiom audit permits `propext`, `Classical.choice`, and `Quot.sound`.  Host installation in a real engine, operating-system I/O, the native stream adapter, emitted file contents, and Wasmtime's agreement with the modeled semantics require external validation.  Talos permits memory growth up to the declared cap, while an engine may refuse growth earlier.  Fuel bounds describe modeled guest execution.  External reads may block.  [The shared proof scope](design.md#scope-of-the-theorem) describes the engine and file-emission limits.

## Native and WebAssembly execution

### Native interpreter

`action.run host : IO (Outcome α)` executes an action through a `NativeHost`.  `action.runStdio` uses Lean's current stdin, stdout, and stderr.  Its result is `.returned value`, `.exited code`, or `.trapped message`.  Exit returns a terminal outcome to the Lean caller without terminating the Lean process.

`NativeHost.ofStreams` reports errno zero for successful stream reads and full successful count after a write and flush.  It accepts every narrowed exit status.  Stream operations may use several operating-system calls.  An `IO.Error` propagates to the Lean caller, including when a failed stream operation has already changed the outside world.  Explicit `Transfer.trapped` replies instead produce an `Outcome.trapped`.  Invalid host reply lengths or errnos raise an `IO.Error`.  [The native interpreter](../LeanExe/Wasi/Interpreter.lean) defines this adapter policy.

### Wasmtime host

The [Wasmtime host setup](leanexe-manual.md#the-wasmtime-host) builds `build/tools/leanexe-wasmtime-host` against pinned Wasmtime 44.0.0.  It uses Wasmtime's standard Preview 1 implementation.  From the repository root, the stdio example builds and emits both module forms:

```sh
mkdir -p build/wasi
tools/leanrun --timeout 10m lake build Verified.Examples.WasiStdio
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean \
  Verified.Examples.WasiStdio StdioExample.command.module build/wasi/stdio-command.wasm
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean \
  Verified.Examples.WasiStdio StdioExample.callable.module build/wasi/stdio-callable.wasm
wasm-tools validate build/wasi/stdio-command.wasm
wasm-tools validate build/wasi/stdio-callable.wasm
```

The command form runs `main` and exits with its returned errno:

```sh
build/tools/leanexe-wasmtime-host --stdin-file input.bin \
  --stdout-file output.bin --stderr-file errors.bin run build/wasi/stdio-command.wasm
```

`run` enables WASI and invokes `_start`.  Without stream-file options it inherits stdio.  For a callable module with a `copySome : UInt64 → Action UInt64` export:

```sh
build/tools/leanexe-wasmtime-host --wasi --stdin-file input.bin \
  --stdout-file output.bin --stderr-file errors.bin --control-file control.txt \
  call build/wasi/stdio-callable.wasm copySome i64 i64:4096
```

Control output contains return values, allocation counts in `call-stats` mode, and terminal records.  Guest stream files contain guest bytes.  Callable WASI modes require `--control-file` or a separate `--stdout-file`.  Script and session modes also require `--stdin-file` so guest input does not consume host instructions.  Host diagnostics use host stderr.

Exit always passes the low 32 bits of the source status.  [Wasmtime 44 accepts statuses below 126](https://github.com/bytecodealliance/wasmtime/blob/v44.0.0/crates/wasi/src/p1.rs#L2614-L2625) and rejects larger narrowed statuses as engine errors.  For example, `2^32 + 7` requests accepted status 7, and `2^32 + 126` requests rejected status 126.  An accepted exit produces a `wasi-exit STATUS` record when control records are enabled, and the host process uses the low eight bits as its status.  Rejection produces an error diagnostic and process status 1.  Both outcomes preserve previously written guest output.  This differs from the native stream adapter's policy of accepting every narrowed status.

## Tests

```sh
tests/wasi/run.sh --foundations-only
tests/wasi/run.sh
```

[The WASI driver](../tests/wasi/run.sh) builds the universal proofs and audits their axioms.  The foundations-only mode also runs native interpreter, wrapper-code, and exit-model tests.  The full mode adds emitted-module validation and execution tests for packed bytes, literals, ownership and allocation counts, reflected callable and command modules, and the standard Wasmtime host.  [The public reflection driver](../tests/wasi/reflection-run.sh) tests generated modules against binary stream fixtures and separate control records.  [The host tests](../tests/wasi/host.sh) cover stream routing, accepted and rejected exits, low-32-bit conversion, and terminal lifecycle behavior.

The interface follows the pinned [Preview 1 declarations](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/wasi_snapshot_preview1.witx), [type definitions](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/typenames.witx), and [application ABI](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/application-abi.md).
