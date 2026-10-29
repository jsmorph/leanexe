# Verified compiler: WASI Preview 1 design

[The WASI manual](wasi.md) describes the public API and generated declarations.  [The development journal](../devnotes.md#2026-10-23-implementing-the-wasi-agenda) records implementation and test results.

## Scope and sources

The initial host interface consists of `fd_read`, `fd_write`, and `proc_exit` in `wasi_snapshot_preview1`.  Source operations select stdin 0, stdout 1, or stderr 2.  A program can compute between operations, inspect errors and short transfers, and return or exit.  Later work may add other Preview 1 operations and library retry policies.

The specification pin is WebAssembly/WASI commit `fae981bae14809d91f9bc2d63852d461f331d161`.  Its [interface definitions](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/wasi_snapshot_preview1.witx), [type definitions](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/typenames.witx), [generated reference](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/docs.md), and [application ABI](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/application-abi.md) are the external references.  A future specification update requires review of the ABI, host assumptions, and proof statements.

The [pure typed source](../Verified/Source.lean) has value semantics.  Its [compiler](../Verified/Compile.lean) emits an import-free module, and its [runtime predicate](../Verified/RuntimeFacts.lean) requires that layout.  The [pure correctness theorem](../Verified/Correct.lean) and [representation API](../LeanExe/Pipeline/Implements.lean) use `Store Unit`.  [The effect language](../Verified/Wasi/Source.lean) embeds these pure expressions, and [its compiler theorem](../Verified/Wasi/Correct.lean) connects them to host-dependent execution through import relocation and host-state transport.

### Earlier implementations

Two earlier efforts informed this design.  A byte-I/O proof inventory covered syscall models, an abstract write protocol, and six concrete echo executions.  The current wrappers have universal execution proofs against the current allocator and ownership layout, and the echo executions remain useful test cases.  An earlier native WASI API exposed all 46 Preview 1 functions through opaque `BaseIO` operations, with direct native lowering, one-iovec transfers, packed byte arrays, and 38 execution cases.  Its wrapper layout and cleanup supplied implementation references, and its full proof gates were incomplete.  The current implementation supplies separate transport, wrapper, and universal effect proofs.  [The development journal](../devnotes.md#2026-10-23-reviewing-the-wasi-design) records the revisions of both efforts.

The earlier native WASI API uses `Action := BaseIO`, UInt32 descriptors, capacities, counts, errnos, and exit codes, and `Except UInt32 ByteArray` read results.  Its byte representation has owner, pointer, and length values.  The current API uses a semantic action monad, UInt64-facing operations, explicit result records, and one root plus length.  Both APIs use `LeanExe.Wasi.Action`, with different meanings and types.  Importing earlier client code requires an explicit compatibility design.  Its wider operation set remains outside the initial scope.

The earlier direct wrappers provide a lowering reference: one iovec, errno checks before count reads, cleanup of failed or empty reads, and partial-transfer preservation.  Its emitter imports the full primitive registry and emits command modules.  The current [module construction](../Verified/Wasi/Program.lean) adds the three-import layout and callable form.  The earlier effect analysis identifies effectful code but supplies no trace semantics or compiler correctness theorem.

## Lean API and behavior

### Actions and results

The public namespace is `LeanExe.Wasi`.  [The native import](../LeanExe/Wasi.lean) supplies actions and their interpreter independently of either compiler.  The shared byte type is `LeanExe.Bytes`, with [its native operations](../LeanExe/Dialect/Bytes.lean).  Compiler representations and proofs live under `Verified`, and [the compiler import](../Verified/Wasi.lean) supplies `verified_compile_wasi`.

`Action α` is a semantic monad with Lean `pure` and `bind` instances.  The accepted source uses ordinary `do`, named first-order helpers, bindings, conditionals, pure Verified calls, and the bounded loop below.  Effectful helper calls form an acyclic call graph.  Pure callees retain their existing recursion and allocation conditions.  These control-flow restrictions follow the review decisions.

| Declaration | Meaning |
|---|---|
| `readSome (capacity : UInt64) : Action ReadResult` | One stdin read after capacity validation and any required allocation. |
| `writeStdoutSome (bytes : Bytes) : Action WriteResult` | One stdout write, borrowing `bytes`. |
| `writeStderrSome (bytes : Bytes) : Action WriteResult` | One stderr write, borrowing `bytes`. |
| `exit (code : UInt64) : Action α` | A terminal exit request with the low 32 bits of `code`, producing an accepted exit or a host trap. |
| `loop (count : UInt64) (init : σ) (test : UInt64 → σ → Bool) (step : UInt64 → σ → Action σ) : Action σ` | At most `count` iterations, carrying a state of an accepted runtime value type. |
| `ReadResult` | A record with `errno : UInt64` and `bytes : Bytes`. |
| `WriteResult` | A record with `errno : UInt64` and `count : UInt64`. |

Zero errno denotes success.  Error results remain ordinary values: the source decides whether to return, exit, continue, or report an error.  Sequencing an action executes it once even if its result is discarded.  A pure binding such as `let action := readSome n` names a description.  A monadic binding such as `let result ← action` executes it.  Sequencing the same named action twice performs two calls.

Native action descriptions and continuations can be constructed as the native interpreter runs.  Reflection translates accepted definitions into fixed typed code.  It performs no guest I/O.  Compiled runtime values have the compiler's value types, including bytes and result records.  The host world belongs to the semantics and host state rather than the source program's arguments.

`loop` is a command-description node.  It starts with index zero and `init`.  Before each iteration it tests the index against `count`, then evaluates the pure `test` on the index and current state.  Reaching the count or a false test returns the current state.  A successful `step` supplies the next state, then the index advances by one.  Exit or a trap terminates that execution.  A zero count executes neither callback.  The callbacks are statically known code reflected with their captured values.  The native interpreter executes the loop, and the compiler emits a structured Wasm loop.  The proof uses natural indices, while the compiled counter stays in UInt64 and reaches `count` without wrapping.

An effectful helper may return `Unit`.  Its result occupies zero Wasm slots, and its unused result binding is erased by a checked equation.  [The result descriptor](../Verified/Wasi/Source.lean) and [result adapters](../Verified/Wasi/Results.lean) cover Unit and accepted value types.

### Reads, writes, and exit

`readSome` accepts zero capacity.  A zero-capacity request still calls `fd_read` with one zero-length iovec.  Stream hosts report EOF through empty success, while zero-capacity empty success supplies no EOF evidence.  The abstract host relation has no separate EOF state and permits later reads to observe more data.

A capacity above `2^32 - 1` returns errno `overflow` (61) and empty bytes before allocation or host I/O.  An address-space or allocator failure after a valid capacity follows the existing guest-trap mechanism.  It is distinct from a WASI errno.  The allocation theorem supplies sufficient-memory premises for a trap-free call.

A successful read returns an owned buffer containing exactly the reported bytes, with length at most the requested capacity.  On zero-byte success the wrapper releases any allocated buffer and returns empty bytes.  On errno it releases that buffer and returns the errno with empty bytes.  An error count supplied through guest memory is ignored.

A successful write returns the host's count, including a short or zero count.  The count is at most the supplied length.  Empty writes still call `fd_write`, so host errors remain observable.  A write error returns its errno and a count of zero.  That zero is a sentinel: `count` describes transferred bytes only when `errno = 0`.  The input buffer remains borrowed throughout either outcome.  Source code can compare `count` with `Bytes.size bytes` before proceeding.

`exit code` has terminal source semantics and no continuation.  It passes `code mod 2^32` as the `proc_exit` argument.  A returned command-entry status uses the same conversion.  The host may accept that request or fail.  Acceptance produces an exit with the exact narrowed status.  Failure produces a host-trap outcome and preserves prior effects.  The raw status of an accepted exit remains separate from its operating-system process status.  The narrowing rule defines the import argument for every UInt64 input.

### Byte operations

`Bytes` is an immutable value whose Lean meaning is a packed byte sequence.  Its native implementation wraps `ByteArray`.  Its public operations use UInt64 values:

| Declaration | Meaning |
|---|---|
| `Bytes.empty : Bytes` | The empty sequence. |
| `Bytes.size (bytes : Bytes) : UInt64` | Its length, exact under the representation's address-space bound. |
| `Bytes.get (bytes : Bytes) (index : UInt64) : UInt64` | The selected byte, zero-extended, or zero past the end. |
| `Bytes.build (count : UInt64) (element : UInt64 → UInt64) : Bytes` | A byte sequence whose element at `i` is the low eight bits of `element i`.  The callback obeys the existing first-order build restrictions. |
| `bytes![0, 65, 255]` | A constant sequence, with each literal checked to lie between 0 and 255 during elaboration. |

The logical length uses Nat where Lean's byte-sequence definitions require it.  Compiled counters, comparisons, API arguments, and returned lengths use UInt64.  Reflection proves their correspondence under the memory bound.  [Byte access](../Verified/Bytes/Get.lean) and [construction](../Verified/AlignedBytes.lean) have universal correctness rules.  Intermediate UInt8 conversions in those rules do not require a general UInt8 arithmetic dialect.

`ReadResult` flattens to an errno word and one byte value.  `WriteResult` is scalar.  The accepted field representation includes `Bytes`.  These records supply the operation results without extending sums to arbitrary heap-valued fields.

A nonempty byte literal produces an owned heap value when evaluated.  The compiler keeps its constant bytes in a protected data segment and copies them into that allocation.  Empty literals produce `(0, 0)`.  Repeated evaluations get separate owned roots.  Literal data remains protected across calls, and construction contributes its allocation and copy cost.

## Packed memory and the WASI ABI

### Byte ownership

A represented byte value has two Wasm values: a UInt64 allocation-root pointer `p` and a UInt64 logical length `n`.  Bytes begin at `p` and occupy consecutive addresses.  A nonzero root has the runtime's 48-byte header, count one, capacity at least `max(8, n)`, kind two, width one, and child mask zero.  Its full allocated region participates in separation and ownership.  [The byte representation](../Verified/Bytes/Basic.lean) states these fields and bounds.

New empty results use `(0, 0)`.  Incoming owned and borrowed empty values may also have a valid allocated root of length zero, matching the existing host allocator.  Cleanup tests the root and releases a nonzero owned root once.  Borrowed-byte separation and frame predicates protect the allocation header and capacity even when the logical length is zero.  A byte value exposes its allocation root and length through the representation API, while source code operates on `Bytes`.

Writes borrow their input.  Reads return a fresh owned root on nonempty success.  If an owned value has multiple live source uses, the compiler's mode and lifetime analysis preserves its owner until the last use.  Converting a borrowed byte value to an owned result copies its bytes.  Result construction, branch cleanup, unused results, and effectful helper returns use the same separation and last-use obligations as existing arrays.  [Owned copying](../Verified/Bytes/CopyOwned.lean) and [release](../Verified/Bytes/Release.lean) prove preservation of the caller's retained regions.

The [execution host](../tools/wasmtime-host.c) allocates raw packed bytes and passes byte values as pointer and length.  [The representation instance](../LeanExe/Pipeline/Bytes.lean) connects that ABI to owned and borrowed source bytes.  Host execution tests check the external allocator and argument handling.

For positive read capacity, the wrapper allocates the requested byte capacity.  A short read retains the root with the returned logical length.  Unused capacity stays private to the allocation.  Error and zero-byte paths release it.  A zero-capacity read uses `(0, 0)` as its empty writable range and needs no allocation.

### Imports and scratch

All imports use the module name `wasi_snapshot_preview1`.  The core-Wasm signatures are:

| Function index | Import | Signature |
|---|---|---|
| 0 | `fd_read` | `(i32, i32, i32, i32) → i32` |
| 1 | `fd_write` | `(i32, i32, i32, i32) → i32` |
| 2 | `proc_exit` | `(i32) → ()` |

For read and write the arguments are the fixed fd, the iovec pointer, one iovec, and the result-count pointer.  An iovec consists of a 32-bit buffer pointer and 32-bit byte count.  The count result occupies four bytes.  The wrapper zero-extends successful counts and errnos into UInt64 values.  Valid enum results are a host-ABI premise.

The scratch reservation is `[0, 16)`: the iovec at bytes 0 through 7, the count at bytes 8 through 11, and four padding bytes.  The wrapper initializes its metadata and count before calling the host.  Constant arrays begin at 4096, and byte literals follow them.  The allocator starts after the static data.

The layout preserves the pure program's constant-array addresses and places raw byte-literal data after those arrays.  The initial bump pointer starts beyond all static data, aligned to eight bytes.  The initial-memory proof includes that data and the current page cap.  These arrays occupy linear memory.  The application ABI's function table is a separate Wasm resource.

Before narrowing a nonempty byte range, the proof establishes `p < 2^32`, `n < 2^32`, and `p + n` within the active memory and its cap.  The read wrapper checks capacity at runtime.  Heap and representation bounds justify address and write-length narrowing.  Empty pointer zero with length zero is a valid range.  Host count results are read only on success, and the host assumptions bound them by the requested range.

The memory frame excludes scratch and, for a read, the newly allocated writable capacity.  A write frame excludes only scratch.  The host preserves allocator headers, globals, tables, memory caps, and every other guest region.  It returns control without invoking another guest export.  Calls into an instance are serialized.  These conditions make a single scratch reservation sufficient across repeated calls and separate instances.

## Observable semantics and host assumptions

### Command meaning

The command semantics relates a source environment and host world to a result, final world, and ordered event trace.  A normal return carries a value.  An accepted exit carries the narrowed status.  A host trap, including rejection of an exit request, carries its committed world and trap identity.  Bounded-loop execution repeats the body in source order and preserves every earlier event.  A separate prefix relation records completed events, the current world, and a residual command when a guest resource failure interrupts execution.

Events record host invocations: the operation, selected fd, requested bytes or capacity, returned errno and successful count, and committed transfer.  Pure computation and capacity rejection leave this trace unchanged.  Stdout and stderr events share one ordered trace.  The host world may map them to the same resource.  The model also permits stdin and output descriptors to alias.  Separate byte logs are useful derived observations but do not establish ordering across descriptors or model aliasing alone.

The abstract world and host-step relations specify the three operations.  [Observed host state](../Verified/Wasi/Observed.lean) adds an append-only joint event journal.  The universal theorem ranges over every satisfying host, with arbitrary input, output length, and permitted transfer partition.  Scripted worlds supply concrete semantic tests.

`Action` has this meaning through [its execution relation](../LeanExe/Wasi/Semantics.lean) and [prefix relation](../LeanExe/Wasi/Prefix.lean).  [The native interpreter](../LeanExe/Wasi/Interpreter.lean) executes actions through a stream or supplied adapter.  Adapter conformance to the abstract host assumptions is external to the compiler proof.  The older opaque `BaseIO` byte-I/O interface would need an explicit relation connecting its operations and state token to the command world.  Kernel-checked equations for `pure` and `bind` establish sequencing, while host assumptions establish transfers.

### Success, errors, and traps

The host specification combines ABI shape, transfer behavior, and the memory frame.  A successful stdin read supplies at most the requested bytes.  Its returned bytes match the writable prefix.  A successful output write commits the reported prefix of the supplied sequence.  The frame protects all guest resources outside the specified writable regions.

On errno, the model may record a committed prefix for the failed operation.  The count exposed by the wrapper remains the zero sentinel.  A read error may have consumed an input prefix and changed bytes within its discarded buffer.  A write error may have committed an output prefix.  Previously completed effects remain in the world and trace.  A stronger error guarantee would be an additional host assumption requiring its own evidence.  This prevents an undefined result-count slot from becoming a claim about device progress.

Host-trap outcomes also retain the world committed before the trap.  Frame conditions still protect unrelated guest memory.  Normal-return ownership postconditions apply after a return.  A host trap, resource trap, or exit ends the host's use of that instance.

Talos models host invocation through `HostEnv`, `HostSpec`, and `HostResult`, as pinned by [the dependency manifest](../lake-manifest.json).  `HostResult` has `Return`, `Trap`, and `Throw` outcomes.  The exit model uses a distinguished world field `exited : Option UInt64`.  Accepted exit records the narrowed status and produces the designated exit trap.  Exit failure produces a host trap and preserves the previous exit field and committed effects.  A host beginning a fresh lifecycle supplies a world with `exited = none`.  Read and write transitions preserve that field.  The accepted-exit theorem requires the designated outcome and recorded status.  An arbitrary trap message or a nonzero guest status cannot establish acceptance.  The host specification excludes ordinary return from `proc_exit` and thrown exceptions from all three operations.

The implementation uses a proof-side exit marker and exact trap identity in [the host assumptions](../Verified/Wasi/HostSpec.lean).  A future explicit exit outcome would require a Talos extension and a separate review.  Relating Wasmtime's accepted exits and exit failures to their modeled outcomes remains an external host assumption checked by execution tests.

## Module construction and compiler proofs

### Pure code in an importing module

Let the existing pure module contain `N` defined functions, including its allocator, release routine, depth entries, and wrappers.  The WASI module prefixes three imports and relocates those `N` definitions before appending the I/O wrappers and effectful functions.  [The layout maps](../Verified/Wasi/Wrappers.lean) give these positions:

| Item | Defined-function position | Absolute function index |
|---|---|---|
| Allocator | 0 | 3 |
| Release | 1 | 4 |
| Existing pure function at old position `k` | `k` | `3 + k` |
| First appended wrapper or effectful function | `N` | `3 + N` |
| Command `_start`, when requested | Last defined position | Three plus that position |

Function indices and type indices are separate mappings.  The layout reserves three type entries for the three imports, including duplicate read/write signatures, then relocates old type index `t` to `3 + t`.  Appended definitions receive type entries.  All calls, depth entries, wrapper calls, exports, and function-type annotations follow the layout maps.  [The validity generator](../Verified/Wasi/ReflectValidity.lean) constructs proofs of import signatures, instruction typing, and export bounds for the concrete module.  [The shared encoder](../LeanExe/Encoding/Modules.lean) and [encoding-domain conditions](../LeanExe/Encoding/Domain.lean) account for function imports.

The encoder and its [module grammar](../LeanExe/Encoding/Spec/Modules.lean) admit one empty nullable-function-reference table with minimum zero and the export `__indirect_function_table` at table index zero.  The table section and table-export entry have encoding, decoding, domain, validity, and round-trip rules.  The empty-table-list case retains the existing encoding scheme, and byte-for-byte preservation of the pure import-free corpus remains an integration gate.  Element segments and indirect calls remain outside this extension.

Existing [function renaming](../Verified/FunRelocation.lean) transports typed source functions and meaning, and the [module-composition rules](../Verified/ModuleComposition.lean) retain the import-free runtime layout.  WASI reuse adds [instruction relocation](../Verified/Wasi/Relocation.lean), [pure execution transport](../Verified/Wasi/PureTransportSpecs.lean), and [module transport](../Verified/Wasi/ModuleTransport.lean).

The transport keeps the pure universal theorem and establishes these properties:

1. Relocated pure code simulates the original code under the layout maps, preserving its data state, represented arguments and results, and resource outcome.  The relation accounts for function identities and any added table resources.
2. Every reachable pure call targets a relocated definition, including allocator and release calls.  It never reaches the three imports.
3. The store projection follows the layout relation and erases the host world.  It commutes with pure execution, and lifting its result preserves that world on returns and guest traps.
4. Appended definitions and the empty application-ABI table do not change pure execution.
5. Heap predicates and representation facts transport through that state relation, including the new byte predicates.

The proof covers an explicit pure instruction profile, including nested control flow and direct calls.  Profile closure excludes host and indirect calls.  [The relocated runtime rules](../Verified/Wasi/Runtime.lean) reuse allocator and release correctness through this transport.  The effect proof preserves both the host world and its ordered event journal across pure calls.

### Typed commands and reflection

The effect IR embeds typed pure expressions and has constructors for return, binding, conditionals, first-order effectful calls, bounded loops, the three stream operations, and exit.  Contexts record the types and ownership modes of live values.  Its result descriptor permits ordinary accepted values and erased Unit.  Read and write constructors invoke their transfer imports.  Exit emits the call to `proc_exit` followed by `unreachable`, which permits validation at any result type.  The host call terminates with a designated exit or a permitted host trap.

Compilation orders operand evaluation before its effect.  It materializes operation results before evaluating a continuation.  Cleanup uses liveness across both the operation and continuation.  An unused read result is still read and then released.  A borrowed write argument remains live through the WASI import call.  Branches and loop iterations carry the same ownership and caller-frame obligations as pure code.

The separate `verified_compile_wasi` command is provided by `import Verified.Wasi`.  `verified_compile_wasi p := [f₁, …, fₙ]` constructs a callable module.  `verified_compile_wasi p (main := main) := [f₁, …, fₙ]` constructs a command module whose selected entry is a closed `Action UInt64`.  The frontend collects pure definitions first, preserving their relative order, then reflects effects in their relative order.  Other listed callees precede callers within each group.  Pure helpers retain their self-recursion rules, while effectful helpers are acyclic.

The generated declarations include `p.module`, `p.initial`, each effectful function's `.related` and `.callee`, and the encoding and validity proofs.  Callable `.implements` and command `.start` run the exported wrappers, including injected depth and hidden tables.  Their `.exported` theorems identify the module exports.  Conditional `.total` theorems use typed resource-prefix and reached-host premises.  [The manual's declaration table](wasi.md#declarations) gives the exact public names and scope of `p.bytes`.

The reflector translates accepted Lean action definitions into this IR and proves `Action.Rel` after flattening accepted values.  [Execution transport](../LeanExe/Wasi/RelatedExec.lean) and [prefix transport](../LeanExe/Wasi/RelatedPrefix.lean) connect this relation to observable semantics.  The reflector recognizes the monad's `pure` and `bind`, supported control flow, and named API operations.  Unlisted inline helpers unfold.  Recursive effectful helpers and action values stored in runtime data require later designs.  A failed reflection proof rejects the program.

The universal compiler theorem is proved by command structure, using the pure transport theorem and wrapper execution lemmas.  It quantifies every concrete satisfying host and related initial state and supplies a sufficient fuel bound.  Each target execution at or above that bound returning a value, exiting, or reporting a permitted host trap has a matching source execution with the same ordered events, final world, and corresponding outcome.  The proof constructs that source path from the host's replies.  Nondeterministic specifications permit several paths.  Each target path must belong to that relation.

On normal return, values have the declared ownership, and retained caller regions keep their contents and separation.  A permitted guest resource trap matches a source prefix and residual command.  It preserves the effects already committed and remains distinct from exit.  Terminal outcomes require the host to discard the instance.

A separate total-execution theorem establishes a return or designated exit when `Heap.Within` supplies allocation room, `Resource.CallPrefixBound` bounds every typed resource prefix and establishes its size and depth checks, and `host.NoTrapsAlong` excludes reached host traps and exit rejection.  Returned errnos remain ordinary results.  Kernel-checked source-correspondence proofs specialize these statements to each reflected definition.  The general refinement theorem retains committed effects on host or guest resource failure.

## Lifecycle, bounds, and execution host

### Callable and command forms

A callable module exports every listed effectful function, `alloc`, `release`, `memory`, and the existing allocation counters.  Its instance persists across successful calls.  The pinned reactor ABI makes `_initialize` optional, and this implementation omits that hook.  Host code provides the three streams before invoking exports, serializes calls, and releases owned returned byte roots.  A returned errno permits another call.  An accepted exit, a host failure, or a guest trap ends the host's use of the instance.

A command module exports `_start : () → ()` and `memory`.  It calls a selected closed `Action UInt64` entry and sends its returned status to `proc_exit`.  Explicit exit inside that entry follows the same terminal path.  The host invokes `_start` once and discards the instance afterward.  Debug allocation-counter exports belong to the callable test form.  Both forms export an empty `__indirect_function_table` to follow the pinned application ABI.  Source operations in this design use no indirect function pointers.

[The initial-store theorem](../Verified/Wasi/ProgramInitial.lean) proves the allocator invariant, memory cap, borrowed constant tables, and static byte pool for the complete modeled module.  It preserves the supplied abstract host world.  Representation, consumed-block separation, and scratch separation remain call premises.  Real engine instantiation and OS-stream configuration remain external to that theorem.

### Resources and termination

The current allocator rounds a requested payload up to eight bytes, with a minimum of eight, and adds its 48-byte header.  A positive read's fresh-allocation charge is therefore `48 + 8 * max(1, ceil(capacity / 8))`, expressed with proof-side natural arithmetic.  A zero-capacity read and each write allocate no byte buffer.  Reuse can reduce the charge.  Copying, byte construction, pure calls, retained state, and call frames contribute their own proved charges.

The byte budget includes the allocation header and requested capacity rather than the short read's logical result length.  Cleanup makes released blocks available for reuse.  A memory bound must account for retained capacities throughout branches and loop iterations.

Each primitive read or write wrapper makes at most one WASI import call.  The host may use several operating-system calls to implement one import.  For the acyclic effect-call graph and bounded loops, termination follows from finite source control flow, terminating pure callees under their depth conditions, and return of each reached host call.  A blocked host call supplies no return-time guarantee.

The internal ABI gives every effectful function a hidden depth word and checks it against the existing limit of 1,000.  Calls to effectful helpers and depth-aware pure bodies receive the next depth.  Host-facing wrappers initialize the depth once.  Pure frames that take the depth retain the 32-position limit.  The compiler admits larger acyclic effectful frames under a checked call-chain estimate.  [The stack check](../Verified/Wasi/Stack.lean) includes guarded calls, pure-module frames, the three WASI wrappers, effectful-frame excess, and exported entries within 512 KiB.  This estimate is a compiler admission condition.  Real engine stack layout remains an external assumption.  The typed resource-prefix condition separately accounts for the combined call path.  Pure functions whose code takes no depth retain their existing ABI.

A process may run to EOF without an iteration bound.  [The process compiler](../Verified/Wasi/ProcessCode.lean) places bounded begin and step functions inside an unbounded `_start` loop.  Begin and each completed step return an owned state, which the loop then compacts: it copies the state above the heap's top and moves the copy down to the heap's base, the heap top when `_start` began.  The process theorems require a state type without trees, `entry.state.compactable = true`, and an initial heap with an empty free list.  [The process refinement theorem](../Verified/Wasi/ProcessCorrect.lean) preserves completed steps and resource-failure prefixes for every target execution that completes without exhausting Talos fuel.  [The total-process theorem](../Verified/Wasi/ProcessTotalCorrect.lean) uses an application-supplied well-founded progress relation, a charge for the cost of begin and of each step with room for the copies of the state before and after it, and final-exit acceptance.

[Running sum's compiled integer theorem](../Demos/RunningSum/Correct.lean) proves canonical cumulative integer output for the lines before the first line that is not a decimal integer, and eventual accepted exit with status 0 when every line is one and 28 otherwise.  [Its stream-host relation](../Demos/StreamFold/StreamHost.lean) requires successful I/O, input-prefix consumption, EOF, committed output prefixes, and a decreasing proof-only credit for zero-byte writes.  [The input-size bounds](../Demos/RunningSum/Model.lean) constrain each line's length and the digit count of each prefix sum of valid lines independently of the total input length.  Limits on the bytes of each line and the digits of each total, `InputLimits L D`, and one inequality between the memory cap and `220 · (L + D) + 1,010,000` bytes above the literal pool replace the allocation premises: the theorem proves the typed allocation-prefix charges of begin and of each step from the generated bounds of the pure functions, at the states that an invariant of the run admits.  `ExitAccepted` excludes rejected final exits.  The mathematical `Nat`/`Int` values and progress ranks are proof-only.  Executable digits, lengths, indices, counts, and statuses use `UInt64`.

[The binary64 running sum](../Demos/RunningSumFp/README.md) uses the same stream protocol with a `Float` accumulator starting at positive zero.  It composes the existing general float parser, IEEE-754 addition, and shortest scientific printer.  [Its compiled theorem](../Demos/RunningSumFp/Correct.lean) identifies the stdout bytes of every sequential rounded prefix before the first line that denotes no number and proves accepted exit with status 0 or 28.  Premises include fewer than `2^32` bytes per line, stream-host progress, a limit `L` on the bytes of each line up to and including the first line that denotes no number, one inequality between the memory cap and `80 · L + 64,031,000` bytes above the heap's base, and final-exit acceptance.  The theorem proves the allocation charges of begin and of each step from the generated bounds of the parser, the printer, and the effect bodies.  [The shared stream proofs](../Demos/StreamFold/README.md) separate accumulator arithmetic and line rejection from byte consumption, short writes, EOF, and well-founded process termination.

Pure calls also need the generated binding of constant tables.  An internal call supplies those hidden table arguments and any depth argument to the relocated body, directly or through a proved depth-preserving wrapper.  Its source-correspondence and bound proofs compose the table binding with the body theorem.  Exported wrappers that initialize depth are reserved for host entry.  The mixed-call tests include table-using pure callees under effectful helpers and calls at the combined depth boundary.

The effect theorem records allocation and depth requirements along an execution path.  A caller proves an upper bound for all permitted resource prefixes and uses it for total execution.  Read lengths are bounded by their requests, which supports such bounds for byte processing.  Pure fragments use the pure compiler's allocation bounds.  The public frontend exposes the typed prefix condition rather than synthesizing an input-only bound for every I/O program.  Such a bound must account for host-dependent branches, result lengths, retained byte roots, and cleanup across loop iterations.

### Wasmtime integration

The host uses the repository's pinned Wasmtime 44.0.0 C API, configured through `wasi_config_t`, `wasmtime_context_set_wasi`, and `wasmtime_linker_define_wasi`.  It inherits or redirects stdin, stdout, and stderr through the standard WASI configuration.  The [download pin](../tools/download-wasmtime.sh), [host build](../tools/build-wasmtime-host.sh), and [canonicalizing engine setup](../tools/wasmtime-host.c) define the tested embedding.  The host resolves the three imports through the standard linker.

The host configures guest stdin, stdout, and stderr through inheritance or explicit file redirection.  Execution tests redirect guest output to separate capture files and send returned values, allocation counts, and terminal records to control outputs, while host diagnostics go to host stderr.  This preserves guest bytes for exact comparisons.  Interactive command mode inherits stdio.  After an engine failure, it reports the error on host stderr and returns a failure status.

The pinned [exit-code type](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/typenames.witx#L605-L606) is `u32`.  The [exit declaration](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/wasi_snapshot_preview1.witx#L426-L432) marks `proc_exit` as nonreturning and leaves nonzero meanings to the environment.  [Wasmtime 44's implementation](https://github.com/bytecodealliance/wasmtime/blob/v44.0.0/crates/wasi/src/p1.rs#L2614-L2625) accepts statuses below 126 and rejects 126 or above as an engine error.  This range concerns the narrowed argument: `2^32 + 7` requests accepted status 7, while `2^32 + 126` requests rejected status 126.

The host identifies accepted exits through [`wasmtime_error_exit_status`](https://github.com/bytecodealliance/wasmtime/blob/v44.0.0/crates/c-api/src/error.rs#L52-L62).  Its control output records the accepted unsigned 32-bit status, and its process status uses the low eight bits.  Exit rejection receives the engine-error diagnostic and process status 1, with no accepted exit record.  Captured guest output remains available after either terminal outcome, and the host discards the instance.

The [native stream adapter](../LeanExe/Wasi/Interpreter.lean) reports full count after a successful write and flush and accepts every narrowed exit status as an `Outcome.exited` returned to Lean.  Stream `IO.Error`s propagate.  This policy differs from Wasmtime's status restriction and one-import transfer behavior.

Lean's kernel checks the compiler and byte proofs against Talos and the specified host relations.  Wasmtime, the C compiler, OS streams, native adapter conformance, and real host progress remain external assumptions tested by execution.  Standard WASI linking supplies compatibility with the selected ABI.

## Implementation and acceptance

The implementation separates native APIs from compiler developments:

| Location | Responsibility |
|---|---|
| [Native bytes](../LeanExe/Dialect/Bytes.lean) | Native byte values, UInt64 operations, and literals. |
| [Native actions](../LeanExe/Wasi) | The three stream APIs, exit, bounded loops, processes, observable semantics, and native interpreter. |
| [Byte compilation](../Verified/Bytes) | Byte representation, ownership, lowering, and proofs. |
| [WASI compilation](../Verified/Wasi) | Host assumptions, typed command IR, module layout, compiler, wrapper proofs, and reflector. |

The pure typed source and compiler include byte operations and the literal-pool context.  An empty pool preserves the previous compilation, and the integration gate compares the old pure outputs byte for byte.

| Stage | Implemented proof boundary | Source |
|---|---|---|
| 1 | Reviewed API, byte layout, host-error relation, exit behavior, and reuse plan. | [Review decisions](#review-decisions). |
| 2 | Packed bytes, ownership, copying, release, access, construction, and literals. | [Byte representation](../LeanExe/Pipeline/Bytes.lean), [byte construction](../Verified/AlignedBytes.lean), and [literal correctness](../Verified/Bytes/Literal.lean). |
| 3 | Import relocation, host-state preservation, and empty-table encoding and validity. | [Module transport](../Verified/Wasi/ModuleTransport.lean), [module grammar](../LeanExe/Encoding/Spec/Modules.lean), and [validity rules](../LeanExe/Encoding/Spec/Validity.lean). |
| 4 | Universal one-iovec read and write wrappers with scratch framing. | [Read execution](../Verified/Wasi/ReadFunction.lean) and [write execution](../Verified/Wasi/Write.lean). |
| 5 | Universal safety and cost-aware compilation for commands, calls, branches, and bounded loops. | [Command safety](../Verified/Wasi/CommandCorrect.lean), [command cost correctness](../Verified/Wasi/CostCommandCorrect.lean), and [program correctness](../Verified/Wasi/Correct.lean). |
| 6 | Native source correspondence, callable and `_start` execution, modeled initial store, and encoded-module proofs. | [Callable entry](../Verified/Wasi/NativeEntry.lean), [command entry](../Verified/Wasi/NativeCommand.lean), [initial store](../Verified/Wasi/ProgramInitial.lean), and [public frontend](../Verified/Wasi/ReflectCommand.lean). |
| 7 | Standard Wasmtime embedding and maintained proof and execution gates. | [Native host](../tools/wasmtime-host.c), [WASI driver](../tests/wasi/run.sh), [verified compiler driver](../tests/verified/run.sh), and [full repository checks](leanexe-manual.md#the-full-check). |
| 8 | Unbounded process refinement and conditional total execution, with integer and binary64 running-sum output and accepted exit with status 0 or 28. | [Process refinement](../Verified/Wasi/ProcessCorrect.lean), [total-process theorem](../Verified/Wasi/ProcessTotalCorrect.lean), [integer correctness](../Demos/RunningSum/Correct.lean), and [binary64 correctness](../Demos/RunningSumFp/Correct.lean). |

The write theorem quantifies arbitrary borrowed bytes, initial worlds, and satisfying hosts.  It proves the reported prefix on success, the declared error relation, preserved input bytes and caller regions outside scratch, and returned UInt64 status/count.  It includes empty and zero-progress success.  The read theorem quantifies capacity and host replies, proves exact returned bytes and ownership, and proves cleanup on errno and zero-byte success.  Fixed echo executions supplement these theorems.

| Test or proof group | Cases and acceptance condition |
|---|---|
| ABI and decoding | Exact three imports and signatures, correct export/type/function indices, the empty function-table section and export, valid one-iovec layout, zero and maximum-width counts, justified narrowing, round-trip decoding, and generated-byte theorems connecting the encoding to the compiled module and native refinements.  Invalid table types and export indices fail the profile checks.  File writing remains external to these theorems. |
| Host-model execution | Arbitrary short reads/writes, zero progress, positive-capacity EOF, zero-capacity reads, errnos with permitted committed prefixes, accepted exit, exit rejection, and a foreign host trap.  The joint trace preserves stdout/stderr order and permits descriptor aliasing. |
| Ownership and memory | Discarded reads, returned reads, read error, EOF, allocated-empty owned and borrowed inputs, retained aliases, branch and loop cleanup, untouched scratch-adjacent bytes, and retained caller regions.  Normal returns leave exactly the expected roots allocated. |
| Source reflection | Discarded effect results still execute, named actions execute once per sequencing, helper calls, Unit results, conditionals, bounded loops, byte access/build, and rejection of unsupported action escape. |
| Native execution | Binary input including 0 and 255, stdout and stderr, EOF, missing/failing streams, and repeated callable calls.  Host fixtures check accepted statuses 0, 7, and 125, rejected requests 126, 256, and `2^32 - 1`, and low-32-bit argument conversion.  Exit rejection preserves prior output, and every terminal outcome prevents later calls.  Native expectations account for the counts the standard host returns. |
| Proof audit | Universal compiler, wrapper, transport, ownership, initial-store, source-correspondence, generated-byte, and validity theorems use only `propext`, `Classical.choice`, and `Quot.sound`. |
| Existing compiler outputs | Exact bytes for the pure import-free corpus, and successful execution, allocation, numerical, WGSL, and GPT32 integration gates. |

Scripted host models supply deterministic partial-transfer and failure cases.  Native tests exercise standard Wasmtime behavior without assuming that it returns every permitted short-write count.  Test-driver time limits bound blocked tests without adding a guest deadline API.

[The maintained WASI driver](../tests/wasi/run.sh) invokes the repository runner and checks its registered examples, native executions, decoding, and theorem axioms.  [The verified test driver](../tests/verified/run.sh) and [full-check procedure](leanexe-manual.md#the-full-check) remain integration gates for shared compiler changes.  All Lean runs obey [the repository limits](../AGENTS.md).

### Review decisions

| Decision | Approved choice | Alternative and consequence |
|---|---|---|
| Zero-capacity read | One `fd_read` import call with a zero-length iovec.  EOF inference requires positive capacity. | Return `INVAL` before I/O, adding a source validation rule. |
| Exit UInt64 to WASI u32 | Explicit low-32-bit conversion for direct exit and command return. | A checked exit-code type adds source representation work.  Trapping on overflow adds a guest failure path. |
| Exit acceptance | Standard host linking with accepted-exit and terminal host-failure outcomes.  A guarantee of return or designated exit requires host acceptance of every reached exit request. | A custom callback accepting every UInt32 changes embedding policy and exit classification. |
| Bytes | A single allocation root plus logical UInt64 length. | A length-prefixed, one-pointer object changes the existing byte host ABI and access proofs. |
| Read result | An errno-and-bytes record, empty on error. | A heap-valued sum requires a broader accepted sum representation. |
| Host errors | Permit the declared current-operation prefix and preserve prior effects.  Count is valid on success. | An unchanged-world error rule needs a stronger host guarantee. |
| Pure proof reuse | Prove import relocation and host-state execution transport, then compose. | Generalize shared compiler rules where the transport proof demonstrates a need. |
| Source monad | A semantic `Action` with checked reflection equations. | Opaque BaseIO primitives require an additional primitive/state correspondence. |
| Frontend | A separate `verified_compile_wasi` command, with an optional command entry. | Inferring an effect profile in `verified_compile` changes that command's accepted types and output selection. |
| Native API placement | Compiler-independent `LeanExe.Bytes` and `LeanExe.Wasi` modules. | Compiler-specific source APIs couple consumers to one compiler's namespace and module organization. |
| Effectful control flow | Bounded loops and an acyclic helper graph for the initial implementation. | Unbounded structured loops require a general trace-prefix theorem and separate termination premises. |
| Depth accounting | Share the existing guarded-call depth through effectful and pure internal calls. | Independent counters require a combined frame bound to justify their interaction. |
| Application-ABI table | Add the narrow empty-table encoding profile and export required by the pinned convention. | A three-import profile without that export reduces proof work but departs from the pinned application-ABI convention. |
