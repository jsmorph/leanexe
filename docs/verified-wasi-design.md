# Verified compiler: WASI Preview 1 design

Status: implementation in progress.  The user directed implementation of this reviewed agenda on minideb1.  The initial scope is WASI Preview 1 over core WebAssembly, stdin reads, stdout and stderr writes, and process exit.  The API uses ordinary Lean `do` notation and follows the compiler's UInt64 convention for executable lengths, counts, and statuses.  The recommendations in the review table guide implementation.  The library reorganization is merged into `main` at `ba466061`.  This work uses `verified-wasi`, with an isolated checkout on minideb1.

## Scope and sources

The initial host interface consists of `fd_read`, `fd_write`, and `proc_exit` in `wasi_snapshot_preview1`.  Source operations select stdin 0, stdout 1, or stderr 2.  A program can compute between operations, inspect errors and short transfers, and return or exit.  Later work may add other Preview 1 operations and library retry policies.

The specification pin is WebAssembly/WASI commit `fae981bae14809d91f9bc2d63852d461f331d161`.  Its [interface definitions](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/wasi_snapshot_preview1.witx), [type definitions](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/typenames.witx), [generated reference](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/docs.md), and [application ABI](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/application-abi.md) are the external references.  A future specification update requires review of the ABI, host assumptions, and proof statements.

The [current typed source](../Verified/Source.lean) has pure value semantics.  The [compiler](../Verified/Compile.lean) emits an import-free module, and its [runtime predicate](../Verified/RuntimeFacts.lean) requires that layout.  The [correctness theorem](../Verified/Correct.lean) and [representation API](../LeanExe/Pipeline/Implements.lean) use `Store Unit`.  This design adds an effect language and proves its connection to host-dependent execution.

### Earlier implementations

Two earlier branches provide implementation and proof examples:

| Revision | Existing work | Reuse and remaining obligations |
|---|---|---|
| `io` at `6a92d7a09cce3861bc9adc0b64e6b3b164047c2b` | The [byte-I/O proof inventory](https://github.com/jsmorph/leanexe/blob/6a92d7a09cce3861bc9adc0b64e6b3b164047c2b/proofs/byte-io/README.md) covers syscall models, an abstract write protocol, and six concrete echo executions. | Adapt the examples to the current allocator and ownership layout.  Universal execution proofs for the emitted read/write routines remain required. |
| `wasi` at `efbd253c74c0e4b7dd8d74ea3bb48b12276f3e28` | The [native API](https://github.com/jsmorph/leanexe/blob/efbd253c74c0e4b7dd8d74ea3bb48b12276f3e28/LeanExe/Wasi.lean) exposes all 46 Preview 1 functions through opaque BaseIO operations.  Its [manual](https://github.com/jsmorph/leanexe/blob/efbd253c74c0e4b7dd8d74ea3bb48b12276f3e28/docs/wasi.md) describes direct native lowering, one-iovec transfers, packed ByteArrays, and 38 execution cases. | Review its wrapper layouts, effect sequencing, cleanup, and test cases against the current runtime.  The [checkpoint](https://github.com/jsmorph/leanexe/blob/efbd253c74c0e4b7dd8d74ea3bb48b12276f3e28/task.md) records incomplete full proof gates.  Verified transport, wrapper, and universal effect proofs remain required. |

The earlier native WASI API uses `Action := BaseIO`, UInt32 descriptors, capacities, counts, errnos, and exit codes, and `Except UInt32 ByteArray` read results.  Its byte representation has owner, pointer, and length values.  This proposal uses a semantic command monad, UInt64-facing operations, explicit result records, and one root plus length.  Both APIs use the proposed name `LeanExe.Wasi.Action`; they cannot coexist unchanged.  The implementation review must settle public API compatibility before importing earlier source.  Its wider operation set remains outside the initial scope.

The earlier [direct wrappers](https://github.com/jsmorph/leanexe/blob/efbd253c74c0e4b7dd8d74ea3bb48b12276f3e28/LeanExe/Wasm/Wasi.lean) provide the closest lowering reference: one iovec, errno checks before count reads, cleanup of failed or empty reads, and partial-transfer preservation.  Its emitter imports the full primitive registry and emits command modules.  The proposed three-import layout and callable form require new construction.  Its [effect analysis](https://github.com/jsmorph/leanexe/blob/efbd253c74c0e4b7dd8d74ea3bb48b12276f3e28/LeanExe/IR/Effects.lean) identifies effectful code but supplies no trace semantics or compiler correctness theorem.

## Lean API and behavior

### Actions and results

The proposed public namespace is `LeanExe.Wasi`.  Native API modules import Lean's data types and the required dialect operations.  Their definitions remain independent of either compiler.  The shared byte type is `LeanExe.Bytes`, with its native operations under `LeanExe/Dialect/Bytes.lean`.  Compiler representations and proofs live under `Verified`.

`Action α` is a semantic command monad with Lean `pure` and `bind` instances.  The accepted source uses ordinary `do`, named first-order helpers, bindings, conditionals, pure Verified calls, and the bounded loop below.  Effectful helper calls form an acyclic call graph in the proposed initial version.  Pure callees retain their existing recursion and allocation conditions.  These control-flow restrictions are review choices.

| Proposed declaration | Meaning |
|---|---|
| `readSome (capacity : UInt64) : Action ReadResult` | One stdin read after capacity validation and any required allocation. |
| `writeStdoutSome (bytes : Bytes) : Action WriteResult` | One stdout write, borrowing `bytes`. |
| `writeStderrSome (bytes : Bytes) : Action WriteResult` | One stderr write, borrowing `bytes`. |
| `exit (code : UInt64) : Action α` | Terminate with the low 32 bits of `code` as the WASI exit status. |
| `loop (count : UInt64) (init : σ) (test : UInt64 → σ → Bool) (step : UInt64 → σ → Action σ) : Action σ` | At most `count` iterations, carrying a state of an accepted runtime value type. |
| `ReadResult` | A record with `errno : UInt64` and `bytes : Bytes`. |
| `WriteResult` | A record with `errno : UInt64` and `count : UInt64`. |

Zero errno denotes success.  Error results remain ordinary values: the source decides whether to return, exit, continue, or report an error.  Sequencing an action executes it once even if its result is discarded.  A pure binding such as `let action := readSome n` names a description.  A monadic binding such as `let result ← action` executes it.  Sequencing the same named action twice performs two calls.

Native action descriptions and continuations can be constructed as the native interpreter runs.  Reflection translates accepted definitions into fixed typed code.  It performs no guest I/O.  Compiled runtime values have the compiler's value types, including the proposed byte type and result records.  The host world belongs to the semantics and host state rather than the source program's arguments.

`loop` is a command-description node.  It starts with index zero and `init`.  Before each iteration it tests the index against `count`, then evaluates the pure `test` on the index and current state.  Reaching the count or a false test returns the current state.  A successful `step` supplies the next state, then the index advances by one.  Exit or a trap terminates that execution.  A zero count executes neither callback.  The callbacks are statically known code reflected with their captured values.  The native interpreter executes the loop, and the compiler emits a structured Wasm loop.  The proof uses natural indices, while the compiled counter stays in UInt64 and reaches `count` without wrapping.

An effectful helper may return `Unit`.  Its result occupies zero Wasm slots, and its unused result binding is erased by a checked equation.  This requires an effect-result representation rule.

### Reads, writes, and exit

`readSome` accepts zero capacity.  A zero-capacity request still calls `fd_read` with one zero-length iovec.  Empty success indicates EOF only when the requested capacity was positive.  EOF is an observation of that call.  The model permits a later read to observe additional data if the host's stdin resource permits it.

A capacity above `2^32 - 1` returns errno `overflow` (61) and empty bytes before allocation or host I/O.  An address-space or allocator failure after a valid capacity follows the existing guest-trap mechanism.  It is distinct from a WASI errno.  The allocation theorem supplies sufficient-memory premises for a trap-free call.

A successful read returns an owned buffer containing exactly the reported bytes, with length at most the requested capacity.  On zero-byte success the wrapper releases any allocated buffer and returns empty bytes.  On errno it releases that buffer and returns the errno with empty bytes.  An error count supplied through guest memory is ignored.

A successful write returns the host's count, including a short or zero count.  The count is at most the supplied length.  Empty writes still call `fd_write`, so host errors remain observable.  A write error returns its errno and a count of zero.  That zero is a sentinel: `count` describes transferred bytes only when `errno = 0`.  The input buffer remains borrowed throughout either outcome.  Source code can compare `count` with `Bytes.size bytes` before proceeding.

`exit code` has terminal source semantics and no continuation.  The explicit conversion is `code mod 2^32`.  A returned command-entry status uses the same conversion.  The formal theorem records the WASI status.  An operating system or shell may expose a narrower process status.

The low-bit rule gives every UInt64 argument defined exit behavior and matches Lean's unsigned narrowing operation.

### Byte operations

`Bytes` is an abstract immutable value whose Lean meaning is a packed byte sequence.  Its native implementation can wrap `ByteArray`.  Its public operations use UInt64 values, with these initial semantics:

| Proposed declaration | Meaning |
|---|---|
| `Bytes.empty : Bytes` | The empty sequence. |
| `Bytes.size (bytes : Bytes) : UInt64` | Its length, exact under the representation's address-space bound. |
| `Bytes.get (bytes : Bytes) (index : UInt64) : UInt64` | The selected byte, zero-extended, or zero past the end. |
| `Bytes.build (count : UInt64) (element : UInt64 → UInt64) : Bytes` | A byte sequence whose element at `i` is the low eight bits of `element i`.  The callback obeys the existing first-order build restrictions. |
| Checked byte-literal syntax | A constant sequence, with each literal checked to lie between 0 and 255 during elaboration. |

The logical length uses Nat where Lean's byte-sequence definitions require it.  Compiled counters, comparisons, API arguments, and returned lengths use UInt64.  Reflection proves their correspondence under the memory bound.  Byte construction and access get proved rules of their own.  Intermediate UInt8 conversions in those rules do not require a general UInt8 arithmetic dialect.

`ReadResult` flattens to an errno word and one byte value.  `WriteResult` is scalar.  These layouts require extending the accepted field representation for `Bytes`; they avoid making arbitrary heap-valued sums a prerequisite.

A nonempty byte literal produces an owned heap value when evaluated.  The compiler may keep its constant bytes in a protected data segment and copy them into that allocation.  Empty literals produce `(0, 0)`.  Repeated evaluations get separate owned roots.  Literal data remains protected across calls, and construction contributes its allocation and copy cost.

## Packed memory and the WASI ABI

### Byte ownership

A represented byte value has two Wasm values: a UInt64 allocation-root pointer `p` and a UInt64 logical length `n`.  Bytes begin at `p` and occupy consecutive addresses.  A nonzero root has the runtime's 48-byte header, count one, capacity at least `n`, and child mask zero.  Its full allocated region participates in separation and ownership.  Header-kind and auxiliary fields follow the current allocator's initialization unless a later proved byte allocator changes them.

New empty results use `(0, 0)`.  Incoming owned and borrowed empty values may also have a valid allocated root of length zero, matching the existing host allocator.  Cleanup tests the root and releases a nonzero owned root once.  Borrowed-byte separation and frame predicates protect the allocation header and capacity even when the logical length is zero.  A byte value exposes its allocation root and length through the representation API, while source code operates on `Bytes`.

Writes borrow their input.  Reads return a fresh owned root on nonempty success.  If an owned value has multiple live source uses, the compiler's mode and lifetime analysis preserves its owner until the last use.  Converting a borrowed byte value to an owned result copies its bytes.  Result construction, branch cleanup, unused results, and effectful helper returns need the same separation and last-use obligations as existing arrays.  Byte-copy and release rules must prove preservation of the caller's retained regions.

The [current execution host](../tools/wasmtime-host.c) already allocates raw packed bytes and passes byte values as pointer and length.  That code can support tests of this representation.  A Verified byte-representation instance and lifetime theorem remain required.

For positive read capacity, the wrapper allocates the requested byte capacity.  A short read retains the root with the returned logical length.  Unused capacity stays private to the allocation.  Error and zero-byte paths release it.  A zero-capacity read uses `(0, 0)` as its empty writable range and needs no allocation.

### Imports and scratch

All imports use the module name `wasi_snapshot_preview1`.  The core-Wasm signatures are:

| Function index | Import | Signature |
|---|---|---|
| 0 | `fd_read` | `(i32, i32, i32, i32) → i32` |
| 1 | `fd_write` | `(i32, i32, i32, i32) → i32` |
| 2 | `proc_exit` | `(i32) → ()` |

For read and write the arguments are the fixed fd, the iovec pointer, one iovec, and the result-count pointer.  An iovec consists of a 32-bit buffer pointer and 32-bit byte count.  The count result occupies four bytes.  The wrapper zero-extends successful counts and errnos into UInt64 values.  Valid enum results are a host-ABI premise.

The proposed scratch reservation is `[0, 16)`: the iovec at bytes 0 through 7, the count at bytes 8 through 11, and four padding bytes.  The wrapper initializes its metadata and count before calling the host.  Scratch remains below the heap base of 4096.  The table writer and byte literals must preserve this reservation.

The layout preserves the pure program's constant-array addresses and places raw byte-literal data after those arrays.  The initial bump pointer starts beyond all static data, aligned to eight bytes.  The initial-memory proof includes that data and the current page cap.  These arrays occupy linear memory.  The application ABI's function table is a separate Wasm resource.

Before narrowing a nonempty byte range, the proof establishes `p < 2^32`, `n < 2^32`, and `p + n` within the active memory and its cap.  UInt64 arithmetic for those checks cannot wrap.  Empty pointer zero with length zero is a valid range.  Host count results are read only on success and must lie within the requested range.  A defensive count check may trap on a host violation, but the proof uses the stated host condition rather than such a check to justify a conforming run.

The memory frame excludes scratch and, for a read, the newly allocated writable capacity.  A write frame excludes only scratch.  The host preserves allocator headers, globals, tables, memory caps, and every other guest region.  It returns control without invoking another guest export.  Calls into an instance are serialized.  These conditions make a single scratch reservation sufficient across repeated calls and separate instances.

## Observable semantics and host assumptions

### Command meaning

The command semantics relates a source environment and host world to a result, final world, and ordered event trace.  A normal return carries a value.  Exit carries the narrowed status.  A host trap carries its committed world and trap identity.  Bounded-loop execution repeats the body in source order and preserves every earlier event.  A separate prefix relation records completed events, the current world, and a residual command when a guest resource failure interrupts execution.

Events record host invocations: the operation, selected fd, requested bytes or capacity, returned errno and successful count, and committed transfer.  Pure computation and capacity rejection leave this trace unchanged.  Stdout and stderr events share one ordered trace.  The host world may map them to the same resource.  The model also permits stdin and output descriptors to alias.  Separate byte logs are useful derived observations but do not establish ordering across descriptors or model aliasing alone.

The abstract world and host-step relations specify the three operations.  A finite scripted world supplies executable examples.  The universal theorem ranges over every host satisfying those relations, with no fixed input string, output length, or transfer partition.

`Action` has this meaning through its constructors, pure expressions, and composition rules.  A native Lean interpreter may execute actions through a host adapter.  The correctness statement for that adapter is separate.  The older [opaque BaseIO interface](https://github.com/jsmorph/leanexe/blob/6a92d7a09cce3861bc9adc0b64e6b3b164047c2b/LeanExe/ByteIO.lean) supplies no observable meaning from its type alone.  If a later compatibility layer accepts it, an explicit relation must connect its opaque operations and state token to the command world.  Kernel-checkable equations for `pure` and `bind` establish sequencing, while primitive I/O assumptions establish transfers.

### Success, errors, and traps

The host specification combines ABI shape, transfer behavior, and the memory frame.  A successful stdin read supplies at most the requested bytes.  Its returned bytes match the writable prefix.  A successful output write commits the reported prefix of the supplied sequence.  The frame protects all guest resources outside the specified writable regions.

On errno, the model may record a committed prefix for the failed operation.  The count exposed by the wrapper remains the zero sentinel.  A read error may have consumed an input prefix and changed bytes within its discarded buffer.  A write error may have committed an output prefix.  Previously completed effects remain in the world and trace.  A stronger error guarantee would be an additional host assumption requiring its own evidence.  This prevents an undefined result-count slot from becoming a claim about device progress.

Host-trap outcomes also retain the world committed before the trap.  Frame conditions still protect unrelated guest memory.  Normal-return ownership postconditions apply after a return.  A host trap, resource trap, or exit ends the host's use of that instance.

Talos models host invocation through `HostEnv`, `HostSpec`, and `HostResult`, as pinned by [the dependency manifest](../lake-manifest.json).  `HostResult` has `Return`, `Trap`, and `Throw` outcomes.  The exit model therefore uses a distinguished world field `exited : Option UInt64` and an exact nonreturning `proc_exit` condition: it records the narrowed status and produces the designated exit trap.  Initial worlds have `exited = none`.  Read and write transitions preserve that field.  The exit theorem requires the exit call's designated outcome and recorded status.  An arbitrary trap message or a nonzero guest status cannot establish exit.  The three-operation host specification excludes thrown exceptions.

This design can use a proof-side exit marker and exact trap identity without changing Talos's outcome type.  A future explicit exit outcome would require a Talos extension and a separate review.  The real Wasmtime exit-status result is related to the modeled exit through the external host assumptions and execution tests.

## Module construction and compiler proofs

### Pure code in an importing module

Let the existing pure module contain `N` defined functions, including its allocator, release routine, depth entries, and wrappers.  The WASI module prefixes three imports and preserves those `N` definitions before appending the I/O wrappers and effectful functions.  The proposed placement is:

| Item | Defined-function position | Absolute function index |
|---|---|---|
| Allocator | 0 | 3 |
| Release | 1 | 4 |
| Existing pure function at old position `k` | `k` | `3 + k` |
| First appended wrapper or effectful function | `N` | `3 + N` |
| Command `_start`, when requested | Last defined position | Three plus that position |

Function indices and type indices are separate mappings.  The simple initial layout reserves three type entries for the three imports, including duplicate read/write signatures, then relocates old type index `t` to `3 + t`.  Appended definitions receive checked type entries.  All calls, depth entries, wrapper calls, exports, and function-type annotations follow the layout maps.  The module's validity theorem establishes import signatures, call signatures, and export bounds.  The [shared encoder](../LeanExe/Encoding/Modules.lean) and [encoding-domain conditions](../LeanExe/Encoding/Domain.lean) already account for function imports.

The encoder and its [module grammar](../LeanExe/Encoding/Spec/Modules.lean) currently require empty table and table-export lists.  The proposed application-ABI table therefore requires an encoding extension.  Its initial profile admits one empty nullable-function-reference table with minimum zero and the export `__indirect_function_table` at table index zero.  It adds the table section and table-export entry to the encoder, decoder, encoding domain, validity conditions, and round-trip proofs.  The existing import-free profile keeps its exact bytes.  Element segments and indirect calls remain outside this extension.

The current [function renaming](../Verified/FunRelocation.lean) transports typed source functions and meaning.  The [module-composition rules](../Verified/ModuleComposition.lean) retain the import-free runtime layout.  Neither supplies the required target execution transport.  Existing store-map and host-lifting helpers in Talos likewise require an execution theorem before they can transport compiler correctness.

The proposed reuse route keeps the pure universal theorem and proves a module-level transport.  Its obligations are:

1. Relocated pure code simulates the original code under the layout maps, preserving its data state, represented arguments and results, and resource outcome.  The relation accounts for function identities and any added table resources.
2. Every reachable pure call targets a relocated definition, including allocator and release calls.  It never reaches the three imports.
3. The store projection follows the layout relation and erases the host world.  It commutes with pure execution, and lifting its result preserves that world on returns and guest traps.
4. Appended definitions and the empty application-ABI table do not change pure execution.
5. Heap predicates and representation facts transport through that state relation, including the new byte predicates.

The proof covers the instruction subset emitted by the pure compiler, including nested control flow and every call form it emits.  The first proof stage must establish this transport for allocator calls and a byte-processing function before I/O commands depend on it.  Shared rules expose the host-state and placement parameters that the transport proof requires.

### Typed commands and reflection

The effect IR embeds typed pure expressions and has constructors for return, binding, conditionals, first-order effectful calls, bounded loops, the three stream operations, and exit.  Contexts record the types and ownership modes of live values.  Its result descriptor permits ordinary accepted values and erased Unit.  Read and write constructors invoke their transfer imports.  Exit emits the call to `proc_exit` followed by `unreachable`, which permits validation at any result type.  The conforming host produces the designated exit outcome at the call.

Compilation orders operand evaluation before its effect.  It materializes operation results before evaluating a continuation.  Cleanup uses liveness across both the operation and continuation.  An unused read result is still read and then released.  A borrowed write argument remains live through the syscall.  Branches and loop iterations carry the same ownership and caller-frame obligations as pure code.

The proposed frontend has a separate `verified_compile_wasi` command.  `verified_compile_wasi p := [f₁, …, fₙ]` constructs a callable module.  `verified_compile_wasi p (main := main) := [f₁, …, fₙ]` constructs a command module whose selected entry is a closed `Action UInt64`.  Definitions appear in callee-before-caller order.  The list may contain pure helpers and effectful definitions, with their respective recursion rules.  Pure source and its existing `verified_compile` command retain their current behavior.

The generated declarations include the module, its encoded-byte theorem, its initial-state theorem, each effectful definition's source-correspondence proof, and its I/O refinement theorem.  Conditional total-execution theorems use the resource and host premises below.  Resource conditions may quantify permitted reply paths.  The command must identify that obligation before exposing an input-only allocation bound.  These syntax and declaration names are proposals for review.

The reflector translates accepted Lean action definitions into this IR and proves equality of their source execution relations after flattening accepted values.  It recognizes the selected monad's `pure` and `bind`, supported source control flow, and named API operations.  Inline helpers unfold under the existing policy.  Recursive effectful helpers and action values stored in runtime data require later designs.  A failed reflection proof rejects the program.

The universal compiler theorem is proved by command structure, using the pure transport theorem and wrapper execution lemmas.  It quantifies every concrete host satisfying the specification and every pair of related initial states.  Each completed target execution returning a value, exiting, or reporting a permitted host trap has a matching source execution with the same ordered events, final world, and corresponding outcome.  The proof constructs that source path from the host's replies.  Nondeterministic specifications permit several paths.  Each target path must belong to that relation.

On normal return, values have the declared ownership, and retained caller regions keep their contents and separation.  A permitted guest resource trap matches a source prefix and residual command.  It preserves the effects already committed and remains distinct from exit.  Terminal outcomes require the host to discard the instance.

A separate total-execution theorem establishes a return or designated exit when allocation and depth budgets fit, pure callees meet their termination conditions, and every reached host call returns or honors exit.  Returned errnos are ordinary results under this theorem.  Host traps and guest resource traps retain their prefix-safety statement.  Kernel-checked source-correspondence proofs specialize these statements to each reflected definition.

## Lifecycle, bounds, and execution host

### Callable and command forms

A callable module exports selected effectful functions, `alloc`, `release`, `memory`, and the existing allocation counters.  Its instance persists across successful calls.  Globals and data segments establish its initial state during instantiation.  The pinned reactor ABI makes `_initialize` optional, and this proposal omits that hook.  Host code provides the three streams before invoking exports, serializes calls, and releases owned returned byte roots.  A returned errno permits another call.  Exit and traps terminate the host's use of the instance.

A command module exports `_start : () → ()` and `memory`.  It calls a selected closed `Action UInt64` entry and sends its returned status to `proc_exit`.  Explicit exit inside that entry follows the same terminal path.  The host invokes `_start` once and discards the instance afterward.  Debug allocation-counter exports belong to the callable test form.  Both forms export an empty `__indirect_function_table` to follow the pinned application ABI.  Source operations in this design use no indirect function pointers.

Instantiation still needs a theorem: the relocated module's initial globals, memory, tables, and byte literals establish the allocator invariant and scratch reservation.  [The current initial-store proof](../Verified/Instantiate.lean) provides the import-free starting point.  A modeled initial store is distinct from a proof of real engine instantiation.

### Resources and termination

The current allocator rounds a requested payload up to eight bytes, with a minimum of eight, and adds its 48-byte header.  A positive read's fresh-allocation charge is therefore `48 + 8 * max(1, ceil(capacity / 8))`, expressed with proof-side natural arithmetic.  A zero-capacity read and each write allocate no byte buffer.  Reuse can reduce the charge.  Copying, byte construction, pure calls, retained state, and call frames contribute their own proved charges.

The byte budget and ownership potential include the allocation header and full retained capacity after a short read.  Reclamation credits require a proved release.  A memory bound must account for those capacities throughout branches and loop iterations.

Each wrapper performs at most one host transfer call.  For the initial acyclic effect-call graph and bounded loops, termination follows from finite source control flow, terminating pure callees under their depth conditions, and return of each reached host call.  A blocked host call supplies no return-time guarantee.

The proposed internal ABI gives every effectful function a hidden depth word and checks it against the existing limit of 1,000.  Calls to effectful helpers and depth-aware pure bodies receive the next depth.  Host-facing wrappers initialize the depth once.  Effectful frames obey the same 32-position limit as guarded pure frames.  The proof and generated depth condition account for the combined call path.  Pure functions whose code takes no depth retain their existing ABI.  Fixed runtime-wrapper frames and real engine stack limits remain part of host validation and execution tests.

Pure calls also need the generated binding of constant tables.  An internal call supplies those hidden table arguments and any depth argument to the relocated body, directly or through a proved depth-preserving wrapper.  Its source-correspondence and bound proofs compose the table binding with the body theorem.  Exported wrappers that initialize depth are reserved for host entry.  The mixed-call tests include table-using pure callees under effectful helpers and calls at the combined depth boundary.

The effect theorem records allocation and depth requirements along an execution path.  A caller can prove an upper bound for all permitted replies and use it for total execution.  Read lengths are bounded by their requests, which supports such bounds for byte processing.  Reflection reuses the pure compiler's generated bound equations.  An input-only bound must account for every host-dependent branch and result length.  Bounded loops need an invariant that accounts for retained byte roots and cleanup on every iteration.

### Wasmtime integration

The host uses the repository's pinned Wasmtime 44.0.0 C API, configured through `wasi_config_t`, `wasmtime_context_set_wasi`, and `wasmtime_linker_define_wasi`.  It inherits or redirects stdin, stdout, and stderr through the standard WASI configuration.  The [existing download pin](../tools/download-wasmtime.sh), [host build](../tools/build-wasmtime-host.sh), and [canonicalizing engine setup](../tools/wasmtime-host.c) provide the starting points.  The new host path resolves the three imports through that standard linker.

The host configures guest stdin, stdout, and stderr through inheritance or explicit file redirection.  Execution tests redirect guest output to separate capture files and send returned values, allocation counts, exit status, and host diagnostics to control outputs.  This preserves guest bytes for exact comparisons.  Interactive command mode inherits stdio.  After an engine failure, it reports the error on host stderr and returns a failure status.

The command host maps the engine's distinguished WASI exit result to its process status.  Tests retain the raw unsigned 32-bit status separately from the operating system's process status.  Other engine errors remain errors and retain captured guest output for diagnosis.  The host releases or discards each instance according to the lifecycle above.

Lean's kernel checks the compiler and byte proofs against Talos and the specified host relations.  Wasmtime, the C compiler, OS streams, the native action interpreter, and real host progress remain external assumptions tested by execution.  Standard WASI linking supplies compatibility with the selected ABI.

### Exit acceptance: pending review

This proposal is pending the user's decision.  The existing exit semantics and host requirements above remain the approved design.

The proposed revision keeps standard Wasmtime linking, `exit : UInt64 → Action α`, and the `code mod 2^32` argument to `proc_exit`.  It distinguishes that argument from host acceptance.  An accepted request produces a designated exit with the same unsigned status.  A rejected request produces a terminal host-trap outcome without recording an accepted status.  Both outcomes preserve prior effects and prevent continuation.  The total-execution guarantee would require host acceptance of each reached exit request.  OS status narrowing would apply only to accepted exits.

The pinned [exit-code type](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/typenames.witx#L605-L606) is `u32`.  The [exit declaration](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/wasi_snapshot_preview1.witx#L426-L432) marks `proc_exit` as nonreturning and leaves nonzero meanings to the environment.  [Wasmtime 44's implementation](https://github.com/bytecodealliance/wasmtime/blob/v44.0.0/crates/wasi/src/p1.rs#L2614-L2625) accepts statuses below 126 and rejects 126 or above as an engine error.  That rejection differs from an accepted exit whose OS representation loses high bits.

The pinned [linker shadowing API](https://github.com/bytecodealliance/wasmtime/blob/v44.0.0/crates/c-api/include/wasmtime/linker.h#L63-L68) supports replacing `proc_exit` with a C callback.  Accepting every `UInt32` through that callback would establish a different host policy and require embedding-owned state for exit classification.  Stock Wasmtime would continue to reject statuses of 126 or above when running the same binary.

## Implementation and acceptance

The proposed implementation separates native APIs from compiler developments:

| Proposed location | Responsibility |
|---|---|
| `LeanExe/Dialect/Bytes.lean` | Native byte values, UInt64 operations, and literals. |
| `LeanExe/Wasi/` | Native action descriptions, the three stream APIs, exit, loops, and their observable meaning. |
| `Verified/Bytes/` | Byte representation, ownership, lowering, and proofs. |
| `Verified/Wasi/` | Host assumptions, typed command IR, module layout, compiler, wrapper proofs, and reflector support. |

Existing pure compiler modules receive the byte-type cases and shared transport lemmas they require.  These paths are proposals.

| Order | Work | Required result |
|---|---|---|
| 1 | Review the API, compatibility with earlier native WASI work, byte layout, host-error relation, exit rule, and pure transport plan. | Recorded decisions and exact theorem statements. |
| 2 | Packed byte meaning, representation, copy/release rules, access, construction, and literals. | Universal byte-operation proofs and source equations. |
| 3 | Import/type/function maps, the empty function-table encoding profile, and host-state transport. | Validity and round-trip proofs for the profile, plus relocated allocator and pure byte-processing execution with preserved host world. |
| 4 | One-iovec wrappers and scratch frame. | `writeSome` for every valid buffer and either output fd, then `readSome` for every capacity and permitted host reply. |
| 5 | Typed commands, bounds, and compilation. | A universal theorem for sequencing, branching, calls, bounded loops, returns, and exit. |
| 6 | Reflection, callable modules, `_start`, and initial-store proof. | Source-to-decoded-module theorems for each form. |
| 7 | Standard Wasmtime host and maintained proof/execution driver. | Checked examples, error cases, allocation results, and the repository gates below. |

The first write theorem quantifies arbitrary borrowed bytes, initial worlds, and satisfying hosts.  It proves the reported prefix on success, the declared error relation, preserved input bytes and caller heap, and returned UInt64 status/count.  It includes empty and zero-progress success.  The first read theorem quantifies capacity and host replies, proves exact returned bytes and ownership, and proves cleanup on errno and zero-byte success.  Fixed echo executions supplement these theorems.

| Test or proof group | Cases and acceptance condition |
|---|---|
| ABI and decoding | Exact three imports and signatures, correct export/type/function indices, the empty function-table section and export, valid one-iovec layout, zero and maximum-width counts, checked narrowing, round-trip decoding, and a theorem connecting emitted example bytes to the compiled module.  Invalid table types and export indices fail the profile checks. |
| Host-model execution | Arbitrary short reads/writes, zero progress, positive-capacity EOF, zero-capacity reads, errnos with permitted committed prefixes, exit, and a foreign host trap.  The joint trace preserves stdout/stderr order and permits descriptor aliasing. |
| Ownership and memory | Discarded reads, returned reads, read error, EOF, allocated-empty owned and borrowed inputs, retained aliases, branch and loop cleanup, untouched scratch-adjacent bytes, and retained caller regions.  Normal returns leave exactly the expected roots allocated. |
| Source reflection | Discarded effect results still execute, named actions execute once per sequencing, helper calls, Unit results, conditionals, bounded loops, byte access/build, and rejection of unsupported action escape. |
| Native execution | Binary input including 0 and 255, stdout and stderr, EOF, missing/failing streams, more than one call per callable instance, command exit zero/nonzero, and the documented exit narrowing.  Native expectations account for the counts the standard host returns. |
| Proof audit | Universal compiler, wrapper, transport, ownership, initial-store, source-correspondence, and byte-file theorems use only `propext`, `Classical.choice`, and `Quot.sound`. |
| Existing compiler outputs | The current pure import-free corpus keeps its exact bytes.  The existing execution, allocation, numerical, WGSL, and GPT32 gates pass. |

Scripted host models supply deterministic partial-transfer and failure cases.  Native tests exercise standard Wasmtime behavior without assuming that it returns every permitted short-write count.  Test-driver time limits bound blocked tests without adding a guest deadline API.

The proposed `tests/wasi/run.sh` invokes the repository runner and checks its registered examples, native executions, decoding, and theorem axioms.  [The verified test driver](../tests/verified/run.sh) and [full-check procedure](leanexe-manual.md#the-full-check) remain integration gates for shared compiler changes.  All Lean runs obey [the repository limits](../AGENTS.md).

### Review decisions

| Decision | Recommendation | Alternative and consequence |
|---|---|---|
| Zero-capacity read | One zero-length syscall.  EOF inference requires positive capacity. | Return `INVAL` before I/O, adding a source validation rule. |
| Exit UInt64 to WASI u32 | Explicit low-32-bit conversion for direct exit and command return. | A checked exit-code type adds source representation work.  Trapping on overflow adds a guest failure path. |
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

The user directed implementation of this agenda after its two reviews.  A change to these recommendations requires a new design discussion.
