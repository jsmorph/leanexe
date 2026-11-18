# Verified compiler: WASI Preview 1 design

## Scope and sources

The verified compiler's WASI modules import `fd_read`, `fd_write`, and `proc_exit` of `wasi_snapshot_preview1` for the standard streams and exit, and the flat calls of the pinned witx that a program uses.  A program reaches a descriptor other than the standard streams only as the preopened directory or through `withOpen`, and the Linux shim implements the imports with Linux system calls.  [The WASI manual](wasi.md) describes the public API, the generated declarations, the theorems, and the tests.  This document records the memory layout, the semantics and host assumptions, the structure of the proofs, and the decisions behind them.

The specification pin is WebAssembly/WASI commit `fae981bae14809d91f9bc2d63852d461f331d161`.  Its [interface definitions](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/wasi_snapshot_preview1.witx), [type definitions](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/typenames.witx), [generated reference](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/docs.md), and [application ABI](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/application-abi.md) are the external references.  `tests/wasi/witx/` holds the pinned witx files, from which `tools/wasi-calls.py` generates the descriptions of the flat calls.  A change of the pin requires review of the ABI, the generated descriptions, the host assumptions, and the proof statements.

The [pure typed source](../Verified/Source.lean) has value semantics.  Its [compiler](../Verified/Compile.lean) emits an import-free module, and its [runtime predicate](../Verified/RuntimeFacts.lean) requires that layout.  The [pure correctness theorem](../Verified/Correct.lean) and [representation API](../LeanExe/Pipeline/Implements.lean) use `Store Unit`.  [The effect language](../Verified/Wasi/Source.lean) embeds these pure expressions, and [its compiler theorem](../Verified/Wasi/Correct.lean) relates them to host-dependent execution through import relocation and host-state transport.

## Lean API and behavior

### Actions and results

The public namespace is `LeanExe.Wasi`, and [the manual's operations](wasi.md#operations-and-results) give its API.  [The native import](../LeanExe/Wasi.lean) supplies actions and their interpreter independently of the verified compiler, and the shared byte type is `LeanExe.Bytes`, with [its native operations](../LeanExe/Dialect/Bytes.lean).  Compiler representations and proofs are under `Verified`, and [the compiler import](../Verified/Wasi.lean) supplies `verified_compile_wasi`.

`Action α` is a semantic monad with Lean `pure` and `bind` instances, whose constructors are a returned value, the stream read and write, exit, `loop`, and `sys` for a flat call.  The accepted source uses ordinary `do`, named first-order helpers, bindings, conditionals, calls of pure functions, and the bounded loop.  Effectful helper calls form an acyclic call graph, and pure callees keep their recursion and allocation conditions, as [the review decisions](#review-decisions) choose.  Error results are ordinary values, so the source program determines whether to return, exit, continue, or report an error.

Native action descriptions and continuations can be constructed as the native interpreter runs.  Reflection translates accepted definitions into fixed typed code and performs no guest I/O.  Compiled runtime values have the compiler's value types, including bytes and result records.  The host world is part of the semantics and host state rather than the source program's arguments.

`loop` is a command-description node whose callbacks are statically known code, reflected with their captured values.  The native interpreter executes the loop, and the compiler emits a structured Wasm loop.  The proof uses natural indices, while the compiled counter stays in `UInt64` and reaches `count` without wrapping.

An effectful helper may return `Unit`.  Its result occupies zero Wasm slots, and a checked equation erases its unused result binding.  [The result descriptor](../Verified/Wasi/Source.lean) and [result adapters](../Verified/Wasi/Results.lean) cover `Unit` and accepted value types.

### Reads, writes, and exit

`readSome` accepts zero capacity and still calls `fd_read` with one zero-length iovec, so EOF inference requires positive capacity.  A capacity above `2^32 - 1` returns errno `overflow` (61) and empty bytes before allocation or host I/O.  An address-space or allocator failure after a valid capacity follows the guest-trap mechanism and is distinct from a WASI errno, and the allocation theorem supplies sufficient-memory premises for a trap-free call.

A successful read returns an owned buffer containing exactly the reported bytes, with length at most the requested capacity.  On zero-byte success the wrapper releases any allocated buffer and returns empty bytes, and on an errno it releases that buffer and returns the errno with empty bytes.  The wrapper ignores a count that the host leaves in guest memory with an errno.

`readAll limit` is a definition over the stream actions: a `loop` of `limit + 2` passes, each a `readSome 4096`.  The definition unfolds to one `loop` node whatever the limit, so the kernel's checks of a reflected program that uses it stay small, and `Action`, `Exec`, and the host assumptions need no rule of their own for it.  A recursion on a fuel of `limit + 2` reads has the same meaning, but the kernel's check of a generated command theorem unfolds it once per unit of fuel and exceeds its recursion depth at a limit of 10,000.  The compiler compiles it with a command of its own, which the section on typed commands describes.

A successful write returns the host's count, including a short or zero count, which is at most the supplied length.  Empty writes still call `fd_write`, so host errors are observable.  A write error returns its errno and a count of zero, a sentinel: `count` describes transferred bytes only when `errno = 0`.  The input buffer stays borrowed in either outcome, and source code can compare `count` with `Bytes.size bytes` before proceeding.

`exit code` has terminal source semantics and no continuation, and it passes `code mod 2^32` as the `proc_exit` argument.  A returned command-entry status uses the same conversion, which defines the import argument for every `UInt64` input.  The host may accept that request or fail.  Acceptance produces an exit with the exact narrowed status, and failure produces a host-trap outcome and preserves prior effects.  The raw status of an accepted exit is separate from its operating-system process status.

### Flat calls and handles

A flat call is one `Action.sys call args next` node, whose `call` is a description generated from the witx and whose reply carries the errno and the content of each region that the call writes.  One node for every call keeps `Exec`, `Prefix`, the host relation, and the compiler's command rule independent of the call, and one generator writes the descriptions, the typed functions, and their reflection equations, which a second lowering of the witx checks.  `Call.reject` rejects before the call an argument that does not fit its core type or that lies outside its enum or flags, since Wasmtime 44 traps on an enum or flags argument outside its type.  The descriptions pass arrays of iovecs with one element, since Wasmtime 44 reads into and writes from only the first non-empty element.  [The flat calls](wasi.md#flat-preview-1-calls) and [the nested calls](wasi.md#nested-calls) give the API and the forms of `Command.sys`.

A program obtains a descriptor only as `Handle.preopened`, descriptor 3, or as the handle that `withOpen` binds for the extent of its body.  `withOpen` follows a successful `path_open` with an `fd_close` when the body returns, and the handle check, which the kernel decides for each program, refuses `path_open`, `fd_close`, and `fd_renumber` outside that shape and every handle argument that is not a bracket's handle or 3.  A program therefore never closes or renumbers descriptors 0 to 3, and under the host assumption `FreshOpens` each use of a handle names a descriptor that its bracket opened.  [The handles](wasi.md#handles) state the theorems.

### Byte operations

`Bytes` is an immutable value whose Lean meaning is a packed byte sequence, and [the manual's byte operations](wasi.md#packed-bytes) give its API.  The logical length uses `Nat` where Lean's byte-sequence definitions require it, while compiled counters, comparisons, API arguments, and returned lengths use `UInt64`, and reflection proves their correspondence under the memory bound.  [Byte access](../Verified/Bytes/Get.lean) and [construction](../Verified/AlignedBytes.lean) have universal correctness rules.  Intermediate `UInt8` conversions in those rules do not require a general `UInt8` arithmetic dialect.

`ReadResult` flattens to an errno word and one byte value, and `WriteResult` is scalar.  The accepted field representation includes `Bytes`, so these records supply the operation results without extending sums to arbitrary heap-valued fields.  The result structures of the flat calls flatten the same way, to their errno, their words, and at most one byte value.

A nonempty byte literal produces an owned heap value when evaluated.  The compiler keeps its constant bytes in a protected data segment and copies them into that allocation, and empty literals produce `(0, 0)`.  Repeated evaluations get separate owned roots.  Literal data stays protected across calls, and construction contributes its allocation and copy cost.

## Packed memory and the WASI ABI

### Byte ownership

A represented byte value has two Wasm values: a `UInt64` allocation-root pointer `p` and a `UInt64` logical length `n`.  Bytes begin at `p` and occupy consecutive addresses.  A nonzero root has the runtime's 48-byte header, count one, capacity at least `max(8, n)`, kind two, width one, and child mask zero, and its full allocated region is included in separation and ownership.  [The byte representation](../Verified/Bytes/Basic.lean) states these fields and bounds.

New empty results use `(0, 0)`.  Incoming owned and borrowed empty values may also have a valid allocated root of length zero, as the host allocator gives.  Cleanup tests the root and releases a nonzero owned root once.  Borrowed-byte separation and frame predicates protect the allocation header and capacity even when the logical length is zero.  A byte value exposes its allocation root and length through the representation API, while source code operates on `Bytes`.

Writes borrow their input, and reads return a fresh owned root on nonempty success.  If an owned value has multiple live source uses, the compiler's mode and lifetime analysis keeps its owner until the last use.  Converting a borrowed byte value to an owned result copies its bytes.  Result construction, branch cleanup, unused results, and effectful helper returns have the separation and last-use obligations of arrays.  [Owned copying](../Verified/AlignedBytes.lean) and [release](../Verified/Bytes/Release.lean) prove preservation of the caller's retained regions.

The [execution host](../tools/wasmtime-host.c) allocates raw packed bytes and passes byte values as pointer and length.  [The representation instance](../LeanExe/Pipeline/Bytes.lean) relates that ABI to owned and borrowed source bytes, and host execution tests check the external allocator and argument handling.  For positive read capacity, the wrapper allocates the requested byte capacity.  A short read keeps the root with the returned logical length, and unused capacity stays private to the allocation.  Error and zero-byte paths release it, and a zero-capacity read uses `(0, 0)` as its empty writable range and needs no allocation.

### Imports and scratch

All imports use the module name `wasi_snapshot_preview1`, and a module with `c` flat calls has these function imports:

| Function index | Import | Signature |
|---|---|---|
| 0 | `fd_read` | `(i32, i32, i32, i32) → i32` |
| 1 | `fd_write` | `(i32, i32, i32, i32) → i32` |
| 2 | `proc_exit` | `(i32) → ()` |
| `3 + i`, for `i < c` | The flat call `i` of `p.sysCalls` | `ABI.callType`: the core types of its parameters, then an `i32` errno |

For read and write the arguments are the fixed fd, the iovec pointer, one iovec, and the result-count pointer.  An iovec consists of a 32-bit buffer pointer and 32-bit byte count, and the count result occupies four bytes.  The wrapper zero-extends successful counts and errnos into `UInt64` values, and valid errno results are a host-ABI premise.  A flat call's parameters lower by `ABI.paramTypes`: one `i32` for a 32-bit value, a descriptor, an enum, 32-bit flags, or a pointer to a result, a reported region, or a record, one `i64` for a 64-bit value or 64-bit flags, a pointer and a length for an input, an output, or an iovec array, and two pointers and a count for subscriptions.

The scratch reservation is `[0, 16)`: the iovec at bytes 0 through 7, the count at bytes 8 through 11, and four padding bytes.  The wrapper initializes its metadata and count before calling the host.  A flat call uses the same bytes for the element of its iovec array and for its result words.  Constant arrays begin at 4096, byte literals follow them, and the allocator starts after the static data.

The layout preserves the pure program's constant-array addresses and places raw byte-literal data after those arrays.  The initial bump pointer starts beyond all static data, aligned to eight bytes, and the initial-memory proof includes that data and the page cap.  These arrays occupy linear memory, and the application ABI's function table is a separate Wasm resource.

Before narrowing a nonempty byte range, the proof establishes `p < 2^32`, `n < 2^32`, and `p + n` within the active memory and its cap.  The read wrapper checks capacity at runtime, and heap and representation bounds justify address and write-length narrowing.  Empty pointer zero with length zero is a valid range.  Host count results are read only on success, and the host assumptions bound them by the requested range.

The memory frame of a read excludes scratch and the newly allocated writable capacity, and that of a write excludes only scratch.  A flat call's frame excludes its output regions.  The host preserves allocator headers, globals, tables, memory caps, and every other guest region, and it returns control without invoking another guest export.  Calls into an instance are serialized.  These conditions make a single scratch reservation sufficient across repeated calls and separate instances.

## Observable semantics and host assumptions

[The trusted-base document](trusted-base.md#wasi-wasi-preview-1-modules) lists the host assumptions of the WASI theorems, with the check and the source of each.  It names the definitions of the Preview 1 model that a statement unfolds to and the theorems that state when a satisfying host exists.  The theorems depend without proof on the command meaning and on the rules for errors and traps that the following subsections state.

### Command meaning

The command semantics relates a source environment and host world to a result, final world, and ordered event trace.  A normal return includes a value, and an accepted exit includes the narrowed status.  A host trap, including rejection of an exit request, includes its committed world and trap identity.  Bounded-loop execution repeats the body in source order and preserves every earlier event.  A separate prefix relation records completed events, the current world, and a residual command when a guest resource failure interrupts execution.

Events record host invocations: the operation, selected fd, requested bytes or capacity, returned errno and successful count, and committed transfer, and for a flat call the call, its arguments, and its reply.  Pure computation and argument rejection leave the trace unchanged.  Stdout and stderr events share one ordered trace, and the host world may map them to the same resource.  The model also permits stdin and output descriptors to alias.  Separate byte logs are derived observations and establish neither ordering across descriptors nor aliasing.

The abstract world and host-step relations specify the stream operations and the flat calls.  [Observed host state](../Verified/Wasi/Observed.lean) adds an append-only joint event journal.  The universal theorem ranges over every satisfying host, with arbitrary input, output length, and permitted transfer partition, and scripted worlds supply concrete semantic tests.  `Action` has this meaning through [its execution relation](../LeanExe/Wasi/Semantics.lean) and [prefix relation](../LeanExe/Wasi/Prefix.lean).  [The native interpreter](../LeanExe/Wasi/Interpreter.lean) executes actions through a stream or supplied adapter, whose conformance to the abstract host assumptions is external to the compiler proof.  Kernel-checked equations for `pure` and `bind` establish sequencing, while host assumptions establish transfers.

### Success, errors, and traps

The host specification combines ABI shape, transfer behavior, and the memory frame.  A successful stdin read supplies at most the requested bytes, and its returned bytes match the writable prefix.  A successful output write commits the reported prefix of the supplied sequence.  A flat call's contract, `sysContract`, admits the requests of `SysRequest`, changes memory only in the request's output regions, and on errno 0 leaves each shown output in its region.  The frame protects all guest resources outside the specified writable regions.

On errno, the model may record a committed prefix for the failed operation, while the count exposed by the wrapper is the zero sentinel.  A read error may have consumed an input prefix and changed bytes within its discarded buffer, and a write error may have committed an output prefix.  Previously completed effects stay in the world and trace.  A stronger error guarantee would be an additional host assumption requiring its own evidence, so the result-count slot after an error says nothing about device progress.

Host-trap outcomes also keep the world committed before the trap, and frame conditions still protect unrelated guest memory.  Normal-return ownership postconditions apply after a return.  A host trap, resource trap, or exit ends the host's use of that instance.

Talos models host invocation through `HostEnv`, `HostSpec`, and `HostResult`, as pinned by [the dependency manifest](../lake-manifest.json), and `HostResult` has `Return`, `Trap`, and `Throw` outcomes.  The exit model uses a distinguished world field `exited : Option UInt64`.  Accepted exit records the narrowed status and produces the designated exit trap, and exit failure produces a host trap and preserves the previous exit field and committed effects.  A host beginning a fresh lifecycle supplies a world with `exited = none`, and read, write, and flat call transitions preserve that field.  The accepted-exit theorem requires the designated outcome and recorded status, so an arbitrary trap message or a nonzero guest status cannot establish acceptance.  The host specification excludes ordinary return from `proc_exit` and thrown exceptions from every import.  [The host assumptions](../Verified/Wasi/HostSpec.lean) hold the exit marker and the exact trap identity, and execution tests check that Wasmtime's accepted exits and exit failures match their modeled outcomes.

### The Linux shim

The shim implements a command's WASI imports with the Linux call layer of [`LeanExe/Linux/`](../LeanExe/Linux), whose rule describes each system call independently of an instruction set.  Its specification in [`Verified/Shim/`](../Verified/Shim) is a Talos host environment, `linuxEnv`, and a host relation, `linuxHost`, over the layer's events: `linuxHost` relates a WASI request to a reply exactly when the layer events that the shim appends form an image of the WASI event.  `linuxEnv_satisfies` proves that the environment satisfies `hostSpecWith` of that relation, so the compiler's command theorem applies to the shim unchanged, and `shim_footprint` composes the two.  The specification takes the kernel's replies as a sequence indexed by the number of layer events and assumes no property of them, so a statement that needs one, such as readAll's corollaries, states it as a premise or a class of reply sequences.  A binding to an instruction set proves that its stubs simulate the environment's functions, as [the AArch64 binding](a64-bare-metal.md#wasi-commands) does.  [The manual's shim section](wasi.md#the-linux-shims-specification) states the functions and the theorems, and [its table of differences](wasi.md#differences-from-wasmtime) the replies in which the shim and the Wasmtime host differ.

## Module construction and compiler proofs

[The native action semantics](../LeanExe/Wasi/Action.lean) gives the source executions, and [the typed effect language](../Verified/Wasi/Source.lean) gives the compiler's commands.  The wrapper and transport results below supply the premises of [command correctness](../Verified/Wasi/CommandCorrect.lean) and [cost-aware command correctness](../Verified/Wasi/CostCommandCorrect.lean).  [Program correctness](../Verified/Wasi/Correct.lean) combines those rules for a complete effectful program, and [callable entry](../Verified/Wasi/NativeEntry.lean) and [command entry](../Verified/Wasi/NativeCommand.lean) relate it to reflected Lean actions.  For an unbounded process, [process refinement](../Verified/Wasi/ProcessCorrect.lean) supplies the execution relation, and [total process execution](../Verified/Wasi/ProcessTotalCorrect.lean) also needs the application's progress, resource, and exit premises, as [the manual's process theorems](wasi.md#process-theorems-and-applications) state.

### Pure code in an importing module

Let the pure module contain `N` defined functions, including its allocator, release routine, depth entries, and wrappers, and let the program use `c` flat calls.  The WASI module imports the stream functions and the flat calls and relocates those `N` definitions before appending the I/O wrappers and effectful functions.  [The module layout](../Verified/Wasi/Module.lean) gives these positions:

| Item | Defined-function position | Absolute function index |
|---|---|---|
| Allocator | 0 | `3 + c` |
| Release | 1 | `4 + c` |
| Pure function at pure position `k` | `k` | `3 + c + k` |
| First appended wrapper or effectful function | `N` | `3 + c + N` |
| Command `_start`, when requested | Last defined position | `3 + c` plus that position |

Function indices and type indices are separate mappings.  The layout reserves three type entries for the stream imports, including duplicate read and write signatures, relocates pure type index `t` to `3 + t`, and places the types of appended definitions after them and the types of the flat calls' imports after every other type.  All calls, depth entries, wrapper calls, exports, and function-type annotations follow the layout maps.  [The validity generator](../Verified/Wasi/ReflectValidity.lean) constructs proofs of import signatures, instruction typing, and export bounds for the concrete module.  [The shared encoder](../LeanExe/Encoding/Modules.lean) and [encoding-domain conditions](../LeanExe/Encoding/Domain.lean) account for function imports.

The encoder and its [module grammar](../LeanExe/Encoding/Spec/Modules.lean) admit one empty nullable-function-reference table with minimum zero and the export `__indirect_function_table` at table index zero.  The table section and table-export entry have encoding, decoding, domain, validity, and round-trip rules.  The empty-table-list case keeps the pure encoding scheme, and byte-for-byte preservation of the pure import-free corpus is an integration check.  Element segments and indirect calls lie outside this profile.

[Function renaming](../Verified/FunRelocation.lean) transfers typed source functions and meaning, and the [module-composition rules](../Verified/ModuleComposition.lean) keep the import-free runtime layout.  WASI reuse adds [instruction relocation](../Verified/Wasi/Relocation.lean), [pure execution transport](../Verified/Wasi/PureTransportSpecs.lean), and [module transport](../Verified/Wasi/ModuleTransport.lean).  The transport keeps the pure universal theorem and establishes these properties:

1. Relocated pure code simulates the original code under the layout maps, preserving its data state, represented arguments and results, and resource outcome.  The relation accounts for function identities and any added table resources.
2. Every reachable pure call targets a relocated definition, including allocator and release calls.  It never reaches an import.
3. The store projection follows the layout relation and erases the host world.  It commutes with pure execution, and lifting its result preserves that world on returns and guest traps.
4. Appended definitions and the empty application-ABI table do not change pure execution.
5. Heap predicates and representation facts transport through that state relation, including the byte predicates.

The proof covers an explicit pure instruction profile, including nested control flow and direct calls.  Profile closure excludes host and indirect calls.  [The relocated runtime rules](../Verified/Wasi/Runtime.lean) reuse allocator and release correctness through this transport.  The effect proof preserves both the host world and its ordered event journal across pure calls.

### Typed commands and reflection

The effect IR embeds typed pure expressions and has constructors for return, binding, conditionals, first-order effectful calls, bounded loops, the stream read and write, the read of the whole input, exit, and `sys` for a flat call.  Contexts record the types and ownership modes of live values, and its result descriptor permits ordinary accepted values and erased `Unit`.  Read and write constructors invoke their transfer imports.  Exit emits the call to `proc_exit` followed by `unreachable`, which permits validation at any result type, and the host call terminates with a designated exit or a permitted host trap.  `Command.sys` compiles a flat call in one of the forms of [`SysForm`](../Verified/Wasi/SysForm.lean), and `command_sys_spec_with` and `cost_command_sys_spec_with` prove its code against `sysContract`.

The constructor `Command.readAll` compiles `readAll limit` into the calling function: the code of the limit, then [fixed code](../Verified/Wasi/ReadAllCode.lean) that uses six locals of the command's scratch.  It tests the limit, allocates the buffer with the shared allocator, and runs a structured loop whose body calls `fd_read` with an iovec at the root plus the bytes held, so that the module's functions, wrappers, and indices are those of a program without it.  [The loop's proof](../Verified/Wasi/ReadAllLoop.lean) carries an invariant of the buffer's header and bytes, the step from the start of the command, the locals, and a partial run of the source loop, and the bytes below the limit plus one decrease at every pass that continues.  [The command's rules](../Verified/Wasi/ReadAllCommand.lean) give its correctness and its charge, and its resource prefixes are the prefixes of its action with the whole charge, since the allocation precedes every read.

Compilation orders operand evaluation before its effect and materializes operation results before evaluating a continuation.  Cleanup uses liveness across both the operation and continuation, so an unused read result is still read and then released.  A borrowed write argument stays live through the WASI import call.  Branches and loop iterations have the ownership and caller-frame obligations of pure code.

The reflector translates accepted Lean action definitions into this IR and proves `Action.Rel` after flattening accepted values.  [Execution transport](../LeanExe/Wasi/RelatedExec.lean) and [prefix transport](../LeanExe/Wasi/RelatedPrefix.lean) relate this relation to observable semantics.  The reflector recognizes the monad's `pure` and `bind`, supported control flow, the stream operations, the typed functions of the flat calls, `args`, `environ`, and `withOpen`, whose bracket it emits as a fixed shape of commands that the handle check recognizes.  Unlisted inline helpers unfold, the reflector rejects recursive effectful helpers and action values stored in runtime data, and a failed reflection proof rejects the program.  [The manual's module forms](wasi.md#callable-and-command-modules) and [declaration table](wasi.md#declarations) give the frontend's forms and the public names.

The universal compiler theorem is proved by command structure, using the pure transport theorem and wrapper execution lemmas.  It quantifies every concrete satisfying host and related initial state and supplies a sufficient fuel bound.  Each target execution at or above that bound returning a value, exiting, or reporting a permitted host trap has a matching source execution with the same ordered events, final world, and corresponding outcome.  The proof constructs that source path from the host's replies, and since nondeterministic specifications permit several paths, each target path must belong to that relation.

On normal return, values have the declared ownership, and retained caller regions keep their contents and separation.  A permitted guest resource trap matches a source prefix and residual command, preserves the effects already committed, and is distinct from exit.  Terminal outcomes require the host to discard the instance.

A separate total-execution theorem establishes a return or designated exit when `Heap.Within` holds for the allocation bound, `Resource.CallPrefixBound` bounds every typed resource prefix and establishes its size and depth checks, and `host.NoTrapsAlong` excludes reached host traps and exit rejection.  Returned errnos are ordinary results.  Kernel-checked source-correspondence proofs specialize these statements to each reflected definition, and the general refinement theorem keeps committed effects on host or guest resource failure.

## Lifecycle, bounds, and execution host

### Callable and command forms

A callable module exports every listed effectful function, `alloc`, `release`, `memory`, and the allocation counters, and its instance persists across successful calls.  The pinned reactor ABI makes `_initialize` optional, and the modules omit that hook.  Host code provides the streams before invoking exports, serializes calls, and releases owned returned byte roots.  A returned errno permits another call, while an accepted exit, a host failure, or a guest trap ends the host's use of the instance.

A command module exports `_start : () → ()` and `memory`.  It calls a selected closed `Action UInt64` entry and sends its returned status to `proc_exit`, and an explicit exit inside that entry follows the same terminal path.  The host invokes `_start` once and discards the instance afterward.  The allocation-counter exports belong to the callable test form.  Both forms export an empty `__indirect_function_table` to follow the pinned application ABI, and source operations use no indirect function pointers.

[The initial-store theorem](../Verified/Wasi/ProgramInitial.lean) proves the allocator invariant, memory cap, borrowed constant tables, and static byte pool for the complete modeled module.  It preserves the supplied abstract host world.  Representation, consumed-block separation, and scratch separation are call premises, and real engine instantiation and OS-stream configuration are external to that theorem.

### Resources and termination

The allocator rounds a requested payload up to eight bytes, with a minimum of eight, and adds its 48-byte header.  A positive read's fresh-allocation charge is therefore `48 + 8 * max(1, ceil(capacity / 8))`, expressed with proof-side natural arithmetic.  A zero-capacity read and each write allocate no byte buffer, and reuse can reduce the charge.  Copying, byte construction, pure calls, flat call buffers and blocks, retained state, and call frames contribute their own proved charges.

`readAll limit` charges `Bytes.allocationCost (limit + 4096)` for its buffer, or nothing for a limit that returns errno 61, and its reads add nothing to the heap top.  The byte budget includes the allocation header and requested capacity rather than the short read's logical result length.  Cleanup makes released blocks available for reuse, and a memory bound must account for retained capacities throughout branches and loop iterations.

Each primitive read or write wrapper makes at most one WASI import call, and the host may use several operating-system calls to implement one import.  For the acyclic effect-call graph and bounded loops, termination follows from finite source control flow, terminating pure callees under their depth conditions, and return of each reached host call.  A blocked host call supplies no return-time guarantee.

The internal ABI gives every effectful function a hidden depth word and checks it against the limit of 1,000 of guarded pure calls.  Calls to effectful helpers and depth-aware pure bodies receive the next depth, and host-facing wrappers initialize the depth once.  Pure frames that take the depth keep the 32-position limit, and the compiler admits larger acyclic effectful frames under the checked call-chain estimate of [the manual's stack check](wasi.md#callable-and-command-modules).  This estimate is a compiler admission condition, and real engine stack layout is an external assumption.  The typed resource-prefix condition separately accounts for the combined call path, and pure functions whose code takes no depth keep their ABI.

A process may run to EOF without an iteration bound.  [The process compiler](../Verified/Wasi/ProcessCode.lean) places bounded begin and step functions inside an unbounded `_start` loop, which compacts the owned state after begin and after each completed step.  Compaction lets the total-process theorem bound the memory of one step at a time, and it requires a state type without trees.  [The manual's processes](wasi.md#processes-without-an-iteration-bound) and [process theorems](wasi.md#process-theorems-and-applications) give the entry, the theorems, and their applications.

Pure calls also need the generated binding of constant tables.  An internal call supplies those hidden table arguments and any depth argument to the relocated body, directly or through a proved depth-preserving wrapper.  Its source-correspondence and bound proofs compose the table binding with the body theorem.  Exported wrappers that initialize depth are reserved for host entry, and the mixed-call tests include table-using pure callees under effectful helpers and calls at the combined depth boundary.

The effect theorem records allocation and depth requirements along an execution path.  A caller proves an upper bound for all permitted resource prefixes and uses it for total execution.  Read lengths are bounded by their requests, which supports such bounds for byte processing, and pure fragments use the pure compiler's allocation bounds.  The public frontend exposes the typed prefix condition rather than synthesizing an input-only bound for every I/O program, since such a bound must account for host-dependent branches, result lengths, retained byte roots, and cleanup across loop iterations.

### Wasmtime integration

The host uses the repository's pinned Wasmtime 44.0.0 C API, configured through `wasi_config_t`, `wasmtime_context_set_wasi`, and `wasmtime_linker_define_wasi`.  It inherits or redirects stdin, stdout, and stderr through the standard WASI configuration and passes the arguments, environment variables, and preopened directory that [the manual's host section](wasi.md#wasmtime-host) lists.  The [download pin](../tools/download-wasmtime.sh), [host build](../tools/build-wasmtime-host.sh), and [canonicalizing engine setup](../tools/wasmtime-host.c) define the tested embedding, and the host resolves every import through the standard linker.

Execution tests redirect guest output to separate capture files and send returned values, allocation counts, and terminal records to control outputs, while host diagnostics go to host stderr.  This separation keeps guest bytes for exact comparisons.  Interactive command mode inherits stdio.  After an engine failure, the host reports the error on host stderr and returns a failure status.

The pinned [exit-code type](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/typenames.witx#L605-L606) is `u32`.  The [exit declaration](https://github.com/WebAssembly/WASI/blob/fae981bae14809d91f9bc2d63852d461f331d161/preview1/witx/wasi_snapshot_preview1.witx#L426-L432) marks `proc_exit` as nonreturning and leaves nonzero meanings to the environment.  Wasmtime 44 accepts statuses below 126 and rejects the others as engine errors, as [the manual's host section](wasi.md#wasmtime-host) states.  The host identifies accepted exits through [`wasmtime_error_exit_status`](https://github.com/bytecodealliance/wasmtime/blob/v44.0.0/crates/c-api/src/error.rs#L52-L62), and captured guest output stays available after either terminal outcome.

Lean's kernel checks the compiler and byte proofs against Talos and the specified host relations.  Wasmtime, the C compiler, OS streams, native adapter conformance, and real host progress are external assumptions tested by execution.  Standard WASI linking supplies compatibility with the selected ABI.

## Implementation and acceptance

The implementation separates native APIs from compiler developments:

| Location | Responsibility |
|---|---|
| [Native bytes](../LeanExe/Dialect/Bytes.lean) | Native byte values, `UInt64` operations, and literals. |
| [Native actions](../LeanExe/Wasi) | Stream APIs, exit, bounded loops, processes, the flat calls' descriptions and typed functions, `withOpen` and the bracket discipline, observable semantics, and the native interpreter. |
| [Byte compilation](../Verified/Bytes) | Byte representation, ownership, lowering, and proofs. |
| [WASI compilation](../Verified/Wasi) | Host assumptions, typed command IR, module layout, compiler, wrapper proofs, the handle check, and reflector. |
| [Linux call layer](../LeanExe/Linux) | Descriptions of Linux system calls, the layer's rule, and the properties of replies. |
| [Shim specification](../Verified/Shim) | `linuxEnv`, `linuxHost`, their contracts, the footprint, and the trace and descriptor lemmas. |
| [AArch64 binding](../Verified/ShimA64) | The stubs' simulation of the shim and the executables' theorems. |
| [Call generator](../tools/wasi-calls.py) | Descriptions, typed functions, reflection equations, and frame tests from the pinned witx. |

The pure typed source and compiler include byte operations and the literal-pool context.  For a program without literals, [the empty-pool equality](../Verified/LiteralCodeEq.lean) states the module that `compileWith` produces, and `tests/verified/run.sh --check-bytes` compares the emitted modules with saved reference modules byte for byte.  The proofs divide at these boundaries:

| Proof boundary | Source |
|---|---|
| Reviewed API, byte layout, host-error relation, exit behavior, and reuse plan. | [Review decisions](#review-decisions). |
| Packed bytes, ownership, copying, release, access, construction, and literals. | [Byte representation](../LeanExe/Pipeline/Bytes.lean), [byte construction](../Verified/AlignedBytes.lean), and [literal correctness](../Verified/AlignedBytes.lean). |
| Import relocation, host-state preservation, and empty-table encoding and validity. | [Module transport](../Verified/Wasi/ModuleTransport.lean), [module grammar](../LeanExe/Encoding/Spec/Modules.lean), and [validity rules](../LeanExe/Encoding/Spec/Validity.lean). |
| Universal one-iovec read and write wrappers with scratch framing. | [Read execution](../Verified/Wasi/ReadFunction.lean) and [write execution](../Verified/Wasi/Write.lean). |
| Universal safety and cost-aware compilation for commands, calls, branches, and bounded loops. | [Command safety](../Verified/Wasi/CommandCorrect.lean), [command cost correctness](../Verified/Wasi/CostCommandCorrect.lean), and [program correctness](../Verified/Wasi/Correct.lean). |
| Flat calls against their contracts, and hosts that satisfy the contracts. | [Flat call commands](../Verified/Wasi/SysCommand.lean), [host assumptions](../Verified/Wasi/HostSpec.lean), and [totality for calls](../Verified/Wasi/HostTotalWith.lean). |
| The handle check and the bracket discipline of checked commands. | [Handle check](../Verified/Wasi/HandleCheck.lean), [handle theorems](../Verified/Wasi/Handles.lean), and [bracket discipline](../LeanExe/Wasi/Bracket.lean). |
| Native source correspondence, callable and `_start` execution, modeled initial store, and encoded-module proofs. | [Callable entry](../Verified/Wasi/NativeEntry.lean), [command entry](../Verified/Wasi/NativeCommand.lean), [initial store](../Verified/Wasi/ProgramInitial.lean), and [public frontend](../Verified/Wasi/ReflectCommand.lean). |
| Standard Wasmtime embedding and maintained proof and execution checks. | [Native host](../tools/wasmtime-host.c), [WASI driver](../tests/wasi/run.sh), [verified compiler driver](../tests/verified/run.sh), and [full repository checks](verified-manual.md#the-full-check). |
| Unbounded process refinement and conditional total execution, with integer and binary64 running-sum output and accepted exit with status 0 or 28. | [Process refinement](../Verified/Wasi/ProcessCorrect.lean), [total-process theorem](../Verified/Wasi/ProcessTotalCorrect.lean), [integer correctness](../Demos/RunningSum/Correct.lean), and [binary64 correctness](../Demos/RunningSumFp/Correct.lean). |
| The shim's environment against `linuxHost`, and the footprint of a command's run under the shim. | [Shim satisfaction](../Verified/Shim/Satisfies.lean) and [footprint](../Verified/Shim/Footprint.lean). |

The write theorem quantifies arbitrary borrowed bytes, initial worlds, and satisfying hosts.  It proves the reported prefix on success, the declared error relation, preserved input bytes and caller regions outside scratch, and the returned `UInt64` status and count, including empty and zero-progress success.  The read theorem quantifies capacity and host replies, proves exact returned bytes and ownership, and proves cleanup on errno and zero-byte success.  Fixed echo executions supplement these theorems.

| Test or proof group | Cases and acceptance condition |
|---|---|
| ABI and decoding | Exact stream imports and signatures, correct export, type, and function indices, the empty function-table section and export, valid one-iovec layout, zero and maximum-width counts, justified narrowing, round-trip decoding, and generated-byte theorems connecting the encoding to the compiled module and native refinements.  Invalid table types and export indices fail the profile checks.  File writing is external to these theorems. |
| Flat calls | The descriptions against the witx and an independent lowering, frame tests of every described function under Wasmtime 44 with seeded faults, and a sweep of enum and flags values in which Wasmtime traps exactly on the values that `Call.reject` rejects. |
| Host-model execution | Arbitrary short reads and writes, zero progress, positive-capacity EOF, zero-capacity reads, errnos with permitted committed prefixes, accepted exit, exit rejection, and a foreign host trap.  The joint trace preserves stdout and stderr order and permits descriptor aliasing. |
| Ownership and memory | Discarded reads, returned reads, read error, EOF, allocated-empty owned and borrowed inputs, retained aliases, branch and loop cleanup, unchanged scratch-adjacent bytes, and retained caller regions.  Normal returns leave exactly the expected roots allocated. |
| Source reflection | Discarded effect results still execute, named actions execute once per sequencing, helper calls, `Unit` results, conditionals, bounded loops, byte access and build, brackets that the handle check accepts and refuses, and rejection of unsupported action escape. |
| Native execution | Binary input including 0 and 255, stdout and stderr, EOF, missing or failing streams, and repeated callable calls.  Host fixtures check accepted statuses 0, 7, and 125, rejected requests 126, 256, and `2^32 - 1`, and low-32-bit argument conversion.  Exit rejection preserves prior output, and every terminal outcome prevents later calls.  Native expectations account for the counts the standard host returns. |
| Proof audit | Universal compiler, wrapper, transport, ownership, initial-store, source-correspondence, generated-byte, and validity theorems use only `propext`, `Classical.choice`, and `Quot.sound`. |
| Compiler outputs | Exact bytes for the pure import-free corpus, and successful execution, allocation, numerical, WGSL, and GPT32 integration checks. |

Scripted host models supply deterministic partial-transfer and failure cases.  Native tests exercise standard Wasmtime behavior without assuming that it returns every permitted short-write count.  Test-driver time limits bound blocked tests without adding a guest deadline API.  [The manual's tests](wasi.md#tests) describe the drivers, [the verified test driver](../tests/verified/run.sh) and [full-check procedure](verified-manual.md#the-full-check) are the integration checks for shared compiler changes, and all Lean runs use [the repository limits](../AGENTS.md).

### Review decisions

| Decision | Approved choice | Alternative and consequence |
|---|---|---|
| Zero-capacity read | One `fd_read` import call with a zero-length iovec.  EOF inference requires positive capacity. | Return `INVAL` before I/O, adding a source validation rule. |
| Exit UInt64 to WASI u32 | Explicit low-32-bit conversion for direct exit and command return. | Checked exit-code type adds source representation work.  Trapping on overflow adds a guest failure path. |
| Exit acceptance | Standard host linking with accepted-exit and terminal host-failure outcomes.  A guarantee of return or designated exit requires host acceptance of every reached exit request. | Custom callback accepting every UInt32 changes embedding policy and exit classification. |
| Bytes | Single allocation root plus logical UInt64 length. | Length-prefixed, one-pointer object changes the byte host ABI and access proofs. |
| Read result | Errno-and-bytes record, empty on error. | Heap-valued sum requires a broader accepted sum representation. |
| Host errors | Permit the declared current-operation prefix and preserve prior effects.  Count is valid on success. | Unchanged-world error rule needs a stronger host guarantee. |
| Pure proof reuse | Prove import relocation and host-state execution transport, then compose. | Generalize shared compiler rules where the transport proof demonstrates a need. |
| Source monad | Semantic `Action` with checked reflection equations. | Opaque BaseIO primitives require an additional primitive/state correspondence. |
| Frontend | Separate `verified_compile_wasi` command, with an optional command entry. | Inferring an effect profile in `verified_compile` changes that command's accepted types and output selection. |
| Native API placement | Compiler-independent `LeanExe.Bytes` and `LeanExe.Wasi` modules. | Compiler-specific source APIs couple consumers to one compiler's namespace and module organization. |
| Effectful control flow | Bounded loops and an acyclic helper graph. | Unbounded structured loops require a general trace-prefix theorem and separate termination premises. |
| Depth accounting | Share the guarded-call depth through effectful and pure internal calls. | Independent counters require a combined frame bound to justify their interaction. |
| Application-ABI table | Add the narrow empty-table encoding profile and export required by the pinned convention. | An import-only profile without that export reduces proof work but differs from the pinned application-ABI convention. |
