# Formal Specification of LeanExe Compilation and Execution

## Subject and status

This specification defines the implemented LeanExe compilation and execution relation.  Its inputs are a checked Lean environment, a module name, an entry name, a compilation mode, and mode bounds.  Its outputs are a rejected compilation or an exact WebAssembly byte sequence.  Runtime behavior is a relation between initial and final WebAssembly configurations, including traps and host events.

The [Type Theory](leanexe-type-theory.md) defines recognized source types, static specialization, and the first-order runtime presentation.  This document completes that account with numeric operations, memory representation, ownership, collection operations, loops, wrappers, and proof boundaries.  It uses the compiler's exact function graphs for acceptance and lowering, and the selected WebAssembly semantics for execution.  This is an implementation-indexed specification.  A general theorem connecting an independent source semantics to every emitted binary remains an explicit proof obligation.

Fix a revision `v` containing the relevant Lean source files and pinned dependencies.  An uncommitted change to any of these files changes `v`.  The definitions refer to declarations rather than volatile proof-case counts.  [Compiler Architecture](compiler.md), [Language Specification](spec.md), and [Artifact Verification Format](artifact-format.md) provide the maintained prose accounts.

## Compilation relation

### Inputs, extraction, and rejection

Let `Q = (E, m, f, mode, bounds)`, where `E` is an environment imported by `Extract.Env.loadEnvironment`, `m` is the module name, and `f` is the fully qualified entry.  Environment import and file access can fail before extraction.  The exact environment includes elaborated declaration values and metadata.

Write `Graph(g, x, y)` when executing the specified implementation function `g` at revision `v` on `x` returns `y`.  Because some compiler functions are declared `partial`, this graph asserts a completed evaluation.  It asserts no general termination theorem for the compiler.

The extraction relation is:

```text
Extractv(E,m,f,library,M)
  iff Graph(compileEnvironment, (E,m,f), ok M).
```

The other modes use their corresponding `compile…ProgramEnvironment` function from [Module Extraction](../LeanExe/Extract/Core.lean).  A result `error message` defines extraction rejection.  The graph includes every body-recognition and ownership check.  A report classification supplies diagnostic evidence but does not replace this complete extraction result.

`compileEnvironmentWithEntryModeDetailed` performs the following ordered computation:

1. Resolve the entry and check its mode-specific signature.
2. Use `collectReachable` under `m.getRoot` to obtain the dependency list.
3. Apply `betaSpecializeExpr` with fuel `32` and collect synthetic structural helpers.
4. Extract the selected functions with empty fresh-result ownership summaries.
5. Compute `freshResultOwnerOffsetsForModule` from that first IR.
6. Check explicit releases with `validateModuleReleases` using those summaries.
7. Extract the functions again with the summaries and return the module and release judgments.

The dependency collector and body extractor jointly fix the accepted external frontier.  Compiler-recognized floating-point primitives use the five names in `compilerPrimitiveName`.  Other external declarations require their dedicated primitive or successful specialization path.  A function signature accepted in isolation supplies no proof that its body will extract.

### Modes and binary output

Let `Emitv(mode,bounds,f,M)` be the result of the named production serializer in `LeanExe.Wasm.Binary.CoreWasm`:

| Mode | Required source entry type | Extractor | Serializer |
|------|----------------------------|-----------|------------|
| Library | `τ₁ → … → τₙ → τ`, with public parameter and result layouts | `compileEnvironment` | `moduleBytes` |
| Stdout | `ByteArray` | `compileProgramEnvironment` | `wasiModuleBytes` |
| Stdin/stdout | `ByteArray → ByteArray` | `compileStdinProgramEnvironment` | `wasiStdinModuleBytes` |
| Stdin/exception | `ByteArray → Except ByteArray ByteArray` | `compileStdinExceptProgramEnvironment` | `wasiStdinExceptModuleBytes` |
| Argv/exception | `Array ByteArray → Except ByteArray ByteArray` | `compileArgvExceptProgramEnvironment` | `wasiArgvExceptModuleBytes` |
| Stdin/argv/exception | `ByteArray → Array ByteArray → Except ByteArray ByteArray` | `compileStdinArgvExceptProgramEnvironment` | `wasiStdinArgvExceptModuleBytes` |

The library serializer's result is a `ByteArray`; regard that return as `ok bytes` in this notation.  The complete relation is:

```text
Compilev(Q, bytes)
  iff ∃M. Extractv(E,m,f,mode,M)
       ∧ Emitv(mode,bounds,f,M) = ok bytes.
```

This relation defines emitted bytes.  WebAssembly validity is a separate premise:

```text
Executablev(Q,bytes,W)
  iff Compilev(Q,bytes)
       ∧ DecodeWasm(bytes) = W
       ∧ ValidWasm(W).
```

The separation is necessary for a precise description of the present compiler.  The source survey found that `reservedExportNames` rejects `memory`, `alloc`, and `reset`, while production export assembly also reserves `retain`, `release`, `free`, and the four counter names.  The documented rejection set therefore exceeds the current extraction check.  `moduleBytes` calls `legacyModuleBytes`; the experimental image validator's duplicate-export check is outside that production path.  This specification records the gap without adding an unimplemented rejection rule.

Binary emission lowers IR functions through `emitFuncInstrs`, encodes structured instructions, and assembles WebAssembly sections.  Library mode uses `legacyModuleBytes`; WASI modes use their dedicated serializers.  WAT rendering consumes the structured instruction representation in [WAT Rendering](../LeanExe/Wasm/Wat.lean).  Equality after an external WAT parse is a tested property of a concrete compilation.  It is separate from the definition of `Compilev`.

### Process outcomes

The command-line interface adds parsing, path, bound, and I/O checks around compilation.  [CLI Implementation](../LeanExe/CLI.lean) and [CLI Failure Interface](../DEVELOPING.md#cli-failure-interface) define status `2` for command use and bounds, `3` for source/project input rejection, `4` for I/O failure, and `5` for internal inconsistency.  A handled failure writes its category and command context to stderr.  A timeout or externally killed process is an execution outcome of the build environment, not an extraction rejection theorem.

## Values and memory representation

### Abstract values and scalar encoding

For each recognized runtime type, define values by:

```text
Val(Unit)       = {unit}
Val(Bool)       = {false,true}
Val(Uw)         = {n ∈ ℕ | n < 2^w}, w ∈ {8,32,64}
Val(Nat64)      = {n ∈ ℕ | n < 2^64}
Val(Bytes)     = finite sequences over Val(U8)
Val(Array τ)   = finite sequences over Val(τ)
Val(τ × υ)     = Val(τ) × Val(υ)
Val(Struct …)  = ordered tuples of retained field values
Val(Variant …)= a constructor index and its active field tuple
Val(Rec D τ̄)  = finite constructor trees of the specialized recursive family.
```

These value sets describe source-facing observations.  A source `Nat` outside the range has no `Nat64` representation.  A recursive tree may have a shared heap representation.  Cyclic or malformed host memory supplies no value through this finite-tree relation.

Let `μ` be byte-addressed WebAssembly linear memory, and `load64(μ,p)` the little-endian unsigned word at a valid eight-byte range.  Define `RepI(μ,τ,a,s̄)` for internal slot vectors and `RepP(μ,τ,a,s̄)` for public vectors.  Both relations include range-valid memory reads and the recursively stated payload relations.

`Unit` has internal slot `[0]`.  A Boolean has `[0]` or `[1]`.  `Uw` and `Nat64` use the word for `n`.  Public `U8` and `U32` input normalization applies `n mod 2^w` before source code observes the argument.  `Values.u8WrapExpr`, `u32WrapExpr`, and the parameter-binding functions fix that normalization.  A general host word for `Bool` has no Boolean representation unless it is `0` or `1`.

### Composite layouts

The representation clauses are:

```text
RepI(μ,Bytes,b,[o,p,n])
  iff n = length(b) ∧ μ[p … p+n) = b ∧ Owner(μ,o,p,n).

RepP(μ,Bytes,b,[p,n])
  iff n = length(b) ∧ μ[p … p+n) = b.

RepI(μ,Array τ,a,[o,p])
  iff load64(μ,p) = length(a)
       ∧ OwnerArray(μ,o,p)
       ∧ ∀i < length(a).
           RepI(μ,τ,a[i], slotsAt(μ,p+8+8*i*wI(τ),wI(τ))).

RepP(μ,Array τ,a,[p])
  iff the same header and element clauses hold with a borrowed outer owner.
```

`Owner(μ,0,p,n)` permits a valid borrowed byte range.  A nonzero owner is a live allocation root whose storage contains that range and whose lifetime covers its use.  `OwnerArray(μ,0,p)` permits a valid borrowed array.  A nonzero array owner identifies the live root governing that array.  Ownership accounting adds the reference-count and alias premises in the next section.  The host must establish these premises for owner slots embedded in array elements.

A product concatenates its two internal vectors.  A structure concatenates retained fields in declaration order.  A nonrecursive variant has a tag followed by reserved payload areas for every constructor, in declaration order.  The active area satisfies the field relations; inactive scalar contents have no source value.  Compiler-generated inactive heap-owner slots must satisfy the allocator's child-walk requirements, so arbitrary nonzero pointers in inactive owner positions cannot be justified by source-level tag inactivity.

A recursive value uses `[p]`, with a tag and flattened constructor payload areas in the pointed-to slot object.  `flattenArrayElementValue`, `valueFromInternalSlots`, and the heap-value flatteners in [Storage Lowering](../LeanExe/Extract/Storage.lean) and [Value Operations](../LeanExe/Extract/Values.lean) fix the offsets.  The child mask marks recursive pointers and owner slots, including owner slots nested in products, structures, and tagged values.

Public input bindings introduce owner `0` for top-level byte arrays and arrays.  Array elements retain their stored internal layouts.  Public output drops top-level owner slots.  Consequently a returned byte pointer may be a slice into a root or borrowed input; the public result alone does not identify a releasable allocation root.

### Address and resource premises

Source-facing memory statements require valid ranges, sufficient allocation capacity, and arithmetic that computes the represented addresses.  The emitted machine code uses `i64` arithmetic and `i32.wrap_i64` for memory addresses.  The complete compiled relation retains that wrapping behavior.  A theorem about mathematical array offsets must state bounds that prevent address wrap and ensure each accessed range lies in linear memory.

This specification supplies no inferred universal allocation bound for all accepted source inputs.  `rcArrayPayloadBytes`, `arraySlotAddress`, and the allocation emitters identify the arithmetic to bound in a program theorem.  Memory growth failure and invalid memory accesses are WebAssembly traps.

## Numeric and control operations

### Integers and binary64

Let `U = 2^64`, `maskw(n) = n mod 2^w`, and let `⊥trap` denote a trap outcome.  The implemented scalar rules, after operand evaluation in order, are:

| Operation | Result |
|-----------|--------|
| `Uw` addition, subtraction, multiplication | `maskw(a+b)`, `maskw(a−b)`, and `maskw(a*b)`, with modular subtraction |
| Unsigned division | `0` if `b=0`; otherwise `floor(a/b)` |
| Unsigned remainder | `a` if `b=0`; otherwise `a mod b` |
| `Nat64` addition | `a+b` if `a+b<U`; otherwise `⊥trap` |
| `Nat64` multiplication | `a*b` if `a*b<U`; otherwise `⊥trap` |
| `Nat64` subtraction | `max(a−b,0)` |
| `Nat64` successor and predecessor | Checked addition by one and saturating subtraction by one |
| Numeric comparisons | Unsigned comparison of represented values |
| Bitwise operations | Bitwise AND, OR, XOR, and complement on the represented word, with narrow-type normalization where required |
| Shifts on `Uw` | Shift count reduced modulo `w`, followed by result normalization to width `w` |
| Fixed-width conversion | Reduction modulo the target width when narrowing; value-preserving embedding when widening |

The mathematical subtraction in `maskw(a−b)` uses an integer intermediate.  The exact primitive-name recognition and normalization occur in `extractValueFrom`, `extractCondFrom`, and the scalar helpers in [Value Operations](../LeanExe/Extract/Values.lean).  Production behavior follows `emitCheckedDivMod`, `emitNatAdd`, `emitNatSub`, `emitNatMul`, their release-aware forms, and `emitU64Op` in [Binary Lowering](../LeanExe/Wasm/Binary.lean).

The binary64 interface has four binary operations and one unary operation:

```text
Fpopp(a,b,r)
  iff r ∈ reinterpretI64(Wasm.f64.p(reinterpretF64(a),reinterpretF64(b)))
       for p ∈ {add,sub,mul,div}.

Fpsqrt(a,r)
  iff r ∈ reinterpretI64(Wasm.f64.sqrt(reinterpretF64(a))).
```

These are the meanings of `LeanExe.Float64.addBits`, `subBits`, `mulBits`, `divBits`, and `sqrtBits` in generated code.  Arguments and results have source runtime type `U64`.  The emitter stages each operand and inserts reinterpretation around the corresponding instruction.  General WebAssembly execution admits allowed NaN results, so a theorem over arbitrary engines uses this result relation.  A theorem in a pinned deterministic Talos model states that model's result and requires a separate bridge for broader engine claims.  [WebAssembly Numeric Semantics](https://webassembly.github.io/spec/core/exec/numerics.html) specifies the permitted arithmetic results.  [Float Intrinsic Definitions](../LeanExe/Float64.lean) provide native Lean comparison functions.

### Branches, evaluation, and calls

For represented scalar conditions, `0` selects false and the accepted Boolean encoding `1` selects true.  `if` evaluates its condition and selected branch.  Boolean conjunction evaluates the right operand after a true left operand; disjunction evaluates it after a false left operand.  Matching evaluates the selected constructor arm.  Monadic `Option` and `Except` sequencing inspects the tag and skips the continuation on failure.

The extractor can defer local values, fields, and arguments through `Binding.thunk` and structured `ExtractedValue` constructors.  When it materializes a direct call, `emitExpr` evaluates arguments in list order and stores returned slots in the assigned locals.  `LocalLet.call`, statement-level calls, and branch materialization preserve a shared multi-slot result.  The precise evaluation schedule is the emitted instruction sequence, determined by extraction and demand analysis.

A generic claim that all accepted terms preserve a single eager or lazy source evaluator would exceed the current evidence.  The source comparison relation must account for the selected demand behavior, bounded numeric traps, and runtime intrinsics.  The present exact compiled relation has no such ambiguity because it executes the emitted instructions.

## Collections and iteration

### Arrays

For a represented finite sequence `a`, use `a[i]`, concatenation `++`, and half-open slices `a[s:t]`.  The following observations hold for in-range memory and successful allocation along the represented path.  Source-level argument evaluation and callback execution follow the emitted order described above.

| Family | Value behavior and boundary |
|--------|-----------------------------|
| Empty, singleton, literals, replicate | `[]`, `[x]`, the source-order sequence, and `n` copies of `x`.  Capacity parameters contribute no observed sequence data. |
| `size`, `isEmpty` | Length and comparison of length with zero. |
| Proof-indexed and bang reads | Element `i` for `i<len`; the emitted bounds failure traps. |
| Safe read, `getD`, `back?` | `some a[i]` or `none`; `getD` selects its fallback when absent; `back?` uses the final element when present. |
| Set and modify | Replace one in-range element; conditional forms return the old sequence when the index is invalid; bang wrappers trap on the invalid case. |
| Push and pop | Append one element; remove the final element when present. |
| Append and extract | Concatenate sequences; extract the clamped half-open window with empty result when the stop is at or below the start. |
| Insert and erase | Insert before `i` when `i≤len`; erase element `i` when `i<len`.  Conditional invalid cases preserve the old sequence; bang wrappers trap. |
| Swap and reverse | Exchange two valid indices; reverse the sequence.  Conditional invalid swap preserves the old sequence. |
| Map and filter | Visit elements in source order, applying the direct body; filter preserves the order of retained elements. |
| Find and optional find-index | Stop at the first true predicate result, returning its value or index; return `none` after exhausting the scan. |
| Any and all | Stop at the first decisive predicate result.  Empty scans return false for any and true for all. |
| Equality | Compare length first, then elements in order using the accepted element-equality operation. |

The exact source dispatch, optional arguments, and proof arguments occur in `extractValueFrom`.  The machine operations are `emitArrayAllocSlots`, `emitArrayLiteralSlots`, `emitArrayReplicateSlots`, `emitArraySize`, `emitArrayGetSlot`, `emitArraySetSlots`, `emitArrayPushSlots`, `emitArrayPopSlots`, `emitArrayAppendSlots`, `emitArrayExtractSlots`, `emitArrayMapSlots`, `emitArrayFilterSlots`, `emitArrayFindIdxSlots`, `emitArrayFindSlot`, `emitArrayAnySlots`, `emitArrayEqSlots`, `emitArrayInsertIfInBoundsSlots`, `emitArrayEraseIfInBoundsSlots`, `emitArraySwapIfInBoundsSlots`, and `emitArrayReverseSlots` in [Binary Lowering](../LeanExe/Wasm/Binary.lean).  Source wrappers determine whether an invalid index takes a conditional fallback or reaches `unreachable`.

Allocated updates copy sequence data and account for heap children through the child and owned-child masks.  Returning an unchanged array preserves its original owner slot.  A borrowed unchanged input remains borrowed.

### Byte arrays and static strings

Byte arrays use the same ordered sequence observations for size, empty, indexing, equality, push, append, set, and search.  `ByteArray.mk` from `Array UInt8` copies the represented bytes.  Extraction slices preserve the original owner while adjusting the visible pointer and length.  [Binary Lowering](../LeanExe/Wasm/Binary.lean) provides the `emitByteArray…` operations, while [Value Operations](../LeanExe/Extract/Values.lean) computes slice and conversion expressions.

For `copySlice(src, srcOff, dest, destOff, copyLen)`, define:

```text
k = min(copyLen, max(length(src)−srcOff,0))
p = min(destOff,length(dest))
q = min(destOff+k,length(dest))
result = dest[0:p] ++ src[srcOff:srcOff+k] ++ dest[q:length(dest)].
```

The byte-copy emitter implements these prefix, copied-range, and suffix segments.  `byteArrayCopySliceCopiedLen` and `byteArrayCopySliceResultLen` in [Value Operations](../LeanExe/Extract/Values.lean) fix the length arithmetic; the equations above assume that its machine addition computes the mathematical sum.

`toUInt64LE!` and `toUInt64BE!` require exactly eight bytes.  For `b₀,…,b₇`, they return `Σi bᵢ*2^(8i)` and `Σi bᵢ*2^(8(7−i))`.  Other lengths trap through `byteArrayLoadUInt64Checked`.

Compile-time strings form a separate static evaluator for ASCII literals, accepted local and constant bindings, and append.  Recognized consumers are UTF-8 byte conversion, length, emptiness, and equality.  A successful static result requires every encoded byte below `128`; `asciiStringBytes?` and the string-extraction paths define this check.  `LeanExe.AsciiString` is a represented structure over `ByteArray`; its checked constructors establish ASCII by explicit computation, while trusted constructors preserve their caller-supplied premise.

The ASCII and JSON modules are source libraries in the fragment.  Their definitions determine parser and renderer behavior.  They add no primitive type-formation or execution rule.  The [Language Specification's JSON section](spec.md#limited-json) records the restricted grammar and the weaker range-skipping behavior of the older scanner.

### Folds and loops

Let a fold state be `(i,a)`, with index `i` and accumulator `a`.  Forward array and byte-array folds use the interval `[start,min(stop,len))`.  On each visited element:

```text
(i,a) → (i+1, body(a,element[i])).
```

Array `foldr` starts with `i=min(start,len)`, visits `i−1`, and continues while `stop<i`.  Its callback receives the element and accumulator in the source operation's order.  Range loops visit `start, start+step, …` while the index is below `stop`; `emitRangeFoldMultiSlot` uses checked `Nat64` addition for the increment.  A zero step, if it reaches this machine loop, repeats the same index until a body exit.  Acceptance supplies no inferred nonzero-step invariant.

`ForInStep.done` terminates after producing its accumulator.  `yield` continues.  `Option` and `Except` folds and loops terminate on the first failure tag.  `Lean.Loop` repeats its accepted body until a done or failure result.  Nested loops compose these rules through their extracted bodies.

All accumulator result slots are staged before replacement.  The `…MultiSlotAssign` forms assign the result as a shared multi-slot computation.  Liveness pruning preserves an atomic materialized fold when any result slot remains live.  When the ownership analysis selects accumulator release offsets, the emitter skips release of the initial accumulator, stages a later replacement, releases the previous selected owned roots, and copies the staged replacement into the accumulator locals.  `emitGuardedAccumulatorReleases`, the fold emitters, and the assignment emitters in [Binary Lowering](../LeanExe/Wasm/Binary.lean) define the exact order.

Fuel recursion and structural recursion have the accepted shapes in [Type Theory](leanexe-type-theory.md#control-and-recursion-coverage).  Tail fuel recursion becomes an explicit loop with base and early-exit branches.  Expression-position recursive calls become direct calls with the predecessor or selected recursive child.  The compiled call/loop relation determines execution.  A source termination proof requires a representation and lowering theorem before it establishes termination of every emitted execution.

## Allocator and ownership transitions

### Heap state

Library mode exports memory initialized to `16` pages of `65536` bytes.  The heap top begins at `4096`.  The runtime has six `i64` globals: heap top, free-list head, allocation count, retain count, release count, and free count.  Each heap object has a `48`-byte header before its returned root pointer `p`:

| Address | Word |
|---------|------|
| `p−48` | Magic value `5501223100278326855` |
| `p−40` | Reference count |
| `p−32` | Payload capacity in bytes |
| `p−24` | Kind: raw bytes `0`, slots `1`, array `2` |
| `p−16` | Slot count for kind `1`; element width for kind `2` |
| `p−8` | Child mask for a live slots/array object; next pointer for a free block |

`rcHeaderBytes`, `rcMagic`, `rcInitHeader`, and `imageGlobals` in [Binary Lowering](../LeanExe/Wasm/Binary.lean) fix these constants and fields.  All counter increments use modular `i64` addition.  A theorem counting events in natural numbers must add a no-counter-overflow premise.

`alloc(len)` uses kind `0` and initial reference count `1`.  `rcAllocPayload` rounds the requested payload to eight-byte alignment with a minimum capacity of eight, searches the free list for the first block with enough capacity, and otherwise advances the heap and grows memory as required by the emitted arithmetic.  Reused blocks keep their capacity.  A successful call increments `allocCount`.  This describes the code's allocation order; bounds needed to interpret every size computation as natural-number arithmetic remain explicit representation premises.

### Retain, release, and reset

For a valid root, the observable transitions follow `coreRetainInstrs` and `coreReleaseInstrs`:

```text
retain(0) = 0, with no state change
retain(p), p≠0:
  require matching magic and positive stored count r
  retainCount := retainCount + 1 mod U
  rc(p) := r + 1 mod U
  return p

release(0): no state change
release(p), p≠0:
  require matching magic and positive stored count r
  releaseCount := releaseCount + 1 mod U
  if r>1 then rc(p) := r−1
  else release marked children in emitted traversal order,
       freeCount := freeCount + 1 mod U,
       rc(p) := 0,
       nextFree(p) := freeHead,
       freeHead := p.
```

An invalid header read, mismatching magic, or zero reference count traps.  A slots object scans its slot count.  An array scans its length and then each element's slots.  Every marked child word becomes a recursive call to release, and zero child words are no-ops.  Raw objects have no child walk.  The runtime tests stored kind values as emitted; the value-representation relation supplies the valid-kind premise.

The child mask is stored as one `i64`.  `heapChildMaskFromType` constructs natural-number masks, `Binary.i64Const` reduces constants modulo `2^64`, and `coreReleaseInstrs` tests each slot with `i64.shr_u`, whose count is modulo `64`.  Proofs of arbitrary-width layouts must therefore address mask truncation and repeated shift positions.  This survey found no general mask-width premise in the layout predicates.  These code facts identify an unresolved ownership boundary; no runtime reproducer ran during this documentation task.

`free` exports the release function under another name.  `reset` restores heap top to `4096` and sets the free-list head and all four counters to zero.  It preserves the allocated linear-memory page count and does not zero old payload bytes.  Every prior pointer loses its lifetime guarantee, because subsequent allocation can reuse that storage.

### Compiler ownership effects

The compiler marks child slots from type layouts.  Copying an existing owned child retains its root; a child recognized as fresh transfers its owned reference into the new parent without that retain.  Owner-zero children remain borrowed.  Fresh-result summaries from the first extraction pass guide this decision in the second pass.

Automatic local cleanup applies to supported nonrecursive byte-array and array temporaries that do not escape through the result or its borrowed roots.  Recursive temporaries can require an explicit release or an accepted accumulator-replacement boundary.  The relevant analyses are `heapChildMaskFromType`, owner-source tracking, fresh-result summaries, liveness, and release-offset selection in [Value Operations](../LeanExe/Extract/Values.lean).

An explicit source `LeanExe.Runtime.release` must satisfy `validateModuleReleases` in [Release Checking](../LeanExe/Extract/ReleaseCheck.lean).  It consumes the accepted root reference and returns the current free count in generated execution.  `LeanExe.Runtime` counter reads observe the generated globals.  Their ordinary Lean definitions all return zero, as does their limited IR interpretation.  The generated operations thus require the extended allocator semantics above in any preservation statement.

## WebAssembly execution and host boundary

### Complete operational relation

Let `→Wasm` be the selected WebAssembly small-step semantics, with explicit memory, locals, globals, call frames, operand stack, and host-import relation.  Let `Init(W,H,args)` be a valid instantiated configuration with host state `H` and a named exported invocation.  Define:

```text
Runv(Q,H,args,out)
  iff ∃bytes,W,c₀,cₙ.
       Executablev(Q,bytes,W)
       ∧ Init(W,H,args) = c₀
       ∧ c₀ →Wasm* cₙ
       ∧ Observe(cₙ) = out.
```

`out` records returned slot values and observable memory, a trap, or a host exit and byte-output trace.  An infinite reduction is divergence.  External execution limits are recorded separately from a semantic trap.  This relation covers every emitted instruction through the chosen WebAssembly semantics, including allocation, address wrapping, invalid inputs, and floating-point special values.

The WebAssembly stack-typing rules are the [Instruction Validation Rules](https://webassembly.github.io/spec/core/valid/instructions.html).  Program proofs in this repository use the pinned Talos execution relation.  A claim about Talos execution names that model and its premises.  A claim about every conforming engine additionally needs a model-to-standard relation or a theorem stated against the standard semantics.  Conformance tests supply finite test evidence.

### Library ABI

The library exports `memory`, `alloc`, `reset`, `retain`, `release`, `free`, the four counter globals, and the entry under the final component of its Lean name.  Every source ABI slot is `i64`.  The entry receives and returns the flattened public layouts defined above.  Host input must supply valid encodings and accessible memory.  A host that consumes a result must preserve its storage lifetime until all reads finish.

The representation relation defines meaningful source observations for valid input.  The broader machine relation also describes executions on malformed tags, forged pointers, invalid owner slots, and stale memory.  Such executions carry no inferred source value or source theorem.

### WASI adapters

The fixed adapters import from `wasi_snapshot_preview1` and export `_start` and memory.  Successful writes use one `fd_write` call for the selected pointer-length range, require error code zero, and require the reported write length to equal the requested length.  A failed or short write traps.  Stdout uses descriptor `1`, and stderr uses descriptor `2`.

For stdin, let `b` be the configured byte bound.  The adapter reserves `b+1` bytes, repeatedly reads through `fd_read`, stops at EOF, and traps when the accumulated count exceeds `b`.  The compile-time limit is:

```text
b ≤ 16*65536 − 4096 − 1.
```

For argv, let `a` be the maximum number of user arguments and `g` the maximum WASI argument-buffer byte count.  The reserved storage is:

```text
R(a,g) = 8 + 24*a + 4*(a+1) + g.
```

Argv mode requires `R(a,g) ≤ 16*65536−4096`.  Combined stdin/argv mode requires the stdin bound above and `b+8+R(a,g) ≤ 16*65536−4096`.  Runtime `args_sizes_get` and `args_get` results must respect the configured limits and report success.  The adapter skips `argv[0]`, builds an array of owner-zero byte strings, and passes the array with owner zero.  The byte bound includes `argv[0]` and NUL terminators.

An `Except.ok` result writes stdout and returns.  An `Except.error` result writes stderr and calls `proc_exit(1)`.  An invalid result tag traps.  The exact import indices, local assignments, buffer layout, and branch order are defined by `wasiReadStdinLoop`, `wasiReadArgvArrayWithImports`, `wasiWriteFd`, and the six `wasi…StartBody`/serializer paths in [Binary Lowering](../LeanExe/Wasm/Binary.lean).

These traces assume WASI imports implement their specified interface.  User source retains a pure entry type; the generated adapter supplies environmental input and output.

## Evidence and coverage

### Implemented and proved boundaries

| Boundary | Executable definition or evidence | Scope |
|----------|-----------------------------------|-------|
| Source typing | Imported declarations checked by pinned Lean | Source terms and proofs in that environment |
| Runtime types and layouts | `Extract.Types` recognizers | Exact accepted representation grammar |
| Specialization and terms | `Extract.Core`, `Patterns`, and `StructuralRec` | Successful algorithm graph, with bounded normalizers |
| Demand and ownership | `Demand`, `Values`, and `ReleaseCheck` | Executable analyses; general soundness remains unproved |
| Integer and binary64 lowering | `CoreWasm.emitExpr` and numeric emitters | Exact emitted instruction sequences |
| Arrays, bytes, loops, recursion | Collection emitters and direct call/loop lowering | Complete machine behavior through `Runv` |
| ABI and allocator | Parameter flattening, runtime functions, and serializers | Exact slot layout and machine transitions |
| WASI | Fixed wrapper emitters | Bounded input and output traces with stated host behavior |
| ASCII and JSON | Accepted source library definitions | Library behavior through ordinary extraction |
| IR reference evaluator | `IR.Expr.eval`, `Stmt.eval`, and `Extract.Eval` | Restricted diagnostic comparison, described below |
| Scalar emitter certificates | [Scalar Certificates](../LeanExe/Wasm/ScalarCertificate.lean) | Successful descriptor recognition implies equality with emitted instructions |
| LEB128 lemma | [LEB128 Theorems](../LeanExe/Wasm/LebTheorems.lean), `u32lebU64_eq_lebList` | The named unsigned encoding equality |
| Exact artifact decoding | [Decoder Soundness](../proofs/talos/lean/Project/Artifact/Binary/Proof/Decode.lean), `Wasm.Binary.Proof.decode_sound` | Successful restricted decoder result satisfies `Grammar.Encodes` |
| Exact artifact validation | [Validator Soundness](../proofs/talos/lean/Project/Artifact/Binary/Proof/Validate.lean), `Wasm.Binary.Proof.validate_sound` | Successful restricted validator result satisfies `CoreValid` |
| Artifact behavior | Exact-byte identity, translated-module equality, and the package's named theorem | One byte sequence and its stated behavior premises |

The exact decoder and validator declarations and their namespaces are specified in [Artifact Verification Format](artifact-format.md).  An artifact package must identify the bytes, decoded module, validated translation, and behavioral theorem.  Its restricted profile excludes WASI imports, so the generic WASI rows above acquire no artifact certificate from that profile alone.  The [Talos Proof Inventory](../proofs/talos/README.md) records current named program and runtime theorems, including the recursive teardown theorem `release_frees_tree` with its heap-tree, separation, and memory premises.

`ScalarDescriptor.Expr.ofIR_emitWithRelease`, `Cond.ofIR_emitWithRelease`, `Stmt.ofIR_emit`, and the related loop/index certificates establish instruction equalities when descriptor reification succeeds.  These statements concern those exact emitters and descriptors.  They do not quantify over every extraction pass or every source term.

### IR reference evaluator limits

`IR.Expr.eval` in [IR Definition](../LeanExe/IR/Core.lean) returns zero for `trap`, counter reads, releases, heap allocation, heap loads, and several collection operations.  Some update cases return an existing pointer expression.  `natAdd` and `natMul` use word arithmetic without the backend's overflow traps.  Loop evaluation also uses an implementation safety bound.

`Extract.Eval.evalEntry` limits the exposed evaluator to scalar arguments, scalar-slot results, and a module passing `scalarModule`.  This excludes heap operations, but its predicate admits `trap` and checked-Nat arithmetic.  Therefore `eval-ir` equality is useful only when the compared execution avoids those semantic differences and stays within its evaluator bounds.  It is not the definition of `Runv`.

### Remaining specification and proof work

The function-graph definitions make the current compiler and compiled behavior precise.  An independent formal language specification would additionally need mechanized syntax and judgments, a source operational relation covering demand and explicit runtime effects, and proof of agreement between those definitions and the implementation.  The required statements include:

```text
Extraction typing:
  Extractv(E,m,f,mode,M) → SlotWF(M).

Emission validity:
  Extractv(E,m,f,mode,M) ∧ wellFormedModeBounds
  → ValidWasm(DecodeWasm(Emitv(mode,bounds,f,M))).

Source refinement:
  SourceEval(E,f,a,result) ∧ representedInput(a,H,args)
  ∧ boundedArithmetic ∧ validOwnership ∧ sufficientResources
  ∧ agreedRuntimeIntrinsicSemantics
  → compiled observations satisfy representedResult(result).
```

These displays are proposed theorem shapes, not asserted theorems.  They need precise source evaluation, trap, divergence, nondeterminism, frame, and resource predicates before mechanization.  A refinement theorem must preserve the chosen source behavior and handle every allowed target outcome.  Successful compilation cannot serve as the proof of its own semantic correctness.

The source survey identified the following concrete review items:

| Item | Evidence and required resolution |
|------|----------------------------------|
| Reserved export names | Extraction checks three names while production exports reserve ten.  Decide and implement the documented rejection before claiming general emission validity. |
| Heap child-mask width | Type layouts construct unbounded natural masks, while runtime headers store one word and shifts mask their counts.  Establish an accepted-layout bound or specify and verify a wider representation. |
| Proof-erasure stage | Constructor and specialization code performs proof erasure on imported expressions.  The compiler overview's statement that Lean has completed proof erasure before extraction needs qualification. |
| Evaluation equivalence | Demand-based extraction, bounded-Nat traps, runtime intrinsics, and the limited IR evaluator require distinct semantic relations and explicit transfer premises. |
| NaN and runtime models | General WebAssembly allows multiple NaN encodings.  Pin each model and state the bridge needed for exact-word claims across engines. |

These items were reported during documentation work.  No acceptance rule, implementation, dependency, or proof changed as part of this specification draft.
