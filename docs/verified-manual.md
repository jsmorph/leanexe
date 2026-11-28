# Verified Compiler Manual

This manual describes the verified compiler's pure dialect, the `verified_compile` command and its generated theorems, allocation and depth bounds, the Wasmtime and WebGPU hosts, programs that call WASI Preview 1 and their AArch64 Linux executables, tests, examples, and the runner `tools/leanrun`.  [The WASI manual](wasi.md) describes in detail the separate `verified_compile_wasi` command, which compiles Lean actions that read and write the standard streams, make the flat calls of WASI Preview 1, open files under a preopened directory, exit, and loop as processes without an iteration bound.  [The AArch64 document](a64-bare-metal.md#the-linux-target) describes the Linux executables that the AArch64 back end writes.  [The README](../README.md) describes the repository and its artifacts.  [The verified compiler's internals](../Verified/README.md) describe its code scheme and the structure of its proof, and [the design document](design.md) gives the decisions and the open work.

## Compiler, theorems, and trusted base

### One theorem for every program

The verified compiler is a Lean function, `compileWith` in [`Verified/Compile.lean`](../Verified/Compile.lean), from a typed source language to a module of Talos, the WebAssembly interpreter written in Lean.  [Program correctness with a static pool](../Verified/Correct.lean), `Prog.correctStaticWith`, states that every source program computes its meaning when the supplied static pool covers its literals.  `Prog.correctWith` specializes the theorem to a program with no nonempty byte literals, and `Prog.correct` does so without tables.  The command `verified_compile p := [f, g, …]` reads ordinary Lean definitions, writes each as a source function, and proves with kernel-checked equations that each source function means its definition.  It then states, for each definition `f`, that the module computes `f` with Lean's own types, and that the module's bytes decode to the module.  The reflector that writes the source functions is meta code and is not trusted: a wrong reflection makes an equation fail in the kernel and cannot produce a false theorem.  `Verified.WGSL.compile` also translates supported typed array builds to WGSL and returns a kernel with proofs of its translation and local layout, as [the WGSL section](#wgsl-kernels) describes with that subset and its dispatch theorem.

### The `implements` and `trapFree` theorems

For a program with an empty byte-literal pool, `p.f.implements` states `ImplementsA aborts p.module k f` ([`LeanExe/Pipeline/Implements.lean`](../LeanExe/Pipeline/Implements.lean)), where `k` is the index of `f`'s function or entry in the module.  From any heap and store with the allocator invariant, a memory cap of at most 65,535 pages, and arguments that represent `x`, whose moved blocks are disjoint from one another and from the memory that the call reads, a run returns words that represent `f x` and that the caller owns.  The run keeps the allocator invariant and the cap, keeps every region of the caller's heap that is disjoint from the moved blocks, and places the result outside those regions.  When `aborts` is true, a run may instead trap at `unreachable`, which the code does only when an allocation finds no memory, an array would hold `2^29` words or more, a byte builder requests at least `2^32` bytes, or a recursion reaches depth 1,000.  `aborts` is true when the function's result holds arrays, a parameter is owned, the body builds, updates, extends, inserts into, or removes from an array, or the body calls a function whose `aborts` is true, whose code takes the call depth, whose result holds arrays, or which owns a parameter.  Byte construction and literals, and list construction and matching, also enable `aborts`.  The compiler uses this flag conservatively.  A generated `trapFree` theorem excludes a trap under its allocation bound and frames condition.

With an empty byte-literal pool, `p.f.trapFree` states `ImplementsA false` for each source function, and `ImplementsTables false` for a wrapper whose callee takes no call depth: the call returns `f x` without a trap and increases `top` by at most the function's allocation bound.  When `aborts` is true, the theorem requires a store in which `top` is at least the bound below the memory cap.  For a function whose code takes the call depth, it also requires a frames condition, which states that every call of the run to a function of this kind happens below depth 1,000.  The reflector also states the bound and the frames condition as Lean terms in the function's parameters, so a concrete bound follows by rewriting, as [Bounds](#bounds-and-total-execution) describes.

A program with nonempty byte literals uses [the static call specification](../Verified/StaticImplements.lean), `ImplementsStatic p.literalPool aborts p.module k f tables Pre Post`.  `tables` is empty for a source function and contains the borrowed tables for a wrapper.  The specification adds `p.literalPool.Input heap store words x` as a separate premise on the machine argument words.  [The static input predicate](../Verified/Bytes/StaticInput.lean) requires the pool's bytes and heap region to be present and the blocks consumed by the call, `Represent.moves store words x`, to be disjoint from that region.  The argument representation, table, heap-preservation, and result-ownership requirements remain the same.  `p.f.trapFree` uses `ImplementsStatic` with `aborts = false`, requires `Heap.Within` for its allocation bound, and adds the frames condition for guarded calls.  Wrappers in these programs also receive this theorem, with the allowance stated by `Wrapper.bound`.  [The static program rules](../Verified/ProgramStatic.lean) state these preconditions and postconditions.

For scalar arguments and results in a program with an empty byte-literal pool, `p.f.pure` states `ImplementsPureA aborts`: every sufficiently
fueled call returns the Lean result and preserves the whole store, or takes the permitted trap.
It holds for a call from any store.  The command generates this theorem when its instruction rules prove
store-independent execution.  Those rules cover scalar arithmetic and conversions, local
variables, branches, loops, and calls to earlier functions with generated store-preservation
proofs.  This proof generator does not cover heap operations and guarded self-calls.  The
[scalar composition example](../Verified/Examples/ScalarComposition.lean) contains generated
theorems for both float widths, word division, tail recursion, and call chains.

### Trusted base

[The trusted-base document](trusted-base.md#wasm-webassembly-modules-of-the-verified-compiler) lists the trusted components of every artifact, with the check and the source of each.  The trusted base is Lean's kernel with the axioms `propext`, `Classical.choice`, and `Quot.sound`, Talos's semantics, the binary decoder, and the step from a constant to a file that [the module emitter](../tools/Emit.lean) performs.  The statements of the verified compiler add definitions of their own: `Heap.Within` in [the runtime facts](../Verified/RuntimeFacts.lean), which states that `top` plus a bound is at most the memory cap, the allocation bound of [the bound definitions](../Verified/Bound.lean), `ImplementsTables` for wrappers, and `initialHeap` and `tableAddr`, which `p.initial` uses.  The kernel checks the reflected equations, bound equations, and compiler proofs.  The theorems of a WASI program add the model of the WASI host that [the trusted-base document's WASI section](trusted-base.md#wasi-wasi-preview-1-modules) lists, and those of its AArch64 Linux executable add the items of A64 and the model of the Linux process, which [its A64L section](trusted-base.md#a64l-aarch64-linux-executables) lists.

A statement's meaning comes from the definitions that it unfolds to.  In `LeanExe/Pipeline/` these are `Implements`, `ImplementsA`, and `Satisfies`, with `Separate`, `Apart`, and `Moved`; the class `Represent` and its instances, among them those of [the byte representation](../LeanExe/Pipeline/Bytes.lean), [the flat records](../LeanExe/Pipeline/FlatRecords.lean), and [the moved tuples](../LeanExe/Pipeline/MovedTuples.lean); `Encode` and `EncodeWellFormed`; `Node` with `NodeOwned`, `NodeBorrowed`, and the record and slot predicates that they use, in [the `Implements` definitions](../LeanExe/Pipeline/Implements.lean); and the `Heap` predicates of [the runtime model](../LeanExe/Pipeline/Runtime.lean).  These definitions use definitions in other directories: `UInt64Array.At` in [the array lemmas](../LeanExe/ProofKit/Array.lean), which fixes the layout of every array; `FreeNode`, `freeHead`, `FreeNode.region`, and `FreeListAt` in [the free list](../LeanExe/Runtime/FreeList.lean); `regionsDisjoint` in [the model of release trees](../LeanExe/Runtime/Tree.lean); and `LeanExe.Bytes` in [the byte dialect](../LeanExe/Dialect/Bytes.lean).  A statement over a type with an `Encode` or `Flat` instance also uses that instance, which a reader finds beside the type unless the `Implements` definitions give it, as they give `Encode (List UInt64)` and `Flat Bool UInt64`, or [the `Int64` representation](../LeanExe/Pipeline/Int64.lean) gives it, as it gives `Flat Int64 UInt64`, which states that an `Int64` is the word `x.toUInt64`.  The namespace `LeanExe.Pipeline` does not mark trust: modules in other directories, such as [the release proof](../LeanExe/ProofKit/ReleaseTree.lean), declare names in it, and the files under `LeanExe/Pipeline/` also hold lemmas.  A lemma, in any directory, can only make a proof fail and never changes what a statement says.

The native theorems add the statements of the translation to C.  `p.f.native` states `NativeImpl`, defined from `NativeA`, both of [the native theorems](../LeanExe/Native/Proof/Native.lean), or `NativeTablesImpl` from `NativeTablesA` or `NativeStaticImpl` from `NativeStaticA`, all four of [the native wrappers](../Verified/Native.lean), and `p.f.nativeAligned` states `NativeAlignedImpl` from `NativeAlignedA` of [the aligned native step](../LeanExe/Native/Proof/AlignedNative.lean) or `NativeTablesAlignedImpl` from `NativeTablesAlignedA` of [the aligned wrappers](../Verified/AlignedNative.lean), with `AlignedInput` and `AlignedOutput` of [the alignment predicates](../LeanExe/Pipeline/AlignedImplements.lean) and `Heap.Aligned` of [the aligned heap](../LeanExe/Pipeline/AlignedHeap.lean).  `NativeAlignedA` differs from `NativeA`, and `NativeTablesAlignedA` from `NativeTablesA`, by exactly the premise `AlignedInput` and, after a return, the conclusions `heap'.Aligned` and `AlignedOutput`.  `NativeAlignedImpl` and `NativeTablesAlignedImpl` take the theorem of `ImplementsA` or `ImplementsTables`, as `NativeImpl` and `NativeTablesImpl` do, and differ from them only in the statement that they name.  These use `Env`, `StoreRel`, and `StatusRel` of [the relation](../LeanExe/Native/Proof/Relation.lean), `EnvOk` of [the straight-line proofs](../LeanExe/Native/Proof/Straight.lean), `ArgsTyped`, `argVals`, and `ResultRel` of [the call proofs](../LeanExe/Native/Proof/Calls.lean), `translate`, `Translation`, `funId`, `signatureOf`, `trapUnreachable`, and `nativeCap` of [the translator](../LeanExe/Native/Translate.lean), and `eval_funcall` and `bigstep_program_terminates` of [the big-step semantics](../LeanExe/Native/Clight/Bigstep.lean), with the rest of the Lean copy of Clight in [`LeanExe/Native/Clight/`](../LeanExe/Native/Clight).

The bare-metal statements add a whole program to the native ones.  The theorem `p.f.program` that `bare_program` of [the bare-metal command](../Verified/Bare.lean) proves uses `bareProgram` of [the whole program](../LeanExe/Native/Proof/Whole.lean), `bareMain`, `OutKind`, `encodeWord`, `encodeArray`, and `outTrace` of [the generated `main`](../LeanExe/Native/Bare.lean), `PrefixOk` of [the bare-metal proof](../LeanExe/Native/Proof/Main.lean), and `E0` of [the events](../LeanExe/Native/Clight/Events.lean).  `sha256_input` uses `inProgram` of the whole program, `inMain`, `inMax`, and `inTooLong` of the generated `main`, `Reads`, `InResultRoom`, `inTrace`, `inLen`, and `inMsgByte` of [the input program](../LeanExe/Native/Proof/Input.lean), and `shaOut` and `message` of [the test's theorem](../tests/TestSupport/Bare/Input.lean), whose output is `SHS.SHA256.Impl.sha256` of [the SHA-256 implementation](../Library/Hashing/Sha2/Impl/SHA256.lean).  `InResult` also allows a run that ends with the code of `unreachable` and no output when `alloc` traps.  [The Rocq composition](../rocq/Clight2Asm.v) transfers such a termination to the Asm program, and its theorems state that step in CompCert's own Coq definitions of Clight and Asm.

Every statement about a value of a recursive type uses its representation in [the `Implements` definitions](../LeanExe/Pipeline/Implements.lean): the null pointer, or a record whose header holds a mask of the slots that hold pointers.  A slot holds a word, a pointer to a child record, a pointer to an array object (`Slot.array`), or the root of a byte buffer (`Slot.bytes`).  The field `lengths` of `RecordHeader` and `RecordSlots` requires that the slot after a buffer's root is a word slot that holds the buffer's length.  An array in a record is owned or borrowed as an `Array UInt64` argument is, through `Heap.Owned` and `Heap.Borrowed`, and a buffer as a `LeanExe.Bytes` argument is, through the buffer predicate `Heap.Buffer` of [the runtime model](../LeanExe/Pipeline/Runtime.lean).  A borrowed buffer, in a record or as an argument, meets the full `Heap.Buffer`, including the count of 1.  In a record, a buffer's root is 0 exactly when the buffer is empty.  A `LeanExe.Bytes` parameter may instead have a nonzero root and no bytes, which a record cannot hold.  The blocks of a value, the regions that a call reads, and the objects that a moved value consumes include its arrays and nonempty buffers, and `release` frees them with the records.

`RecordHeader` has two conditions on the value alone, at most 64 slots in a record and a word slot that holds a buffer's length after each buffer slot, and `RecordSlots` has the second.  An encoding that violates the length condition makes `Represent.borrowed` and `Represent.owned` false for its values in every store, and one that violates the slot bound makes `Represent.owned` and the precondition of a moved value false, while a borrowed value can still be represented.  An `Implements` statement over the type then holds for every module whenever the type is an argument, for a violated length condition, or a moved argument, for a violated slot bound.  A type that appears only as a result constrains nothing in either case, because only modules that always trap satisfy the statement, and those satisfy every `Implements` statement.  The `Represent` instances of a type with `Encode`, in [the `Implements` definitions](../LeanExe/Pipeline/Implements.lean), require the class `EncodeWellFormed`, which states both conditions for every record of every value.  `verified_recursive_type` proves the theorem `wellFormed` and, unless the type has one, the instance for every type that it declares, from the layout of the type's tree, the encodings of `List UInt64`, `Words`, and `KeyTree` prove it by hand, and the typed-tree audit fails for a recursive type of its example without the theorem.  With the instance, a reader of an `Implements` statement over the type can exclude the possibility that it holds vacuously because of these two layout conditions.  Values too large for 32-bit memory have no representation, such as a buffer of 2^32 bytes or an array of about 2^29 words, which limits single values and never every value of a type.

WGSL dispatch uses the shared [device model](#the-wgsl-library-and-the-browser-pages)
with strict binary32 arithmetic.  Its theorems prove successful modeled execution and race freedom
under their buffer, count, and invocation bounds, and `Dispatch.executions` extends them to every consistent execution under a Lean statement of the Vulkan memory model.  That statement, the guarantees of WebGPU that it uses, and a GPU's arithmetic are trusted, as [the WGSL kernels of the trusted-base document](trusted-base.md#wgsl-wgsl-kernels) state.

### Outside the proofs

The theorems hold in Talos's semantics, which bounds no call depth and grows memory whenever the new page count is within the cap.  Wasmtime ends a deep recursion with a stack-overflow trap, so guarded code traps at depth 1,000, and the pure reflector limits the frame of every function whose code takes the call depth to 32 positions, which [Calls and recursion](#calls-and-recursion) relates to Wasmtime's stack and [the module cases](#module-cases) test at depth 999.  [The WASI compiler](wasi.md#callable-and-command-modules) permits larger acyclic effectful helpers under its separate call-chain stack check.

`p.initial` proves that the modeled initial store meets the allocator invariant and the cap and holds the tables.  With a nonempty literal pool, it also proves the pool's static contents and heap region.  A later call must establish separation from its consumed argument blocks.  The proofs do not cover real engine instantiation or the host programs that run the modules, such as the Wasmtime host.  The WASI theorems state a program's ordered I/O in Talos's semantics under the host assumptions that [the WASI proof premises](wasi.md#execution-proofs-and-their-premises) describe, and the theorems of a WASI command's Linux executable state its run in a model of the Linux process, whose agreement with Linux no theorem states.  The floating-point theorems describe the WebAssembly deterministic profile.  The numerical examples have further theorems about mathematical functions, rounding, and exceptional values, with the domains and bounds listed in [the algorithm index](../index.md) and each function's document.

## The dialect

[`Verified/Source.lean`](../Verified/Source.lean) defines the source language: the types `Ty`, the element types `Elem`, the expressions `Expr S Γ t`, typed by the callees' signatures `S` and the context `Γ`, and their meaning `denote`.  A program consists of ordinary Lean definitions, which the reflector translates into this language.  The reflector's error messages name the term or the type that it cannot translate.

### Programs and definitions

A program is the list of definitions in `verified_compile p := [f₁, …, fₙ]`.  A definition may call the definitions before it in the list and, when it is recursive, itself, so the only cycles are a definition's calls of itself.  When no source rule covers a term, the reflector unfolds a helper marked `@[inline]`, including an `abbrev`, and checks the equation for its expanded body.  A listed helper compiles as a function and takes precedence over unfolding.  A named constant that holds no array is reflected as its value.  The reflector reads a recursive definition through its unfolding equation `f.eq_def`, so it accepts structural and well-founded recursion, and it rejects a definition with universe parameters and a recursive definition that uses `sorry`.

### Types

| Type | Representation | Notes |
|---|---|---|
| `UInt64` | One i64 word | Arithmetic wraps modulo `2^64`. |
| `Int64` | One i64 word, its two's-complement bits | `Flat Int64 UInt64` of [the `Int64` representation](../LeanExe/Pipeline/Int64.lean).  Arithmetic wraps modulo `2^64`, and the order, division, remainder, and right shift are signed. |
| `Bool` | One i64 word, 1 or 0 | |
| `Float` | One f64 word, its bit pattern | Lean's binary64, which equals Talos's `IEEE64` on bit patterns. |
| `Float32` | One f32 word, its bit pattern | Parameters, results, tuples, arrays, and loop state, with binary32 operations. |
| Pair of types without arrays | Words of the first component, then those of the second | Nested pairs are tuples. |
| Structure with a `Flat` instance whose tuple is its fields | Its fields' words | Nested structures flatten in turn. |
| Enumeration with a `Flat` instance to a word | One word | Inductive type whose constructors have no fields. |
| Sum with scalar fields and a `Flat` instance | Word tag and words of the constructor fields | Tag occupies the tuple's first leaf.  Each constructor's fields occur once. |
| `Array α`, for `α` a word, `Int64`, `Bool`, float, tuple, flat structure, enumeration, or sum | Address of a length word followed by the elements' words | Element of `k` words occupies `k` consecutive words.  An array of tuples may only be a local value, since Lean has no `Represent` instance for it. |
| `LeanExe.Bytes` | Allocation root and UInt64 logical length | Packed bytes, with owned and borrowed parameters, results, pairs, updates in place, copying, and release. |
| Pair that holds arrays, or structure whose `Flat` tuple holds arrays | Its components' words | Structure of this kind is a record with array fields. |
| Sum with a `Flat` instance whose tuple holds `Bytes`, arrays, or recursive types | Word tag and words of the tuple's components | Inactive components hold the instance's values: `Bytes.empty` and a null tree allocate nothing, and `#[]` allocates an empty array.  A parameter is owned when the function consumes it and no match alternative names it, as [the sum section](#records-tuples-and-sums) states. |
| `List UInt64` | Null for `[]`, otherwise a record holding the head word and tail pointer | Construction, matching, identity, duplication, tuples, calls, tail recursion, and folds with scalar state |
| Recursive type whose fields are `UInt64`, `Bool`, `Float`, `Float32`, arrays of these, `LeanExe.Bytes`, types with a `Flat` instance whose flattening holds these, or the type itself | Null for the first constructor without fields, and for any other constructor a record of its word and child fields in declaration order, then its array and buffer fields in declaration order, a buffer as its root followed by its length, after a tag word that holds the constructor's index when the type has more than one record constructor.  A `Bool` slot holds 1 or 0, a `Float` slot its bit pattern, and a `Float32` slot its bit pattern in the low 32 bits.  A field of a type with a `Flat` instance occupies one slot for each leaf of its flattening, in order. | Each record has between 1 and 64 slots, the tag included, at least one constructor has no child field, and at least one has a child field.  Construction, one-level matching, guarded and tail recursion, identity, duplication, tuples, calls, and loop state.  A type with a field that holds an enumeration or a sum cannot be a parameter of a recursive or tail-recursive definition. |

`Nat`, `Int`, `Int8`, `Int16`, `Int32`, `String`, `Option`, recursive types outside the listed layout, and arrays of arrays are outside the dialect.  Integers are `UInt64` and `Int64`, so that a program and its module compute the same values, wraparound included.  A read past the end of an array gives Lean's default element, whose flattening must have zero words.  An array stores each Float32 bit pattern in the low 32 bits of an eight-byte word.

`LeanExe.Bytes.empty` returns an empty buffer.  `bytes.size` returns its UInt64 length, and
`bytes.get index` returns a byte as a UInt64, or zero when the index is past the end.
`LeanExe.Bytes.build count f` takes a UInt64 count and stores the low eight bits of each UInt64
callback result.  A zero count skips allocation and the callback.  The code checks the count
before allocating the result and traps when the count is at least `2^32`.  Memory exhaustion may
also cause a trap under the allocation bound.

`bytes.set index byte` is `LeanExe.Bytes.set`: the buffer with byte `index` replaced by the low
eight bits of `byte`, or the buffer unchanged when `index` is not below its size, as `set!` leaves
an array.  The source expression `Expr.bytesSet` compiles as `set` does: an owned buffer that dies
at the update keeps its block and receives the byte there, and any other buffer is copied first.
Its charge in the generated bound is `Var.ownedCost` of the buffer, 0 for an owned buffer at its
last use and the copy's block otherwise.  A loop whose state holds a buffer, or a function that
takes a buffer as an owned parameter and returns it, therefore writes the buffer in place, as
`fillFrom` of [the byte update examples](../Verified/Examples/BytesSet.lean) does, while
`setKept` of the same examples reads its buffer after the update, so that update writes into a copy.

`bytes![65, 0, 255]` constructs a `LeanExe.Bytes` literal.  Each numeral must be between 0 and
255.  Each evaluation of a nonempty literal allocates a fresh owned buffer and copies the bytes
into it.  `bytes![]` returns `(0, 0)` without allocating.  Literals work inside ordinary, guarded,
and tail-recursive helpers, loop bodies, and build and fold callbacks.  [The literal examples](../Verified/Examples/Literals.lean)
cover these positions, repeated literals, conditional selection, and computed byte indices.

The compiler deduplicates nonempty byte lists across the program in `p.literalPool` and stores
their concatenated raw bytes in a data segment after the constant word-array tables.  The allocator
starts at the eight-byte-aligned end of this pool.  Deduplication shares the static source bytes.
Each evaluation still allocates and copies its result.  [The pool definitions](../Verified/Bytes/LiteralPool.lean)
and [literal-copy correctness](../Verified/AlignedBytes.lean) give the layout and allocation rules.
For a program without literals, [the empty-pool equality](../Verified/LiteralCodeEq.lean) states
the module that `compileWith` produces: the table segments are its only data, its memory size and
heap start depend only on the tables, and its functions use the empty pool.
`tests/verified/run.sh --check-bytes DIRECTORY` compares the emitted modules with saved reference
modules, such as those of another build of the verified compiler.  [The WASI manual](wasi.md#packed-bytes) describes the same byte values in actions: reads and flat calls return them, and writes and flat calls take them.

### Expressions

| Construct | Lean forms |
|---|---|
| Word arithmetic | `+`, `-`, `*`, `/`, `%`, `&&&`, `\|\|\|`, `^^^`, `<<<`, `>>>`, `min`, `max` |
| Word comparisons, unsigned | `==`, `!=`, `<`, `≤`, `>`, `≥`, `=`, `≠` |
| `Int64` arithmetic | `+`, `-`, `*`, `/`, `%`, `&&&`, `\|\|\|`, `^^^`, `<<<`, `>>>`, negation, `min`, `max`, literals such as `-5` and `Int64.minValue`, `x.toUInt64`, `w.toInt64` |
| `Int64` comparisons, signed | `==`, `!=`, `<`, `≤`, `>`, `≥`, `=`, `≠` |
| `Int64` conversions | `a.toFloat`, `a.toFloat32`, `x.toInt64`, `y.toInt64`, with `a : Int64`, `x : Float`, and `y : Float32` |
| Float arithmetic, both widths | `+`, `-`, `*`, `/`, `sqrt`, `abs`, negation, `min`, `max`, literals |
| Binary32 rounding | `LeanExe.Float32.nearest` |
| Float comparisons | `==`, `!=`, `<`, `≤`, `>`, `≥` |
| Conversions | `UInt64.toFloat`, `Float.toUInt64`, `Float.toBits`, `Float.ofBits` |
| Binary32 conversions | `w.toFloat32`, `Float32.ofBits w.toUInt32`, `x.toUInt64`, `x.toBits.toUInt64`, `(Int32.ofUInt32 w.toUInt32).toFloat32`, `x.toInt32.toUInt32.toUInt64`, with `w : UInt64` and `x : Float32` |
| `Bool` operations | `!`, `&&`, `\|\|`, `==`, `!=`, `decide` of a comparison, an equation, a conjunction, or a disjunction |
| Bindings | `let`, and `match` on a pair, a tuple, or a structure |
| Conditionals | `if` on a `Bool`, a comparison, or a conjunction or disjunction of these, `if h : c` whose branches do not use `h`, `match` on an enumeration or sum, and `match` on a structure whose patterns fix fields to enumeration constructors |
| Calls | Listed definition applied to all its arguments, or unfolded `@[inline]` helper |
| Combinators | `LeanExe.loop`, `LeanExe.repeatWhile`, `LeanExe.build` |
| Array folds | `xs.foldl step init`, with the default bounds `start = 0` and `stop = xs.size` |
| List folds | `xs.foldl step init` over `List UInt64`, with scalar state |
| Arrays | `#[]`, literals `#[a, b, …]`, `xs.size.toUInt64`, `xs[i.toNat]!`, `xs.set! i.toNat v`, `xs.setIfInBounds i.toNat v`, `xs.push v`, `xs ++ ys`, `xs.insertIdx! i.toNat v`, `xs.insertIdxIfInBounds i.toNat v`, `xs.eraseIdxIfInBounds i.toNat`, `LeanExe.insertAt xs i v`, `LeanExe.eraseAt xs i` |
| Packed bytes | `bytes![0, 255]`, `LeanExe.Bytes.empty`, `bytes.size`, `bytes.get index`, `bytes.set index byte`, `LeanExe.Bytes.build count f`, with UInt64 counts, indices, bytes, and callback results |
| Tuples and structures | `(a, b)`, `.1`, `.2`, constructors, `{ s with … }`, field reads |
| Lists of words | `[]`, `x :: xs`, and `match xs with \| [] => empty \| x :: ys => node` |

Every construct has Lean's meaning.  Word division by zero gives 0, the remainder by zero is the dividend, and a shift uses its amount modulo 64.  Each insertion accepts indices from 0 through the array's length.  Beyond the length, `insertIdx!` returns `#[]`, and `insertIdxIfInBounds` and `LeanExe.insertAt` return the input array.  Updates and removals leave the array unchanged at indices greater than or equal to its length.  Boolean equality supports `==`, `!=`, decisions of `=` and `≠`, and `if` on either proposition.  `==` and `!=` on `Bool` require `LawfulBEq Bool`.

An `Int64` is its word, and the reflector writes each `Int64` operation as an operation on words.  `+`, `-`, `*`, `&&&`, `|||`, `^^^`, `<<<`, and `==` are the word operations, and negation is `0 - x`.  The order comparisons are the source language's signed comparisons `slt` and `sle`, which compile to `i64.lt_s` and `i64.le_s`, and `>>>` is its arithmetic shift `sar`, which compiles to `i64.shr_s`.  Both shifts take the amount's low 6 bits, so `x >>> 65` is `x >>> 1` and `x >>> (-1)` is `x >>> 63`.  `min` and `max` are `if a ≤ b` on the signed comparison, with `Int64` branches.  `/` and `%` divide the magnitudes with the unsigned division and fix the sign afterwards, by the equations of [the word forms](../LeanExe/ProofKit/Signed64.lean), as `BitVec.sdiv_eq` and `BitVec.srem_eq` state Lean's definitions: `x / 0` is 0, `x % 0` is `x`, `minValue / -1` is `minValue`, and `minValue % -1` is 0, and the module executes no `i64.div_s` or `i64.rem_s`, so neither instruction's trap arises.  The C translator, the AArch64 back end, and the Cortex-M7 back end compile the signed comparisons and the shift.  A narrower signed value is sign-extended with two shifts, `((w <<< 56).toInt64) >>> 56` for a byte.  A table of a wrapper stays an `Array UInt64`, whose reads a program converts with `.toInt64`, and a recursive type has no array field of `Int64`.  A C caller that converts a returned `unsigned long long` to `long long` relies on a conversion that C11 6.3.1.3 leaves to the implementation, outside the theorem.  [The `Int64` fixture](../Verified/Examples/Signed.lean) and [the floor example](../Examples/Floor/README.md) compile these forms.

The conversions between `Int64` and the floats are word forms over the unsigned conversions, with equations in [the conversion forms](../LeanExe/ProofKit/Signed64Float.lean) that the kernel checks against Lean's model of each conversion.  `a.toFloat` and `a.toFloat32` convert the word `w` of `a` with `UInt64.toFloat` or `UInt64.toFloat32` when its sign bit is clear, and otherwise convert the magnitude `0 - w` and negate the result.  Lean's model rounds the magnitude to nearest with ties to even and attaches the sign afterwards, and `fromInt_neg` proves from Talos's rounding that the rounding of `-n` is the negation of the rounding of `n`, so the form rounds every input as Lean does.  The magnitude of `minValue` is `2^63`, which the unsigned conversion reads exactly.  At binary32 the 64-bit magnitude rounds once, so `2^62 + 2^38 + 1` gives `2^62 + 2^39`, where a conversion through binary64 would give `2^62`.  `x.toInt64` and `y.toInt64` truncate toward zero and saturate: for a negative operand the form negates `(-x).toUInt64` capped at `2^63`, and otherwise it caps `x.toUInt64` at `2^63 - 1`.  NaN and both zeros therefore give 0, negative infinity and every value at or below `-2^63` give `minValue`, and positive infinity and every value at or above `2^63` give `maxValue`.  The forms read their operand more than once, so the reflector binds an operand that is a compound expression first, while `k.toFloat` of an `Int64` variable `k`, and `w.toInt64.toFloat` of a word variable `w`, convert the variable directly, as `Library.Numerics.Float64.Log` converts its exponent `k`.  [The `Int64` values](../LeanExe/ProofKit/Signed64Value.lean) state the integer of a word read as `Int64` and of an arithmetic shift, and the exact conversion of an integer of magnitude at most `2^53`, for proofs about such programs.  The module executes none of `f64.convert_i64_s`, `f32.convert_i64_s`, `i64.trunc_sat_f64_s`, and `i64.trunc_sat_f32_s`, and [the conversion example](../Examples/Convert/README.md) proves that each of its exports returns what the corresponding instruction returns.

`min` and `max` at both float widths are IEEE 754-2019's `minimum` and `maximum`, which the reflector writes, by the theorems of [`FloatMinMax`](../LeanExe/ProofKit/FloatMinMax.lean), as comparisons, `==`, and, for two equal operands, the unsigned order of their bit patterns, which puts `-0` above `+0`, with the canonical NaN for a NaN operand.  Every back end, the WGSL and PTX kernels included, compiles these operations.  Float comparisons `==` and `!=` use IEEE value equality.  The reflector rejects the bit-pattern propositions `=` and `≠` on floats.  Both `Float.ofBits` and `Float32.ofBits` canonicalize NaNs as Lean does.  Binary32 signed conversion interprets the low 32 bits of a `UInt64` as an `Int32`, and signed truncation returns the resulting `Int32` bit pattern zero-extended to `UInt64`.  Only the listed conversion forms accept the intermediate `UInt32` and `Int32` terms.  Conversions between `Float` and `Float32` remain outside the dialect.  Lean's opaque float functions, such as `Float.exp` and `Float.sin`, require definitions of their own, as the numerical examples provide.

### Array literals and conditions on propositions

The reflector reads an array literal with elements, `#[a₁, …, aₙ]`, as `((#[].push a₁).push …).push aₙ`, and the kernel checks the reading by unfolding `Array.push`.  The literal therefore allocates as those pushes do: an empty block, then the growth of an owned array at each push.  The allocation bound charges the first push with `growCost` and each later push with `paidGrowCost`, so a literal of two words costs 232 bytes.  The elements may be any expressions of the dialect, of any element type that an array holds, and a literal may occur wherever an array may, such as a loop's state or a result.

`if p ∧ q` and `if p ∨ q` on propositions test the decision of the proposition, by `ite_decide_eq`, and the reflector reads `decide (p ∧ q)` and `decide (p ∨ q)` as `decide p && decide q` and `decide p || decide q`, by `decide_and_eq` and `decide_or_eq` at the instance of the term.  Each part is a comparison, an equation of `Bool`s or enumerations, or another conjunction or disjunction, as in `(a < b ∧ b < c) ∨ (c < b ∧ b < a)`.  The code evaluates both parts of each connective, as it does for `&&` and `||`, so a part that calls a function or reads an array runs even when the other part decides the result, and a nested `if` keeps the second test lazy.  The rule holds in ordinary code, in the elements of builds, in loops, and in the conditions of tail loops, and the WGSL translation lowers the Boolean connectives.  [The forms example](../Verified/Examples/Forms.lean) compiles literals and both connectives in each of these places, among them two tail recursions on a conjunction and a disjunction.

The termination proof of a tail loop applies Lean's functional induction to the definition, whose cases state the conditions in Lean's simplified form, such as `¬(r ≤ 1 ∨ d ≤ 1)` as `1 < r ∧ 1 < d`.  The step equation keeps the source form, so the proof splits each remaining case on the step's conditions and closes the branches that contradict the case with `omega` on the words' natural numbers and the integers of `Int64` values.  Negation `¬ p`, implication, and equivalence of propositions remain outside the dialect, as the restrictions table states.

### Loops and builds

`LeanExe.loop n init f` applies `f` to the indices `0` to `n - 1` in order, starting from the state `init`.  `LeanExe.repeatWhile fuel init cond step` applies `step` while `cond` holds, at most `fuel` times, and `LeanExe.build n f` is the array of `n` elements whose element `i` is `f i`.  The modules of [`LeanExe/Dialect/`](../LeanExe/Dialect) define the three, and [`Lemmas.lean`](../LeanExe/Dialect/Lemmas.lean) proves `loop_induction`, `loop_congr`, `loop_and_iff`, `build_size`, and `build_get` about them.  [`ArrayLemmas.lean`](../LeanExe/Dialect/ArrayLemmas.lean) proves `get_set`, `push_get_lt`, `push_get_size`, `get_toList`, and `take_get_mem` about reads `xs[k]!` after `set!` and `push` and about prefixes `xs.toList.take n`.  A state may have any type of the dialect, records with array fields included, and each part of a loop or a build is an expression of the dialect, which may hold further loops, builds, and calls.  `for`, `while`, and `do` notation are outside the dialect.  Recognized tail recursion compiles as a loop.

`xs.foldl step init` accepts every array element type and any accumulator type of the dialect.  The step may contain loops, builds, calls, and further folds, and an array accumulator may grow in place under the ownership rules.  The reflector requires the full-array bounds, `start = 0` and `stop = xs.size`.  Its source operation has Lean's full fold meaning.  Compiled lengths and indices use `UInt64`, and the heap representation bounds the array size below `UInt64.size`, which the compiler proof uses to equate the word-counted loop with the fold.  Folding over a record needs no default value or `Inhabited` instance for that record.

`List.foldl` accepts `List UInt64` and a scalar accumulator: words, Booleans, floats of either width, and their tuples, flat structures, enumerations, or sums.  The loop follows each cell's tail pointer and ends at null.  The step may contain calls, allocation, nested folds, and reads from captured values.  Captures remain borrowed during the fold, and ownership releases a constructed list or an owned capture after its last use.  A structural traversal computes allocation bounds and frames conditions.  A fold that calls guarded code retains that code's depth limit.  [The list example](../Verified/Examples/Lists.lean) and its [execution cases](../Verified/Examples/ListsCases.lean) cover these forms.

### Ownership

A variable that holds an array, a buffer, or a tree is borrowed or owned.  The reflector chooses each parameter's mode with `Expr.paramChoice` in [`Verified/Reflect/Modes.lean`](../Verified/Reflect/Modes.lean), by the rule `Ty.paramMode t m = if t.scalar then .borrowed else m`: a parameter that holds an array, a buffer, or a tree, alone or in a tuple, a structure, or a sum, is owned when the body consumes it at its last use, as the array of an update, an extension, an insertion, or a removal, as an argument at an owned parameter, or as the result, and borrowed otherwise.  The reflector splits a tuple parameter at the function's entry, so the body consumes the tuple when it consumes one of its components that holds an array, a buffer, or a tree, and a body that reads only a word of the tuple leaves it borrowed.  The reflector does not split a sum with such components, and a sum parameter that a match alternative names stays borrowed, as [the sum section](#records-tuples-and-sums) states.  An owned parameter has type `Moved α` in the theorem, such as `Moved (Array α)` for an array and `Moved (α × β)` or `Moved S` for a tuple or a structure, and the caller moves the value to the call.  A tuple argument at an owned parameter that is not a variable is bound whole to a variable of the tuple's type before the call, which moves the variable.  The theorem holds for every choice of modes, so the choice affects only the code's cost.  When an update, an extension, an insertion, or a removal is the last use of an owned array, the code changes the array in its own block, and it copies any other array first.  An extension that exceeds the array's capacity moves the array to a block of at least twice its capacity, so the number of blocks that a loop of pushes allocates grows with the logarithm of its count.  The code releases each owned array after its last use, unless the array moves into the result or into an owned parameter.  A caller copies a borrowed value that it passes to an owned parameter.

A list parameter also has a borrowed or owned mode.  `Moved (List UInt64)` transfers every cell
to the call.  Matching an owned cell detaches its children and releases unused fields.  When
reconstruction consumes the cell at its last use, the code reuses its header.  Copying a list
allocates one record per cell.  A borrowed list retains its records.

The same ownership rules apply to accepted user-defined recursive types.  Such a type has no
parameters or indices, is neither mutual nor nested, and has fields of type `UInt64`, `Bool`,
`Float`, `Float32`, an array of one of these, or the type itself, or of a type with a `Flat`
instance whose flattening holds words, `Bool`s, and floats, such as a structure, an enumeration, or
a sum.  Its first constructor without fields is null, and each other constructor is a record
constructor.  A `Bool`, a float, or a word occupies one slot, a field with a `Flat` instance one
slot for each leaf of its flattening, nested structures included, an array one slot, which holds
the address of an array object, and a `LeanExe.Bytes` buffer two slots, its root and its length.  A
record holds its word and child slots in the order of the fields and then its array and buffer
slots in the order of the fields, so the `Encode` instance writes each array slot after the
record's word and child slots, as `Slot.array` of the array's words, and each buffer as
`Slot.bytes b` followed by `Slot.word (UInt64.ofNat b.data.size)`.  The `Encode`
instance writes a `Bool` as `cond b 1 0`, a `Float` as its bit pattern, a `Float32` as its bit
pattern in the low 32 bits, a flattened field as the words of its leaves, and an array of `Bool`s or
floats as the words of its elements.  A construction moves an owned array into its record and
copies a borrowed one.  A construction moves an owned buffer into its record and copies a borrowed
one, and an empty buffer whose root is nonzero has its object released and is stored with root 0,
as the trusted model requires of a record.  A match binds an array field as an array variable and a
buffer field as a buffer variable of two locals, owned in an owned match, which releases them when
the branch does not use them, and a copy of a tree copies the arrays and buffers of each record.  A match binds such a field as one variable, and the code holds each leaf in a local
of its type.  A type with several record constructors is tagged: slot 0 of each record holds its
constructor's index in declaration order, and a match tests the tag against the record constructors
in that order and runs the last one's branch without a test.  A pattern matches one constructor
level, and a wildcard alternative compiles once for each constructor it covers.  A variable that
names the matched value, as in `| s => f s`, compiles in each record constructor's copy as that
constructor applied to the fields, which reuses the matched header and makes the matched variable
owned.  A branch that names the matched variable itself, as in `| _ => f t`, reads it, and when that
variable is owned the match works on a copy.  Tail matching preserves ownership across return and
continue steps.

The command `verified_recursive_type T`, defined in `Verified.Reflect.RecursiveTypes`, which
`Verified.Reflect.Command` imports, derives the declarations through which `verified_compile` and
`verified_compile_wasi` compile programs over `T`.  It places them in the namespace `verifiedT`
within `T`'s enclosing namespace, such as `Library.Trees.WordTree.verifiedKeyTree`.  They are `toTree`, the conversion to
`Tree` of `T`'s shape, `encoding`, the agreement of `T`'s `Encode` instance with that tree's
records, `wellFormed`, the theorem that every record of an encoded value meets the conditions of
the representation on the value alone, with the `EncodeWellFormed` instance that it gives unless
`T` has one, and the lemmas of a match on `T`.  When every flattened field is a structure whose `Flat`
tuple holds each of its fields and whose leaves, through nested structures, are words, `Bool`s, and
floats, the command also derives the conversion `fromTree` and the inverse laws `from_to` and
`to_from`.  A word that encodes no constructor of an enumeration or a sum has no Lean value, so a
type with a field that holds an enumeration or a sum has no `fromTree` and cannot be a parameter of
a recursive or tail-recursive definition, and neither can a type with a structure field whose `Flat`
tuple leaves out one of the structure's fields.  The command first encodes each constructor with an
array or buffer field at variables for its fields, and an instance that writes an array or buffer
slot before a word or child slot, two such slots out of the order of their fields, or a buffer's
root without its length slot after it, fails with a message that names the field.  Any other
encoding that disagrees with the layout fails the proof of `encoding`.  The command runs once, after `T`'s `Encode` instance, and fails when `T`
already has the declarations.  A program over `T` fails to compile unless its own module or a module
that it imports runs the command, so the declarations exist in one module and any number of modules
that compile programs over `T` can be imported together.  [The derivation for the library's
`KeyTree`](../Library/Trees/WordTree/Reflected.lean) runs the command in a module of its own, so
that the type's encoding, which `Library.Native` also imports, does not import the verified
compiler.

### Records, tuples, and sums

The reflector reads a structure through its `Flat` instance ([`LeanExe/Pipeline/Implements.lean`](../LeanExe/Pipeline/Implements.lean)), which must map it to the tuple of its fields, each field once and in any order.  The reflector writes a constructor or `{ s with … }` as the tuple of the fields, a chain of field reads, `.1`, and `.2` as one projection, and a `match` on a structure with one alternative as bindings of its fields.  A structure whose fields hold arrays is represented as its tuple by the instance `instRepresentOfFlat` of [`FlatRecords.lean`](../LeanExe/Pipeline/FlatRecords.lean), and it may be a parameter, a result, a local value, or a loop state.  An enumeration's `Flat` instance maps each constructor to a distinct word, by `ctorIdx` or by a `match`, and a `match` on an enumeration compiles to a chain of tests on the word.  `==` on an enumeration needs `LawfulBEq`, which `deriving DecidableEq` gives.  A `match` must have one discriminant and no `h :`.  [`Fields.lean`](../Verified/Examples/Fields.lean) and [`Enums.lean`](../Verified/Examples/Enums.lean) declare a record with array fields and an enumeration in this way:

```lean
open LeanExe.Pipeline

structure Book where
  prices : Array UInt64
  sizes : Array UInt64
  fills : UInt64
  deriving Inhabited

instance : Flat Book (Array UInt64 × Array UInt64 × UInt64) :=
  ⟨fun b => (b.prices, b.sizes, b.fills)⟩

inductive Phase where
  | solid | liquid | gas
  deriving Inhabited, DecidableEq

instance : Flat Phase UInt64 := ⟨fun | .solid => 0 | .liquid => 1 | .gas => 2⟩
```

A sum's `Flat` instance maps it to a scalar tuple with a distinct constant word tag for each constructor and each constructor field in one position.  The standard layout places the tag first, then every constructor's fields, with zeros in inactive fields.  Fields may themselves be scalar tuples, structures, or enumerations.  An accepted sum has no type parameters or indices.  Matching uses the tag to choose an alternative and its field positions to supply the alternative's arguments.  The kernel checks the translation by constructor cases.  Wildcard alternatives may bind the original value, and an expression used as a discriminant is evaluated once.  [The sum example](../Verified/Examples/Sums.lean) compiles the `Shape` program of `Examples.Shape`, arrays of shapes, and a sum with Float32 and enumeration fields.

A sum's fields may also be `Bytes`, arrays, and recursive types, each one component of the tuple, as in [the heap sum example](../Verified/Examples/HeapSums.lean):

```lean
inductive Item where
  | text (body : LeanExe.Bytes)
  | words (xs : Array UInt64) (scale : UInt64)
  | keys (tree : KeyTree) (weight : Float)
  | none

instance : Flat Item (UInt64 × LeanExe.Bytes × Array UInt64 × UInt64 × KeyTree × Float) := ⟨fun
  | .text body => (0, body, #[], 0, .leaf, 0)
  | .words xs scale => (1, .empty, xs, scale, .leaf, 0)
  | .keys tree weight => (2, .empty, #[], 0, tree, weight)
  | .none => (3, .empty, #[], 0, .leaf, 0)⟩
```

Such a sum is represented as its tuple, as a record with array fields is, and the instance's values for inactive fields are part of that representation: a construction of `.text body` allocates the empty array of the instance, while `Bytes.empty` and a null tree allocate nothing.  A variable of the sum is not split into components, since no function rebuilds the sum from its tuple.  A match destructures the variable once and tests the tag, and each branch releases the owned components that it does not use.  An owned value whose alternative names the matched value, as in `| other => other`, is copied before the match destructures it, while an alternative that rebuilds its constructor, as in `| .text b => .text b`, moves the fields and allocates the constructor's empty arrays again.  A parameter of such a sum is owned when the function returns the sum or consumes one of its fields and no alternative names it, since a match copies an owned value that an alternative names, and borrowed otherwise.  The destructuring stores each nested pair of the tuple in fresh locals, the whole tuple first and then each remaining part, so a match on `Item`, whose tuple has seven words, takes 22 positions, and a function whose code takes the call depth may exceed its 32 positions.  A field may not itself be a record with arrays or a sum with heap fields, and arrays cannot hold such sums.

### Structure patterns

A `match` on a structure with a `Flat` instance may have several alternatives whose patterns fix fields to constructors of enumerations and bind the other fields, as `Calc.undo` of [the calculator example](../Examples/Calc/README.md) does with `| { value, steps, last := .add } => …`.  Each pattern binds the whole value, or applies the structure's constructor with each field a variable or a constructor of an enumeration that has a `Flat` instance to words, and the alternatives end with a wildcard or cover every combination of constructors.  The reflector reads the match as a chain of `if`s in the order of the alternatives.  Each test compares the words of the fields that one pattern fixes with `==` and combines them with `&&`, and the last alternative, or an alternative that fixes no field, takes no test and ends the chain.  A variable of a pattern becomes the projection of the matched value, and a pattern that binds the value receives the value.  A matched value that is neither a variable nor a structure built from variables is bound with `let` first, so the code evaluates it once.

The reflector proves that the chain equals the match by cases on the structure and on each fixed field, with variables for the value and for each alternative's body, and the kernel checks the proof by reducing both sides at each combination of the fixed fields' constructors.  The proof has one case for each combination, and the code reads each fixed field once for each test that names it.  [The pattern example](../Verified/Examples/Patterns.lean) compiles patterns that fix one field or two, fix different fields in different alternatives, fix every field, bind the value, or cover every constructor without a wildcard.  Its matches are on parameters, on a structure built in place, on a call, in a loop's body, and on a record that holds an array.  A pattern that fixes a field to a literal, a `Bool`, or a nested pattern makes the reflector fail, as the restrictions table states.  Lean's `UInt64` is a structure without a `Flat` instance, so the rule does not apply to a `match` on a `UInt64` with literal patterns, which fails with `unsupported term`, as the pattern example checks.  A `match` with one alternative binds the fields, as the section on records states.

### Calls and recursion

A call passes its arguments' words and receives its result's words, a pair or a record as several WebAssembly results.  The command compiles recognized tail recursion as a Wasm loop: a step returns a result or continues with new parameter values.  It recognizes self-calls in tail position under bindings, conditionals, list matches, and single-alternative destructuring matches.  Continuation arguments cannot contain a self-call.  Parameter modes stay fixed across iterations, and mode inference propagates ownership from continuation arguments.  The reflector derives a decreasing rank from Lean's generated induction theorem.  The rank occurs in proofs and bound calculations.  Executable parameters and indices retain their dialect types.

Other recursion uses a call-depth parameter, and `set_option verified.tailLoops false` selects that path for every recursive definition in the command.  Guarded functions and their callers trap at `unreachable` when the depth reaches 1,000 and pass depth plus one to each depth-taking callee.  A tail loop takes the depth only when its body calls guarded code, and continuing iterations preserve it.  An exported entry starts a depth-taking function at depth 0.  Such a function may use at most 32 positions, including its depth, parameters, and locals.  Wasmtime keeps 8 bytes per value live across a call and 16 bytes per frame, so 1,000 frames of 32 positions take at most 272,000 bytes of its 512 KiB default stack.  The reflector gives each recursive definition as its source meaning, with a fixed-point proof and, for a tail loop, a termination proof.  Recursive parameter types require an inverse of their flattening on every source value.  Enumerations, sums, and recursive types with a field that holds an enumeration or a sum are excluded from recursive parameter types, because invalid tags and inactive field values prevent that inverse.

### Tables and wrappers

A table is a Lean constant of type `Array UInt64`, which the module writes in a data segment.  A function reads a table as a borrowed array parameter, and a wrapper is a listed definition of the form `f x := g T₁ … Tₖ x` that applies a listed function `g` to tables before its own parameters.  The module exports the wrapper as an entry that pushes the tables' addresses and calls `g`.  The wrapper's theorem, `ImplementsTables`, requires a store that holds each table at its address, disjoint from the blocks that the arguments move, and `p.initial` proves that the store in which the module starts holds them.  The host calls wrappers, while internal definitions pass tables as parameters.  In [the Fourier implementation](../Library/Numerics/Fourier/Program.lean), `transformWith` passes Trig's tables to `twiddleWith`, which passes them to `Trig.cosWith` and `Trig.sinWith`.

### Restrictions

| Message | Cause | Rewrite |
|---|---|---|
| `unsupported term …` | Term that no rule covers: an unlisted helper without `@[inline]`, `for`, or an opaque float function | List the callee before its callers, mark a helper `@[inline]`, use the combinators, or define the float function. |
| ``a pattern fixes the field … to …, which is not a constructor of an enumeration with a `Flat` instance to words`` | Structure pattern that fixes a field to a literal, a `Bool`, or a nested pattern, such as `{ flag := true, value }`.  Patterns that fix fields to enumeration constructors compile, as [structure patterns](#structure-patterns) describes. | Test the field with `if`, or match the nested structure in a nested `match`. |
| `unsupported term match w with …` | `match` with several alternatives on a `UInt64`, such as `match w with \| 0 => … \| _ => …`.  Lean's `UInt64` is a structure without a `Flat` instance, so the rule of [structure patterns](#structure-patterns) does not apply. | Test the word with `if`. |
| `unsupported condition …`, `unsupported decision …` | `if` or `decide` on a proposition other than a comparison, an equation, and conjunctions and disjunctions of these, such as `¬ p` or `p → q` | Test `!decide p`, or state the comparison that `¬ p` negates. |
| `Array.foldl requires start = 0`, `Array.foldl requires stop = xs.size` | Fold over part of an array | Use a word-counted `LeanExe.loop` for that range. |
| ``the type … is not UInt64, Bool, Float, Float32, Bytes, a structure with a `Flat` instance, an array, or a pair`` | Parameter, result, or binding of a type outside the dialect, such as `Nat` | Use the dialect's types, and give a structure or an enumeration a `Flat` instance. |
| `verified_compile: … is not among the listed definitions` | The option `(exports := [...])` names a definition that the list does not hold | List the definition, or remove it from the option. |
| `= and ≠ on … compare bit patterns; use == and !=` | `=` or `≠` on `Float` or `Float32` | Use `==` or `!=`. |
| ``an index must be `i.toNat` for a word `i` ``, ``a position must be `i.toNat` for a word `i` `` | Read or update at a position that is not a word's `toNat` | Index with `i.toNat` for `i : UInt64`. |
| `Lean has no Represent instance for …, so no theorem can be stated for it` | Parameter or result whose type has no instance, such as an array of tuples | Keep such an array local, or use an array of structures with a `Flat` instance. |
| `an array holds elements, not …` | Array of arrays, or of records with array fields | Store the inner arrays in one array at computed positions. |
| ``the `Flat` instance of … is not a tuple of its fields``, ``… repeats a field``, ``… does not hold all its fields`` | `Flat` instance other than the tuple of the structure's fields | Map the structure to the tuple of its fields, each once. |
| `unsupported comparison on …` | Comparison outside the supported word, float, enumeration, and Boolean equality forms | Compare supported scalar components. |
| `unsupported negation …` | `-x` on words | Write `0 - x`, or compute with `Int64`. |
| `unsupported operation … on …` | `+`, `/`, or another arithmetic operation on a type other than `UInt64`, `Int64`, and the floats | Convert the operands to words or to `Int64`. |
| `… has universe parameters` | Universe-polymorphic definition | Define the function at one universe. |
| `a match on several values is not supported`, `` `match h : …` is not supported `` | `match` with several discriminants or a named hypothesis | Nest the matches, and use `if` for tests. |
| `cannot reduce the recursive match at …` | Pattern below the first constructor level of a recursive type, such as `.a (.a _)` | Match the child in a nested `match`. |
| `the branches of … use the hypothesis of the if` | `if h : c` with a branch that uses `h` | Read with `xs[i.toNat]!`, which needs no proof of the bound. |
| `… must be applied to all n arguments` | Partial application of a listed definition | Apply the definition to all its arguments. |
| `the code of … takes the call depth and needs k positions, more than the 32 …` | Recursive function, or caller of one, with many live values | Move work into a function that calls no recursive function, or bind fewer values. |
| `the parameter type … of a recursive definition holds an enumeration or a sum …` | Parameter of a recursive or tail-recursive definition whose type holds an enumeration or a sum, directly or in a field of a recursive type | Pass the enumeration's word or the fields of the sum's constructor, and give a recursive type a `UInt64` field for an enumeration's word. |
| ``the parameter type … of a recursive definition has a field that holds the structure …, whose `Flat` tuple leaves out its field …`` | Parameter of a recursive or tail-recursive definition whose recursive type has a structure field, directly or in a nested structure, whose `Flat` tuple omits one of the structure's fields | Map the structure to the tuple of all its fields. |
| ``… needs `verified_recursive_type …` after its `Encode` instance, in the program's module or a module that it imports`` | Program over a recursive type `T` for which neither the program's module nor a module that it imports runs `verified_recursive_type T` | Run `verified_recursive_type T` once, after `T`'s `Encode` instance, in the program's module or in a module that it imports. |
| `verified_recursive_type: … is not a recursive type that the compiler supports` | Type with parameters or indices, mutual or nested type, field of a type outside the listed kinds, or shape outside the layout rules of the types table | Give the type the fields and constructors that the types table lists. |
| `verified_recursive_type: … already has its declarations` | Second run of the command for one type | Keep one run and import its module. |
| ``verified_recursive_type: the `Encode` instance of … places the array field … before a word or child slot``, ``… after a later array or buffer field``, or ``… places the buffer field … without its length slot after it`` | `Encode` instance that writes an array or buffer slot of a record before a word or child slot, two such slots out of the order of their fields, or a buffer's root without its length slot after it | Write each record's word and child slots first and its array and buffer slots after them, each group in the order of the fields, and each buffer's length slot after its root. |
| `a sum field must be a scalar, Bytes, an array, or a recursive type: …` | Sum field that is a record with arrays or a sum with heap fields | Give the constructor the record's fields as its own fields. |
| `the flattening of the default … is not the default element …` | Structure whose default does not take each field's default | Use `deriving Inhabited`. |
| `` `==` on … needs `LawfulBEq` `` | `==` on an enumeration without `LawfulBEq` | Use `deriving DecidableEq`. |
| `… must take the tables of … as borrowed arrays of words before its other parameters` | Wrapper whose callee takes the tables elsewhere | Put the table parameters first. |

## Compiling and running

### `verified_compile`

A program's file imports `Verified.Reflect.Command` and the definitions, and runs one command.  Native definitions are in separate `Program` modules, so that native Lean and the compiled module run the same functions, as [`Library/Random/Lcg/Verified.lean`](../Library/Random/Lcg/Verified.lean) shows for the [LCG generator](../Library/Random/Lcg/README.md).  The command lists the definitions in calling order, a callee before its callers.  A program over a user-defined recursive type also imports the module that runs `verified_recursive_type` for the type, as [Ownership](#ownership) describes.

```lean
import Verified.Reflect.Command
import Library.Random.Lcg.Jump

namespace Library.Random.Lcg

open _root_.Library.Random.Lcg

verified_compile compiled := [affine, step, advance, jumpPass, jump]
```

Two options size the memory.  `verified_compile (pages := N) p := [...]` starts the module's memory with `N` pages, 16 by default, or with more when the module's tables and literals need them, and the allocator grows the memory on demand.  `(cap := C)` gives the translation to C an `lx_mem` of `C` pages in place of `nativeCap`, 4,096, and states `p.translation` and every `p.f.native` for that cap, which must be at least the module's pages.  Either option may appear alone, and `(pages := N)` precedes `(cap := C)` when both appear.  The filter of the controller test, [`tests/TestSupport/Bare/Ctl.lean`](../tests/TestSupport/Bare/Ctl.lean), uses `(pages := 1) (cap := 1)`, so that its program fits a microcontroller's RAM.

A third option chooses the exports.  `verified_compile (exports := [f, g]) p := [...]` makes `p.module` export `alloc`, `release`, and the chosen definitions, each of which the list must hold, and no other function, so that a host sees the module's interface and not the helpers that the interface calls.  The module's functions, entries, and indices are those without the option.  The command states every theorem of a definition, exported or not, about the module of `compileWith`, as without the option, and carries it to `p.module`, `Verified.selectExports` of that module, with `LeanExe.Pipeline.ImplementsA.selectExports` and its counterparts of [the exports module](../Verified/Exports.lean).  These rest on `Wasm.run_exports` and `LeanExe.ProofKit.alignedRun_exports`, which state that a run of a module does not read its exports.  [The exports example](../Verified/Examples/Exports.lean) exports a division with a status and a wrapper and keeps a helper with Lean's convention at a zero divisor internal.  Each option may appear alone, and the options appear in the order `(pages := N)`, `(cap := C)`, `(exports := [...])`.

The command adds the program, the module, and every theorem in one step, and the kernel checks each.  The theorems use only the axioms `propext`, `Classical.choice`, and `Quot.sound`, as `#print axioms` shows for `Prog.correct`, `Prog.correctWith`, and each example's `compiled.bytes` and named theorems.  The declarations and the exports take the last component of a definition's name, so two listed definitions whose names end in the same component collide.  `set_option trace.Verified.reflect true` reports the reflection and proof-generation stages for each function and the encoding check for each function index.  Reflection entries include the remaining heartbeat budget in the units of `maxHeartbeats`.

### `verified_compile_wasi`

`import Verified.Wasi` provides a separate frontend for `LeanExe.Wasi.Action` definitions.  Its callable form, `verified_compile_wasi p := [pureHelper, actionHelper, action]`, exports each listed action.  Adding `(main := main)` selects a closed `Action UInt64`, exports `_start`, and passes main's returned status to `proc_exit`.  An action uses ordinary `do` notation, UInt64 lengths and counts, packed bytes, bounded loops, and acyclic effectful helpers, and its pure helpers use this manual's dialect and recursion rules.  A process without an iteration bound is a begin function and a step function of a callable program, which [the typed process entry](../Verified/Wasi/ProcessCode.lean) composes into a `_start` loop.  The step takes the state by move, and the loop compacts the state after begin and after each step that leaves the heap above its base larger than four times the state's copy cost, so the process theorems require free memory for a step's charge with four copies of the state before the step and one of the state after it, as [the WASI manual's section on processes](wasi.md#processes-without-an-iteration-bound) describes.

Every module imports the stream functions, `fd_read` of descriptor 0, `fd_write` of descriptors 1 and 2, and `proc_exit`, through which `readStdin`, `readAll`, `writeStdout`, `writeStderr`, and `exit` use the standard streams and end the process.  [The call table](../LeanExe/Wasi/CallTable.lean), which `tools/wasi-calls.py` generates from the pinned witx, describes every function of `wasi_snapshot_preview1` but `proc_exit`, `sock_recv`, and `sock_send` by its import name, the core form of each parameter, and the call that reports the sizes of its regions.  A call of such a description is a flat call, among them `fd_read` and `fd_write` on a handle and the other calls that pass arrays of records, which [the WASI manual](wasi.md#nested-calls) calls nested.  `LeanExe.Wasi` gives each flat call a typed function, such as `clockTimeGet`, `randomGet`, `fdPrestatGet`, `fdRead`, `fdWrite`, and `pathUnlinkFile`, except `args_get` and `environ_get`, which `args` and `environ` make after their reporters, `path_open` and `fd_close`, which only `withOpen` makes, and `fd_renumber`, which no program makes.  A typed function takes words, byte strings, and handles, returns the errno with the call's results, and makes its call through `Action.sys`.  `verified_compile_wasi` compiles each such call to one `Command.sys`, and the module imports, after the stream functions, the flat calls that the program makes, `p.sysCalls`, in the order of their first use.  [The WASI manual's section on flat calls](wasi.md#flat-preview-1-calls) describes the typed functions, their results, and the arguments that they reject before a call.

Apart from the standard streams, which the stream functions use, a program reaches a descriptor only through a `Handle`: `Handle.preopened`, descriptor 3, the directory that the host preopens, or the handle that `withOpen dir dirflags path oflags rightsBase rightsInheriting fdflags onError body` binds.  `withOpen` calls `path_open` for `path` under `dir`, runs `body` on the new handle, and closes it with `fd_close` when the body returns, and its result pairs the body's result with the close's errno, or the result of `onError` with 0 when the open fails.  The handle check `Command.HandleCheck` refuses a call that is not a description of `Call.table`, a `path_open`, `fd_close`, or `fd_renumber` outside the shape that `withOpen` reflects to, and a handle argument other than a bracket's handle, a variable that a `ret` of the literal 3 binds, alone or under `letPair` bindings (`Command.preopened` and `Expr.isPreopened`), or a `Handle` parameter of the helper being checked.  `verified_compile_wasi` decides the check in the kernel for each program as `p.handlesChecked` and proves from it `p.handles`, or `p.f.handles` for each export of a callable program, which states that every run keeps each use of a handle between its open and its close, as [the WASI manual's section on handles](wasi.md#handles) describes.

`main` of [the files command](../Verified/Examples/WasiFiles.lean) writes the file `f` under the preopened directory in one bracket, reads it back in another, and writes the bytes that it read and the directory's name to the standard output.  The first bracket opens `f`, whose name is the byte 102, with the open flags `creat` and `trunc`, 9, and the right `fd_write`, 64, and the second opens it with the right `fd_read`, 2.  The read fills a buffer of 16 bytes that `main` builds, and the write of stdout takes the window of the bytes that the read placed, from position 0 for the read's count.  The first component of each bracket's result is the errno of its body or of `onError`, and the second is the errno of its close:

```lean
import Verified.Wasi

namespace Verified.Examples.WasiFiles

open LeanExe LeanExe.Wasi

def main : Action UInt64 := do
  let written ← withOpen .preopened 0 bytes![102] 9 64 0 0
    (fun errno => pure errno) fun file => do
      let sent ← fdWrite file bytes![104, 105] 0 2
      pure sent.errno
  if written.1 != 0 then
    pure written.1
  else if written.2 != 0 then
    pure written.2
  else
    let read ← withOpen .preopened 0 bytes![102] 0 2 0 0
      (fun errno => pure errno) fun file => do
        let got ← fdRead file (Bytes.build 16 fun _ => 0) 0 16
        if got.errno != 0 then
          pure got.errno
        else
          let _ ← writeStdout got.buffer 0 got.count
          pure 0
    if read.1 != 0 then
      pure read.1
    else if read.2 != 0 then
      pure read.2
    else
      let prestat ← fdPrestatGet .preopened
      if prestat.errno != 0 then
        pure prestat.errno
      else
        let name ← fdPrestatDirName .preopened (Bytes.build prestat.prNameLen fun _ => 0) 0
          prestat.prNameLen
        if name.errno != 0 then
          pure name.errno
        else
          let _ ← writeStdout name.buffer 0 name.buffer.size
          pure 0

verified_compile_wasi command (main := main) := [main]

end Verified.Examples.WasiFiles
```

These shell commands build the files command, write its module, and run it in [the Wasmtime host](#the-wasmtime-host) with an empty directory preopened.  The build passes `--memory-high 8G`, as the test scripts do.  The run writes `hi.`, the file's two bytes followed by the preopened directory's name, and exits with status 0:

```sh
tools/leanrun --timeout 30m --memory-high 8G lake build Verified.Examples.WasiFiles
mkdir -p build/wasi/dir
tools/leanrun --timeout 5m lake env lean --run tools/Emit.lean \
  Verified.Examples.WasiFiles Verified.Examples.WasiFiles.command.module build/wasi/files.wasm
wasm-tools validate build/wasi/files.wasm
build/tools/leanexe-wasmtime-host --dir build/wasi/dir run build/wasi/files.wasm
```

The generated callable `.implements` and command `.start` theorems concern the exported wrappers with their hidden depth and table arguments.  For every host environment that satisfies `hostSpec host`, or `hostSpecWith host p.sysCalls` for a program with flat calls, they relate each sufficiently fueled target execution to a native source execution with the same ordered effects, world, and result, or to a source prefix on a permitted guest resource trap.  `hostSpecWith host calls` adds to `hostSpec host` the host's specification of each flat call, `sysContract host call`: for a request that `SysRequest` admits, which fits the call's parameters, which `Call.reject` accepts, whose inputs lie in memory, and whose aligned output regions lie in memory below `2^32`, apart from one another and from the inputs, the host changes memory only in the output regions and on errno 0 leaves each output in its region.  Host traps and rejected exits remain terminal outcomes of these theorems.  The conditional `.total` theorems require free memory for allocation, `Resource.CallPrefixBound` for the typed program, and `host.NoTrapsAlong` the native action.  [The WASI manual](wasi.md) defines the generated declarations, the premises on ownership and on the low memory, the modeled initial store, and the host policies, and [WASI programs and their executables](#wasi-programs-and-their-executables) lists the theorems with their premises.

### Buffers and windows of WASI programs

The reads, the writes, and the flat calls with an output buffer take a buffer that the program passes and a window of it, a start and a count, and none of them allocates.  `LeanExe.Bytes.window buffer start count` of [the window definitions](../LeanExe/Wasi/Window.lean) gives the window's first position, `start` or the buffer's size when that is smaller, and its length, `count` or the bytes from that position on when they are fewer, so a window never leaves its buffer, and `Bytes.range` gives the window's bytes.  The compiled code computes the same positions in words and passes the window's address in the buffer's block and its length to the import, so the host reads or writes the program's buffer in place.  A window of `2^32` bytes or more gives errno 61 without a host request, through `Call.reject` for a flat call and `Exec.read_reject` for a read of stdin, and a represented buffer holds fewer than `2^32` bytes, so a compiled program never reaches that case.  A flat call whose result is a record, such as `fdFilestatGet`, and a poll place their regions in the call area `[16, 176)` of the low memory, where `callFits` requires them to fit, so they take no buffer and allocate nothing, as [the WASI manual](wasi.md#callable-and-command-modules) states.  `args` and `environ` allocate a block of the size that `args_sizes_get` or `environ_sizes_get` reports.

| Operation | Type | Call | Result |
|---|---|---|---|
| `readStdin buffer start count` | `Bytes → UInt64 → UInt64 → Action FillResult` | One `fd_read` of descriptor 0 into the window | The count of bytes read and the buffer |
| `randomGet buffer start count` | `Bytes → UInt64 → UInt64 → Action FillResult` | One `random_get` into the window | The window's length and the buffer |
| `fdRead h buffer start count` | `Handle → Bytes → UInt64 → UInt64 → Action FillResult` | One `fd_read` of the handle into the window | The call's count, at most the window's length, and the buffer |
| `writeStdout buffer start count`, `writeStderr buffer start count` | `Bytes → UInt64 → UInt64 → Action WriteResult` | One `fd_write` of descriptor 1 or 2 with the window's bytes | The count that the host took, which may be short |
| `fdWrite h bytes start count` | `Handle → Bytes → UInt64 → UInt64 → Action WordResult` | One `fd_write` of the handle with the window's bytes | The count written |
| `writeAll buffer start count` | `Bytes → UInt64 → UInt64 → Action UInt64` | `writeStdout` of the window's bytes that earlier writes did not take, at most the window's length plus one times | The number of bytes that the writes took, or the exit with the errno of a write that fails |

A fill returns `FillResult`, whose fields are the errno, the count, and the buffer, as `FillResult.of buffer start count errno used bytes` of [the actions](../LeanExe/Wasi/Action.lean) states.  On errno 0 the result's buffer holds in its window the bytes of the window after the call (`Bytes.splice`), and after an errno the count is 0 and the window's bytes are 0 (`Bytes.clear`), so the program keeps its buffer in both cases.  The reply of `random_get` or `fd_read` on a handle holds the whole window, which `sysContract` places there on errno 0.  `Exec.read_return` passes the continuation of a read of stdin a range, the bytes of the read's region after the call, which it requires to have the window's length and, on errno 0, to begin with the bytes read, and which it leaves otherwise free, since Preview 1 states neither which bytes of an iovec's region the host writes nor what the bytes after the count hold.  `readStdin_placed` of [the semantics](../LeanExe/Wasi/Semantics.lean) states that a read with errno 0 places the bytes read at the window's start, and `readStdin_returns` that the count is at most the buffer's size and that the buffer keeps its size.

A fill takes its buffer with the code of a `ret` of the buffer's variable, which moves an owned buffer whose variable dies at the call and copies the buffer otherwise, with the variables that `sysTakeLive` names as live after the take.  The host writes into the block that the code took, the code sets the window's bytes to 0 after an errno, and the result holds that block.  The resource model charges a fill `PureContext.sysTakeCost`, 0 when the variable dies at the call and the copy's block when it stays live or is borrowed.  A write borrows its buffer: the code pushes the buffer's root and size and the window's start and count and calls the write wrapper, which computes the window and passes it to `fd_write`, so a write neither copies nor allocates.  `wp_read_fill_with` of [the read command](../Verified/Wasi/ReadCommand.lean), `command_sys_spec_with` and `cost_command_sys_spec_with` of [the flat call commands](../Verified/Wasi/SysCommand.lean), and `wp_write_command_with` of [the write command](../Verified/Wasi/WriteCommand.lean) prove this code.

`writeAll` of [the write loop](../LeanExe/Wasi/WriteAll.lean) writes the window of a buffer to stdout and follows a short write with a write of the bytes that remain.  The compiler has no command for it, so a program lists it among its definitions, as the demos' `verified_compile_wasi` lists do.  Each pass that finds bytes left writes the window of the same buffer that starts `written` bytes past the window's first position and holds the bytes that remain, a write that returns an errno ends the run with the exit of that errno, and the loop returns the number of bytes taken, which falls short of the window's length only when its passes run out.  `writeAll_run` states that every run meets `WriteAllRun` over the window's bytes, `writeAll_run_whole` states the case of a whole buffer, and `WriteAllRun.taken` states that a run that returns `v` took the first `v` bytes in writes that returned errno 0, each of which offered the bytes that remained, with one write for each pass when `v` falls short.  `stdoutTaken` and `Offered` state the bytes that the writes of a trace took and offered, in the terms that a command's specification uses, `WroteSome` states that a write offered at least one byte, and `WriteAllRun.shape` states it of every write of a run that returns or exits, since a pass writes only while bytes remain.  A program tests the returned count against the window's length to tell a stall from success, and the demos give a stall a status above 76, the largest WASI errno.

### Streaming commands that allocate nothing in their passes

A command that processes a stream in a loop allocates nothing in a pass when it builds its buffers once, before the loop, keeps them in the loop's state, and gives each buffer to the call that fills it at the last use of the buffer's variable.  The reflector splits the loop's state into its components at the start of each pass, and the result of each action where `←` binds it, with `Command.letPair`, so the state's buffer is a variable of its own, which dies at the fill, and the fill moves it.  The fill returns the buffer in its result, and the pass puts that buffer into the next state.  Pure functions read the buffer through a borrowed parameter or update it through an owned parameter at its last use, and `writeAll` borrows it.  The resource model, which charges a copy of an owned value at each use after which the value stays live and credits no release, then charges the pass nothing, and `loop_bounded` of [the resource rules](../Verified/Wasi/ResourceRules.lean) with a pass charge of 0 bounds the loop by the charge of its test, whatever the number of passes.

| Demo | Buffers in the loop's state | Fill | Work on the buffer | Output |
|---|---|---|---|---|
| [Random-residue histogram](../Demos/RandomHistogram/README.md) | One of 4,096 bytes, with the counts, the words still to draw, and an errno | `randomGet state.2.1 0 (8 * count)`, the buffer's first `8 · count` bytes | `tally` counts the first `count` words of the borrowed buffer into the counts, which it updates in place | `writeAll output 0 output.size` after the loop |
| [Unbiased random choice](../Demos/RandomChoice/README.md) | A draw buffer of 4,096 bytes and an output buffer of 10,752 bytes, with the values still to choose and a status | `randomGet state.2.2.1 0 4096`, the whole draw buffer | `putPicks` reads the borrowed draw buffer and writes the lines of the picks with `Bytes.set` into the output buffer, which it takes as owned | `writeAll put.1 0 put.2.1`, the window that the lines fill, in each pass |
| [Manifest checker](../Demos/ManifestCheck/README.md) | One read buffer of 65,536 bytes, with the hash value and the counts of bytes held and read, moved into each `withOpen` bracket and out of it | `fdRead file s.2.1 s.2.2.1 (chunk - s.2.2.1)`, the window after the bytes held | `update` compresses the blocks of a full buffer, which it borrows, and `finish` pads and compresses the bytes after the last whole block | `writeAll line 0 line.size` for each line of the manifest |

The histogram's loop shows each step.  Its state holds the counts, the buffer, the words still to draw, and the errno of a failed call, and each pass draws at most 512 words into the buffer's first bytes.  The pass puts the buffer of the fill's result into its new state:

```lean
let drawn ← Wasi.loop (n / 512 + 1)
    (LeanExe.build 10 fun _ => (0 : UInt64), Bytes.build 4096 fun _ => 0, n, (0 : UInt64))
    (fun _ state => state.2.2.1 != 0) fun _ state => do
  let count := min state.2.2.1 512
  let random ← randomGet state.2.1 0 (8 * count)
  if random.errno != 0 then
    pure (state.1, random.buffer, (0 : UInt64), random.errno)
  else
    pure (tally state.1 random.buffer count, random.buffer, state.2.2.1 - count,
      (0 : UInt64))
```

The loop's test reads the state in a borrowed slot, and the split of `state` moves the counts, the buffer, and the words still to draw into variables of their own, since `state` dies there.  `randomGet` moves the buffer, whose variable dies at the call, and the split of `random` moves the result's buffer into its variable.  `tally` takes the counts as an owned parameter, updates them with `set!` in their block, and borrows the buffer, so its generated bound is 0 (`tally_charge` of [the histogram's budget](../Demos/RandomHistogram/Budget.lean)), and each branch's tuple moves variables that die there.  The proof of `body_bounded` applies `loop_bounded` with a pass charge of 0, and the tactics `rule_free`, `rule_ite`, and `rule_ret` of [the budget tactics](../Verified/Wasi/BudgetTactics.lean) and `letPair_free` of the resource rules apply the rules of each command of the pass.

A window lets one buffer receive the bytes of several reads in turn.  The manifest checker's `hashFile` reads into the window after the bytes that its buffer holds, and when a read fills the buffer it compresses the buffer's blocks and starts again at position 0, so no byte moves within the buffer, and `readBytes` reads the manifest into a buffer of its reported size in the same way.  The random choice writes only the window of its output buffer that the pass's lines fill, so one buffer of the largest pass's size serves every pass.  The proofs state a fill with `Bytes.splice`: `splice_take` of [the histogram's command proof](../Demos/RandomHistogram/CommandProof.lean) states that the first bytes of a buffer after a fill from position 0 are the reply's.

A pass allocates when it uses the buffer's variable after the fill, fills a borrowed buffer, or builds a buffer.  The first two copy the buffer at the call, and the third, such as `Bytes.build 4096 fun _ => 0` in a read step of the process demos, allocates and fills a block at each pass.  Any block that a pass allocates adds to the charge once for each pass, since the model credits no release: the manifest checker's pass over a line allocates the copy of the line's name, the output line, and the words that `finish` packs, and `loop_bounded_sum` bounds that loop by the sum of the passes' charges, which the size of the manifest bounds.  `body_bounded` bounds the whole body, and the charge of 0 for each pass appears in its proof and in no statement, so a program that built its buffers in its first pass would meet the same bound.

### Generated declarations

These declarations belong to the pure `verified_compile` command, and [the WASI declaration table](wasi.md#declarations) describes those of `verified_compile_wasi`.  A name `p.f.d` is the declaration `d` of the listed definition `f` in the namespace of the program `p`, such as `compiled.advance.implements` of the LCG program.  A name without `f`, such as `p.bytes`, concerns the program, its module, or a type that the program uses.

| Declaration | Content |
|---|---|
| `p.program`, `p.funs`, `p.meaning` | Source program, meanings of its functions, and proof of `Prog.Meaning p.program p.funs`. |
| `p.prefix_k` | The program of the first `k + 1` listed definitions that are not wrappers: `Prog.cons` or `Prog.consTail` of the `k`-th one's `p.f.func`, its flags, `p.f.sig_eq`, and `p.prefix_(k-1)`, or `Prog.consRec` of a recursive definition's `p.f.func` and `p.prefix_(k-1)`, typed by the literal list of their signatures.  `p.program` is the last prefix.  The bound definitions, the proof `p.meaning`, and the proofs over the bound tables refer to these constants, so the kernel checks the program's chain once, in the prefixes' definitions. |
| `p.f.sig_eq` | For a definition that is neither recursive nor a wrapper: `p.f.func.sig = p.f.func.sigWith aborts depth`, with the flags `aborts` and `depth` as literals.  `Prog.cons` and `Prog.consTail` take the flags and this equation and index the function by `sigWith aborts depth`, so a comparison of the program's signatures with the literal list compares the stated flags, and only the check of `p.f.sig_eq` evaluates the body's `aborts` and `depthCalls`. |
| `p.tables`, `p.wrappers`, `p.module` | Tables, wrappers, and module `compileWith p.program p.tables p.wrappers`, or, under the option `(exports := [...])`, `Verified.selectExports` of the chosen names and that module. |
| `p.literalPool` | Deduplicated nonempty byte literals, starting after the constant word-array tables.  The module uses this pool explicitly. |
| `p.initial` | Store in which the module starts meets the allocator invariant, caps the memory at 65,535 pages, and holds each table at its address.  A nonempty pool adds its static contents and heap region as a fourth conjunct.  An empty pool keeps the three-part result. |
| `p.bytes` | `∃ bytes, encode p.module = .ok bytes ∧ decode bytes = .ok p.module ∧` the conjunction of the theorems `p.f.implements`. |
| `p.sections`, `p.bodies`, `p.data`, `p.encoding` | Literal byte lists for the sections, function bodies, and data, and their assembly into the module's bytes. |
| `p.func_ok_k`, `p.rest_ok`, `p.data_ok`, `p.codes_ok`, `p.funcs_count`, `p.funcs_length` | Kernel-checked encoding claims for each function, the other sections, and the sizes. |
| `p.encoded` | `encode p.module = .ok ⟨p.encoding.toArray⟩`, with the bound on each function's locals that `decode_encode` requires. |
| `p.inSubset` | `LeanExe.Native.InSubset p.module`: the module is in the subset of WebAssembly that the translator to C accepts.  A module outside it gets a warning that names the first part outside, and no theorem. |
| `p.native_part_k`, `p.native_parts`, `p.translation_infos` | Checks from which `p.inSubset` and `p.translation_funcs` follow, one theorem for each function: function `k`'s `functionViolation` is `none`, and its `callInfo`, the functions that its C function calls, is entry `k` of the literal `p.translation_infos`. |
| `p.translation`, `p.translation_funcs`, `p.translation_eq` | For a module that translates with `nativeCap` pages, or with the `C` pages of the option `(cap := C)`: its translation to C, the list of the functions that the translation contains, and `translate nativeCap p.module = some p.translation`, or the same with `C`.  A module that does not translate gets a warning. |
| `p.f.native` | For a function that the translation contains: under every global environment that holds the translation's globals, memory, and functions, the C function computes `f` as `p.f.implements` states (`NativeImpl`, `NativeTablesImpl`, or `NativeStaticImpl`).  After a return, `p.f.native` concludes, as `p.f.implements` does, the postcondition, unchanged memory caps, and the region clause: every nonempty region of the heap disjoint from the moved blocks keeps its bytes, remains a region of the final heap, and is disjoint from the result.  With `set_option verified_compile.alignedNative true`, for a program without byte literals, the command also states the translation without the alignment test, `p.translationAligned`, its equation `p.translationAligned_eq`, and `p.f.nativeAligned`, which is `NativeAlignedImpl p.f.implements` or `NativeTablesAlignedImpl p.f.implements`: from an input that meets `AlignedInput`, the C function computes `f` as `p.f.native` states, with an aligned final heap and a result whose blocks meet `AlignedOutput`.  The SHA-256, SHA-3, CRC, and insertion-sort modules of the library and the verified Euler and binary32 GPT-2 modules set the option. |
| `p.f.aligned` | For each definition of a program without byte literals: from an input whose heap, consumed objects, and read regions are aligned, every run of the entry from some fuel on makes only aligned 64-bit accesses inside memory, and the final heap and the result's blocks are aligned.  `p.f.nativeAligned` follows from it and `p.f.implements`. |
| `p.f.func`, `p.f.denote_eq` | Source function and its body equation.  A tail body's equation describes its return-or-continue step.  A wrapper has no source function, and its equation relates it to its callee at the tables and parameters. |
| `p.f.implements` | With an empty literal pool, `ImplementsA aborts p.module k f` with Lean's instances, or `ImplementsTables` for a wrapper.  With a nonempty pool, `ImplementsStatic p.literalPool aborts p.module k f tables Pre Post`, including the static input premise. |
| `p.f.uniform`, `p.f.pure` | For eligible scalar functions in a program with an empty literal pool: raw execution is independent of the store, and `ImplementsPureA aborts` computes the Lean result while preserving the whole store. |
| `p.f.argsAgree`, `p.f.resultAgree` | Lean's instances represent the arguments and the result as the source's instances represent their flattenings. |
| `p.f.bound`, `p.f.bound_eq` | Allocation bound in bytes on the argument tuple, and its equation in the parameters.  For a function whose code takes the call depth, the bound takes the number of frames first. |
| `p.f.cost`, `p.f.cost_eq` | For a function with a paid parameter: the bound without the credits of the paid arguments, and its equation. |
| `p.f.trapFree` | With an empty literal pool, `ImplementsA false`, or `ImplementsTables false` for a wrapper whose callee takes no call depth.  It requires `Heap.Within` for the bound when `aborts` is true and the frames condition for guarded calls.  With a nonempty pool, `ImplementsStatic` with `aborts = false` adds static input, allocation, and guarded-call premises.  Such wrappers receive `trapFree` through `Wrapper.bound`, without a named wrapper `bound` declaration. |
| `p.f.fits`, `p.f.fits_eq` | For a function whose code takes the call depth: the frames condition, and its equation. |
| `p.f.meaning`, `p.f.meaning_eq`, `p.f.fixed` | For a recursive definition: its meaning on source environments, the equation of its self-call, and the fixed-point equation. |
| `p.f.body`, `p.f.step`, `p.f.step_eq`, `p.f.wellFounded`, `p.f.decreases` | For a tail loop: its typed body, native return-or-continue step, their agreement, the well-founded continuing relation, and the source rank's decrease. |
| `p.flat_injective.E` | For each enumeration that the program compares, with `E` its full name: its flattening is injective, which the comparisons of its words use. |
| `p.flat_eta.R`, `p.flat_field.R.f` | For each record with array fields that the reflector splits, with `R` its full name: the eta law of its flattening, and the equation of field `f` with its component of the flattening. |

Functions 0 and 1 of the module are the runtime's `alloc` and `release`, and function `2 + k` is the `k`-th listed definition that is not a wrapper, counted from 0.  In a program of `n` such definitions, the entry of the `j`-th definition whose code takes the call depth is function `2 + n + j`, and the wrappers follow the entries.  The module exports each definition under its name, at its entry when its code takes the call depth, or only the definitions that the option `(exports := [...])` chooses.

A call theorem for one export follows from `p.f.implements` or `p.f.trapFree`.  [The call module](../Verified/Call.lean) states the call as `Verified.Call p.module p.tables k f Pre Post`: from a store that `Verified.Ready p.module p.tables` states ready, with borrowed or scalar arguments and `Pre`, function `k` returns `f x` without a trap and leaves a ready store.  The call also keeps every borrowed array borrowed and every region of the heap unchanged, and it meets `Post`.  `Verified.CallSpec p.module p.tables k f B` is that statement with `top` at least `B x` bytes below the memory cap before the call and an increase of `top` by at most `B x`.  `Verified.ImplementsTables.call` proves `Call` from the entry's theorem, and `Verified.Call.spec` proves `CallSpec p.module p.tables k g p.f.bound` from `p.f.trapFree` for a specification `g` that equals `f` on represented arguments, for words, word arrays, and tuples of them, as `Examples.Increment.compute_callSpec` does.  [The congruence theorems](../Verified/Congr.lean) transfer a theorem to an equal function in two other forms: `Verified.implementsA_congr` transfers `ImplementsA`, which covers arguments that the caller moves to the call, and `Verified.call_on` transfers `Call` to a function that equals the first only on the arguments that meet a predicate, which the new precondition implies.  `Verified.Ready.initial rfl p.initial` proves that the store in which the module starts is ready.

### Module composition

The typed API combines separately reflected programs with `Prog.append`:

```lean
def program := source.program.append library.program
def funs := source.funs.append library.funs
theorem meaning : program.Meaning funs := source.meaning.append library.meaning
def module := Verified.compile program
```

`Prog.cons` and `Prog.consTail` take a function's flags `aborts` and `depth` with the equation
`f.sig = f.sigWith aborts depth`.  In a program written by hand, `Prog.consSig f rest` and
`Prog.consTailSig f rest` supply the flags that the signature computes, as
[the composition example](../Verified/Examples/Composition.lean) does.  The library's functions keep their indices.  The index of each source function and of each call between source
functions increases by the library's function count.  `FVar.appendLeft` refers to a relocated source
function, and `FVar.appendRight` refers to a retained library function.  A typed function of the combined program can
call both.  The generic append theorem keeps the meaning proofs of ordinary,
guarded-recursive, and tail-recursive functions.  The tail rank changes only in the proof.
Function export names must be unique.  Tables and wrappers remain arguments of `compileWith`.

`Prog.calls_append` reuses the library's execution, allocation, and frames theorems in the
combined module.  A shared pool must cover both programs and compile both function lists.
[Append coverage](../Verified/ProgramLiterals.lean), `Prog.covered_append`, gives the two coverage
premises.  `Prog.correctStatic` applies to the combined meaning proof.  With no nonempty
literals, `Prog.correct` gives the empty-pool specialization.  The scalar proof generator
also accepts a composed module with an empty pool.
[The relocation example](../Verified/Examples/Relocation.lean) gives native and whole-store
theorems for a retained function, a relocated tail loop, and a caller of both libraries.

### WGSL kernels

[`Verified.WGSL.compile`](../Verified/WGSL/Compile.lean) translates a reflected function's typed
body to a WGSL kernel.  The body must be an outer `LeanExe.build`, whose count is a word
parameter or an input array's length.  Parameters and array elements are words, Booleans, or
binary32 values.  The per-element subset includes borrowed reads, scalar bindings, conditional
branches, and counted loops with word, Boolean, or binary32 state.  Helpers marked `@[inline]`
can unfold into the element expression.  Source calls, heap operations inside an element,
binary64 values, and composite parameter or element types are outside this subset.

Word arithmetic includes addition, subtraction, multiplication, and division or remainder by a
constant power of two from 2 through 2³¹.  Binary32 operations include arithmetic, comparisons,
square root, absolute value, negation, nearest-even rounding, and conversion to or from bit
patterns.  The translation accepts finite float literals.  Parameters, input arrays, and runtime
bit conversions can supply infinities and NaNs.  The shared WGSL translation normalizes arithmetic
NaNs to `0x7fc00000`.

After `verified_compile compiled := [scale]`, the typed API constructs the kernel as follows:

```lean
import Verified.WGSL.Compile

def gpu := (Verified.WGSL.compile (e := .float32) compiled.scale.func.body).get (by decide +kernel)
def kernel : LeanExe.WGSL.Module := gpu.module
```

Compilation returns `none` when translation or the local-layout check fails.  Each successful
result includes their proofs.  `gpu.dispatch_eq` states that dispatch returns the source array,
encoded as words, and that the dispatch is race-free.  Its conditions include input arrays and
an output count below 2²⁹, the count's agreement with its parameter or array, an output buffer
with the length header and a slot for every element, and enough invocations to cover the output.
The theorem uses the device model of [the WGSL library](#the-wgsl-library-and-the-browser-pages) with strict binary32 arithmetic.
[The kernel examples](../Verified/Examples/Wgsl.lean) compile ordinary Lean
definitions with both backends.  [Their native-value proofs](../Verified/Examples/WgslProof.lean)
combine the generic dispatch theorem with the generated `denote_eq` equations.

[Binary32 GPT](../Demos/Gpt32/Verified.lean) compiles the kernel functions of the binary32 GPT
application unchanged.  [Its dispatch proofs](../Demos/Gpt32/VerifiedDispatch.lean)
reuse `Compiled.dispatch_value`, which transfers source correctness through a native
denotation equation.  [Its host theorem](../Demos/Gpt32/VerifiedHost.lean) instantiates the
application's typed generation proof with the map of these kernels.  It states the native step's scores
and race freedom under the same device model and shape, token, and weight bounds.  [The WGSL
tests](#wgsl-tests) compare these kernels and those of the examples with native Lean.

### PTX kernels

[`Verified.PTX.compile`](../Verified/PTX/Compile.lean) translates the builds of words, Booleans,
and binary32 values that `Verified.WGSL.compile` translates, without the WGSL translation's limits:
word division and remainder take any divisor, and a binary32 constant may be an infinity or a NaN.
[The PTX translation](../LeanExe/PTX/Translate.lean) keeps each word, each Boolean as 0 or 1, and
the bits of each binary32 value in a `.b64` register, and it evaluates the operands of `&&`, `||`,
and conditional expressions in branches, as the source semantics does.  A binary32 operation moves
its operands into `.f32` registers, and the translation replaces a NaN result by `0x7fc00000`,
since PTX leaves single-precision NaN results unspecified and Talos's NaN results are that NaN.
Absolute value clears the sign bit of the word, which keeps a NaN's payload as Talos's `abs` does.
The typed API constructs a kernel as follows:

```lean
import Verified.PTX.Compile

def ptx := (Verified.PTX.compile (e := .word) compiled.wordScan.func.body).get (by decide +kernel)
def kernel : LeanExe.PTX.Module := ptx.module
```

`ptx.executions_eq` states the launch theorem under [the PTX memory
model](../LeanExe/PTX/MemoryModel.lean): a consistent execution exists, and in every consistent
execution no access of a thread is in a data race, every thread ends, and the copy back reads the
count followed by the source array's encoded elements.  Its conditions are those of the WGSL
dispatch theorem for the arguments, an output of the count followed by one word for each element,
and a launch of at least the count's threads in fewer than 2³² blocks with fewer than 2⁶⁰ threads.
`ptx.launch_value` states the sequential run of the launch, which leaves the same words and is
race-free.  `LaunchSeq` and `LaunchMeets` name the two conclusions for a kernel's statements.
`Verified.PTX.Compiled.of_wgsl` in [`Verified/WgslPtx.lean`](../Verified/WgslPtx.lean) gives, for a
build that both compilers translate, the equality of the PTX and WGSL `spec`, arguments, and
encoding, so a PTX launch theorem can take the `Spec.Fits` proof of a WGSL dispatch theorem, as
[the GPT-2 PTX kernels](../Demos/Gpt32/VerifiedPtx.lean) do, and [the GPT-2 PTX
host](../Demos/Gpt32/VerifiedPtxHost.lean) composes their launches into a generation step.  [The PTX
examples](../Verified/Examples/Ptx.lean) compile the WGSL examples, [the binary32
example](../Examples/Binary32/CompiledPtx.lean) compiles its kernels, and
[`tests/ptx/run.sh`](../tests/ptx/run.sh) compiles their text with `ptxas` and compares their
output words with native Lean on an NVIDIA GPU.  [`tests/ptx/nearest.sh`](../tests/ptx/nearest.sh)
checks the meaning of `cvt.rni.f32.f32`, which the ISA does not state for every input, on all 2³²
binary32 inputs.

### The WGSL library and the browser pages

[`LeanExe/WGSL/`](../LeanExe/WGSL) defines the WGSL subset of the kernels, a printer, a parser that `Module.parse_print` proves to invert the printer, and the device model, a semantics in which binary32 operations compute Talos's `IEEE32` results and a dispatch runs its invocations in order.  [`MemoryModel.lean`](../LeanExe/WGSL/MemoryModel.lean) states the dispatch's executions under the Vulkan memory model, with each invocation's reads taken from an oracle, and `Dispatch.executions` in [`MemoryModelProof.lean`](../LeanExe/WGSL/MemoryModelProof.lean) proves that every consistent execution of a race-free dispatch has every invocation end, has no data race, and leaves the output of the sequential model.  `Verified.WGSL.compile`, which [WGSL kernels](#wgsl-kernels) describes, translates into this subset.  [`tools/EmitWgsl.lean`](../tools/EmitWgsl.lean) prints a kernel after checking that the parser reads the text back as the kernel, and [`tools/build-webgpu-host.sh`](../tools/build-webgpu-host.sh), after [`tools/download-wgpu-native.sh`](../tools/download-wgpu-native.sh), builds `build/tools/leanexe-webgpu-host`.

`uv run tests/web/serve.py` serves a kernel page and a GPT-2 page on http://127.0.0.1:8000/.  The kernel page runs the WGSL kernel cases on the browser's WebGPU and compares every word with native Lean's, and the GPT-2 page runs GPT-2 124M in binary32 with its kernels on WebGPU, in `gpt32.wasm`, or on both with their scores compared.  The pages load the verified compiler's kernels and cases, which `tests/wgsl/run.sh` writes to `build/wgsl` without an option, and its modules `build/verified/gpt32.wasm` and `build/verified/gpt.wasm`.  The GPT-2 page needs the weights that `uv run tests/gpt32/generate.py --export` writes, and [the description of the pages](../tests/web/README.md) covers the setup, the controls, and what is proved about the pages.

### Emitting and running

```sh
tools/leanrun --timeout 60m lake build Library.Random.Lcg.Verified
mkdir -p build/verified
tools/leanrun --timeout 10m lake env lean --run tools/Emit.lean \
  Library.Random.Lcg.Verified Library.Random.Lcg.compiled.module build/verified/lcg.wasm
wasm-tools validate build/verified/lcg.wasm
build/tools/leanexe-wasmtime-host call build/verified/lcg.wasm advance i64 i64:3 i64:1
```

`Verified` is not a default target, so `lake build` alone does not build it.  Every Lean command runs through [`tools/leanrun`](#toolsleanrun-and-the-shared-lock).  `Emit.lean` evaluates the module, encodes it, checks that the decoder returns it, and writes the file.  [The Wasmtime host](#the-wasmtime-host) runs the module: it allocates an array argument through `alloc`, prints a float as its bit pattern, and reads a pair result with the kind `list:`.  `call-stats` also prints the runtime's allocation and release counts.  Besides the definitions, the module exports `alloc`, `release`, its memory as `memory`, and the counters `allocCount` and `freeCount`.

### The Wasmtime host

[`tools/download-wasmtime.sh`](../tools/download-wasmtime.sh) fetches the C API of Wasmtime 44.0.0, and [`tools/build-wasmtime-host.sh`](../tools/build-wasmtime-host.sh) builds `build/tools/leanexe-wasmtime-host` from [`tools/wasmtime-host.c`](../tools/wasmtime-host.c).  On an ARM Mac, [`tools/bootstrap-macos.sh`](../tools/bootstrap-macos.sh) installs the pinned tools in repository-local paths.  The host enables Cranelift's NaN canonicalization so that float results follow the deterministic profile.

```sh
build/tools/leanexe-wasmtime-host call build/verified/gcd.wasm gcd i64 i64:48 i64:18
build/tools/leanexe-wasmtime-host call-stats build/verified/sumCount.wasm sumCount array-u64 \
  array-u64:1,2,3
build/tools/leanexe-wasmtime-host call build/verified/insert.wasm insertLevel \
  list:array-u64,array-u64 array-u64:105,101 array-u64:4,6 i64:1 i64:103 i64:5
```

The form is `call MODULE.wasm FUNCTION RESULT-KIND ARG …`.  The first command prints `6`, the second prints `[6, 3]` and `stats 4 2`, the allocation and free counters after the call, and the third prints `[105, 103, 101]` and `[4, 5, 6]` on separate lines.  A structure, sum, or pair argument is passed as one argument per component.

| Argument | Meaning |
|---|---|
| `i64:N` | Word. |
| `f64:BITS`, `f32:BITS` | Float given by its bit pattern as a decimal word. |
| `array-u64:N,N,…` | `Array UInt64` that the host allocates through `alloc`.  `array-u64:` is the empty array, and a float array passes the elements' bit patterns. |
| `file-u64:PATH` | `Array UInt64` read from a file of little-endian words. |
| `chain-u64:N,N,…` | `List UInt64` as a chain of records. |
| `tree-u64:K,L,R` | Tree of the `KeyTree` layout in preorder, with `.` for a leaf, such as `tree-u64:5,3,.,.,.`. |
| `records-u64:W,M,S,…` | Tree of records in preorder: `.` for null, and otherwise the width, the child mask, and the slots, where a slot whose mask bit is set is a tree, such as `records-u64:3,6,3,2,0,1,7,.` for `Term.add (.lit 7) .zero` of [the tagged example](../Verified/Examples/TaggedTypes.lean). |
| `bytes:HEX`, `bytes-file:PATH` | Byte object, passed as a pointer and a length. |

| Result kind | Output |
|---|---|
| `i64`, `f64`, `f32` | One decimal word, the bit pattern for floats. |
| `array-u64` | Elements, as `[a, b, …]`. |
| `chain-u64`, `tree-u64`, `records-u64` | List as `[a, b, …]`, or tree in the preorder form of its argument, after the host checks each record's header.  `records-u64` prints the width and mask that each header holds. |
| `file-u64:PATH` | Array, written to a file. |
| `list:K1,K2,…` | Several results, one line each.  Each kind is `i64`, `f64`, `f32`, `array-u64`, `chain-u64`, `tree-u64`, or `records-u64`. |
| `slots:N` | `N` words on one line. |
| `bytes` | Two results, a pointer and a length, printed as the bytes in hexadecimal. |

`session MODULE.wasm` reads commands from standard input, one per line, and keeps the instance between calls, which [`tools/gpt2.py`](../tools/gpt2.py) and [the GPT session checks](../tests/gpt/sessions.sh) use.  `script` mode reads the same commands and allows one call.  A value in a command is a decimal word, `result:K` for result `K` of the last call, or `u64:V` for a variable that `read-u64` set.

| Command | Effect |
|---|---|
| `alloc ID SIZE`, `bytes ID HEX`, `bytes-file ID PATH`, `file-u64 ID PATH` | Allocate an object and name its pointer `ID`. |
| `write-u64 ID OFFSET VALUE`, `write-ptr ID OFFSET ID2`, `write-bytes ID OFFSET HEX` | Write into an object. |
| `arg-u64 VALUE`, `arg-ptr ID`, `arg-f64 BITS` | Push an argument for the next call. |
| `call FUNCTION NRESULTS` | Call an export and print `results r0 r1 …`. |
| `keep ID VALUE` | Name a value, such as a returned pointer, `ID`. |
| `save-u64 VALUE PATH` | Write the array at a pointer to a file. |
| `read-u64 V PTR OFFSET`, `read-memory PTR LEN` | Read memory after a call. |
| `stats`, `memory-size`, `done` | Print the counters, print the memory size, or stop. |

A host releases an object it owns by calling the export `release` with the pointer.  `release` traps when the header lacks the magic number or the count is not 1, so a second release of one pointer traps.  The host also has test commands for the allocator (`release-reuse`, `free-alias`, `temp-byte-call`, `temp-array-call`, `noarg-temp-reuse`, and `allocator-grows`), which [`tools/wasmtime-host.c`](../tools/wasmtime-host.c) documents.

Options before the mode configure WASI.  `--wasi` links WASI preview 1, and `run MODULE.wasm` enables WASI and calls `_start`.  `--stdin-file`, `--stdout-file`, and `--stderr-file` give the guest's streams, which the guest otherwise inherits from the host.  `--arg VALUE` appends `VALUE` to the guest's arguments, the first of which takes the place of a program's name, `--env NAME=VALUE` adds a variable to the guest's environment, and `--dir PATH`, given at most once, preopens the directory `PATH` as descriptor 3 under the name `.` with the rights to read and write its directories and files.  `--random-bytes PATH` makes `random_get` give the bytes of the file `PATH` in order, as [the WASI manual](wasi.md#wasmtime-host) states.  `--control-file` receives the host's own output, the control records, which otherwise go to the host's stdout.  [The WASI manual](wasi.md#wasmtime-host) states which combinations each mode requires.  In WASI mode, the control output of a failed run ends with `wasi-exit N`, `trap`, or `error`, and in `run` mode the host writes records only to a control file.  Without `--wasi`, the host writes no outcome records, and its status and stderr report a failure.

| Record | Meaning | Host status |
|---|---|---|
| Result line, `results r0 r1 …`, `u64 V X`, `memory P L HEX`, `memory-size N`, `saved N` | Output of a call or a script command. | 0 |
| `stats A F` | Allocation and free counters after `call-stats` or the `stats` command. | 0 |
| `return` | `_start` returned in `run` mode. | 0 |
| `wasi-exit N` | Call of `proc_exit` by the guest with a status `N` that Wasmtime accepts. | `N` modulo 256 |
| `trap` | Trap in the export that the mode or a script `call` command calls. | 2 |
| `error` | Any other failure after the control output opens: a Wasmtime error, a rejected exit status, a trap in `alloc`, `reset`, or module initialization, a malformed result, or a host failure. | 1 |

### Linux executables of WASI commands

The AArch64 back end writes a WASI command as a static Linux executable for AArch64, which runs without a WebAssembly engine.  `genWasiElf` of [`LeanExe/A64/Wasi.lean`](../LeanExe/A64/Wasi.lean) compiles the module's functions to A64 code and implements each import with a stub that computes the import's function in the shim's environment `linuxEnv` of [`Verified/Shim/Satisfies.lean`](../Verified/Shim/Satisfies.lean).  The stubs of reads, writes, clocks, random bytes, and files make Linux system calls through `SVC #0`, the stubs of the arguments, the environment, and the preopened directory read Linux's initial stack or the shim's scratch, an area above linear memory that records the descriptor numbers that the shim holds open and holds the buffers of its calls, and the stub of `proc_exit` ends the process with `exit_group`.  Each system call is a call of [the Linux call layer](a64-bare-metal.md#the-linux-call-layer), whose table `tools/linux-calls.py` generates from syzkaller's description of Linux and whose rule `step` changes the process's memory only in a call's output region, the frame that `step_frame` proves.  The generator accepts a command whose flat calls lie in `shimCalls`, the calls that `clockTimeGet`, `randomGet`, `argsSizesGet`, `args`, `environSizesGet`, `environ`, `withOpen`, `fdRead`, `fdWrite`, `fdFilestatGet`, `fdPrestatGet`, and `fdPrestatDirName` make, and it rejects any other import with the message `an import NAME with no stub`.  The module's functions may have frames of 4,096 bytes or more, which the generator of the bare-metal programs rejects.  [The AArch64 document's section on WASI commands](a64-bare-metal.md#wasi-commands) describes the executable's layout and its stubs, and [its section on the stamp executable](a64-bare-metal.md#the-stamp-executable) describes an executable that makes the layer's calls without WASI.

The executable `a64-wasi` of the Lake package writes the executables.  `a64-wasi wasm IN OUT` writes to `OUT` the executable of the module file `IN`, with `_start` at the module's export of that name, a linear memory of 4,096 pages, and a stack's room of 65,536 bytes below `main`'s frame, and `a64-wasi module IN OUT CAP` writes it with a linear memory of `CAP` pages and prints the address of the module's area.  `a64-wasi emit DIR` writes the executables of the tests, as [its source](../tests/TestSupport/A64/WasiElfMain.lean) describes.  After the shell commands of [`verified_compile_wasi`](#verified_compile_wasi), these write the files command's executable and run it on an AArch64 Linux host with the directory as descriptor 3, where it writes `hi.` and exits with status 0, as it does in the Wasmtime host:

```sh
tools/leanrun --timeout 60m --memory-high 8G lake build a64-wasi
tools/leanrun --timeout 30m lake env .lake/build/bin/a64-wasi wasm build/wasi/files.wasm \
  build/wasi/files.elf
chmod +x build/wasi/files.elf
build/wasi/files.elf 3<build/wasi/dir
```

The program's arguments and environment are those that Linux places on the process's initial stack, so the first argument that `args_get` returns is the process's `argv[0]`.  When the module imports `path_open`, `fd_close`, `fd_read` or `fd_write` on a handle, `fd_filestat_get`, `fd_prestat_get`, or `fd_prestat_dir_name`, the executable checks descriptor 3 with `openat` before `_start`: a directory there becomes the preopened directory, a closed descriptor 3 or one that is not a directory leaves the process without one, and every other result, such as descriptor 0, which Linux returns when the standard input is closed, ends the run with status 67.  The process exits with the status that the program passes to `proc_exit`, with 1 for a status of 126 or more, which the shim rejects as Wasmtime 44 does, and with 2 after a trap of the guest or of the shim.  The shim follows the Wasmtime host in its errnos and in the order of its checks, and [the table of the shim's differences](wasi.md#differences-from-wasmtime) lists the replies in which it differs, such as errno 31 (`isdir`) for a read of a directory, where Wasmtime answers 8 (`badf`).  Under `qemu-aarch64` 8.2.2, QEMU's user-mode emulator, which the tests also use, a `path_open` that passes the shim's checks gives errno 29 (`io`), since QEMU answers `openat2` with `ENOSYS`.  QEMU 9.2 is the first release that implements `openat2`, and the manifest checker's driver refuses an older `qemu-aarch64`.

## Proving

### Representations

`Represent α` defines the representation of a value for a compiled function: its WebAssembly values, the heap data they point to when borrowed and when owned, the blocks its owned objects occupy, the regions a call reads, and the pointers a call consumes.  `Scalar` covers values without heap data: `UInt64`, `Float`, `Float32`, `Unit` for a function without parameters, pairs, and any type with a `Flat α β` instance, which represents `α` as the scalar `β`.  `Bool` has the instance `cond b 1 0` built in, and a user enumeration, structure, or sum needs its own `Flat` instance, such as `Flat Calc (UInt64 × UInt64 × Op)` in [the enumeration example](../Verified/Examples/Enums.lean).  The instances are part of what the theorem states.

Arrays have instances for `Array UInt64`, `Array Float`, `Array Float32`, and `Array α` for a flat `α`, which is stored as `flatWords xs`.  `LeanExe.Bytes` has the instance of [the byte representation](../LeanExe/Pipeline/Bytes.lean), a pair of represented types is represented by its components, and a structure whose `Flat` tuple holds arrays is represented as that tuple through [the flat records](../LeanExe/Pipeline/FlatRecords.lean).  `Moved α` represents a consumed argument for these arrays, for `LeanExe.Bytes`, and for types with `Encode`, and [the moved tuples](../LeanExe/Pipeline/MovedTuples.lean) extend it to a pair, as the moved values of its components with their objects apart, and to a structure or a sum, as its `Flat` tuple.  A function's argument tuple gives an owned parameter the type `Moved`.

A type with `Encode` and `EncodeWellFormed` instances is represented by the records that `encode` gives, a `Node` tree of words, children, arrays, and buffers, and `List UInt64` has both instances built in.  A user recursive type needs an `Encode` instance, from which `verified_recursive_type` derives `EncodeWellFormed` and the declarations that compile programs over the type, as [Ownership](#ownership) describes.  `EncodeSlotted` states that every record of an encoded value has a slot, which gives the slot regions of a borrowed value positive length, as the keep lemmas of [the VKB entry on region frames](../VKB/entries/region-frame/README.md) require, and `List UInt64`, `Words`, `KeyTree`, and `Verified.Tree shape` have instances.

### The `Implements` family

| Predicate | Statement |
|---|---|
| `Runs aborts env m k store args P` | Every run of entry `k` with enough fuel returns values satisfying `P` or, when `aborts`, traps at `unreachable`.  `ReturnsOrAborts` is `Runs true`. |
| `Implements m k f` | `ImplementsA true m k f` without a precondition or a postcondition, as `Implements.toA` states.  A run may trap. |
| `ImplementsPureA aborts m k f` | For scalar arguments and results: from any store, the call returns the values of `f x` and leaves the store unchanged, or traps when `aborts`.  `ImplementsPure` is the `true` case, `ImplementsPure.implements` derives `Implements`, and `ImplementsPureA.implementsA` derives `ImplementsA` with a postcondition that keeps the heap and the store.  `p.f.pure` states it. |
| `ImplementsA aborts m k f Pre Post` | Statement of [the `implements` theorem](#the-implements-and-trapfree-theorems), with the abort flag, a precondition `Pre x heap store`, and a postcondition `Post x heap store heap' final`.  `ImplementsA.implements_of` derives `Implements` from `ImplementsA true` when `Pre` always holds. |
| `ImplementsTables aborts m k f tables Pre Post` | `ImplementsA` with the further premise that each table of `tables`, an address and its words, is borrowed and is disjoint from the moved blocks.  A wrapper's `p.f.implements` and `p.f.trapFree` state it. |
| `ImplementsStatic pool aborts m k f tables Pre Post` | `ImplementsTables` with the further premise `pool.Input heap store params x` on the byte-literal pool.  The functions of a program with nonempty byte literals state it. |
| `Satisfies m k P Q` | For inputs satisfying `P`, the call traps or returns an owned `y` with `Q x y`.  `Implements.transfer` derives it from `Implements` and `∀ x, P x → Q x (f x)`. |

A theorem about a function of several parameters takes them as one tuple in declaration order, as `lcg_advance` states `ImplementsA false compiled.module 4 (fun x : UInt64 × UInt64 => advance x.1 x.2)`, and the entry index is the function's index in the module, which [the generated declarations](#generated-declarations) give.  The arguments are reversed in `Runs` because Talos lists them with the top of the stack first.  A call of `gcd a b` therefore takes `[.i64 b, .i64 a]` in `Library.Numerics.Arithmetic.Gcd.gcd_call`.

### Using the generated theorems

The generated theorems state facts about Lean functions, so a theorem about a program combines with them in ordinary Lean.  `p.bytes` gives the bytes and their decoding, and `p.f.implements` gives a function's theorem.  `lcg_advance` in [`Library/Random/Lcg/Verified.lean`](../Library/Random/Lcg/Verified.lean) combines the module's bytes and theorem with the period theorem of [`Library/Random/Lcg/Period.lean`](../Library/Random/Lcg/Period.lean):

```lean
theorem lcg_advance : ∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok compiled.module ∧
    LeanExe.Pipeline.ImplementsA false compiled.module 4
      (fun x : UInt64 × UInt64 => advance x.1 x.2) (fun _ _ _ => True) (fun _ _ _ _ _ => True) ∧
    ∀ x y : UInt64, ∃! n : UInt64, advance n x = y := by
  obtain ⟨bytes, success, decoded, _⟩ := compiled.bytes
  exact ⟨bytes, success, decoded, compiled.advance.implements, advance_existsUnique⟩
```

A theorem for one function gives a theorem for an equal function by rewriting: `lcg_jump` rewrites `compiled.jump.implements` with `jump_eq`, which states that the jump-ahead program computes `advance`.  `ImplementsA.mono` strengthens a precondition or weakens a postcondition, and `drone_trapFree` in [`Demos/Drone/Verified.lean`](../Demos/Drone/Verified.lean) uses it to replace the planner's bound by the constant 2,251,064.  The drone's theorems `drone_compute` and `drone_safe` combine the bytes with the planner's optimality and safety theorems in the same way.

### Bounds and total execution

`p.f.bound x` counts the bytes by which the allocator's `top` can increase during the call: 48 bytes of header plus the payload for each copy, each built array, and each block of `push`, `++`, and `insertAt`, with no reuse of freed blocks.  `p.f.bound_eq` states the bound as a Lean term that has the structure of the definition: the loop counts, states, and call arguments of the program, the block sizes `blockCost`, `growCost`, `paidGrowCost`, and `creditCost` of [`Verified/BoundFacts.lean`](../Verified/BoundFacts.lean), `loopCost` and `sumBelow` of [`Verified/Bound.lean`](../Verified/Bound.lean) for loops and builds, `min` of the unpaid and paid bounds for a loop whose state is a paid pair, and `p.g.bound` at the arguments of a call, or, for a callee `g` with a paid parameter, `p.g.cost` and `creditCost` of each argument that the call charges.  A function that allocates nothing gets `p.f.bound x = 0`, and a record's arrays appear as its fields, such as `b.prices.size`.  `BoundFacts.lean` gives the closed forms, such as `blockCost_eq`, sums of `sumBelow`, `loopCost_const` for passes of equal cost, and `loopCost_le`, which bounds a loop's cost by an invariant of its index and state.  `pushSquare_bound` in [`Tables.lean`](../Verified/Examples/Tables.lean) shows the method:

```lean
theorem pushSquare_bound (xs : Array UInt64) (k : UInt64) :
    compiled.pushSquare.bound (⟨xs⟩, k) = 16 * (xs.size + 1) + 80 := by
  rw [compiled.pushSquare.bound_eq, compiled.pushWith.bound_eq, compiled.pushWith.cost_eq,
    creditCost, paidGrowCost_eq]
```

The bound charges an extension of an owned array by amortization.  An owned array of `n` words in a block of `c` bytes holds the potential `4 · 8 (n + 1) ∸ 2c`, and every owned array parameter of a function whose body extends an array, by `push`, `++`, `insertAt`, or a call with a paid parameter, is paid: the caller charges its credit, `creditCost`, 16 bytes per word and length word, and each extension of the paid array is charged `paidGrowCost`, a header and 32 bytes per added word.  The potential covers the bytes of the moves to larger blocks, so a loop of `n` pushes of one word onto a paid state is charged `80 n` bytes plus the credit.  For a function with a paid parameter, `p.f.cost` is the bound without the credits, and `p.f.bound` adds them.  [The internals](../Verified/README.md) give the rules that determine which values are paid.

The bound does not count the reuse of freed blocks and charges every extension of an owned array at its last use as a new block, so a precondition that fails says nothing about the program.  The bound also depends on the modes that `Expr.paramChoice` chooses.  The precondition `heap.Within store p.module (p.f.bound x)` states that `top` plus the bound is at most `65536` times the memory's cap, at most 4,294,901,760 bytes, and no theorem bounds the memory's size in pages.

`foldCost xs init step charge` in [the fold lemmas](../Verified/Reflect/FoldLemmas.lean) sums each fold step's allocation charge at its element, index, and accumulator.  The generated bound adds the initial expression's charge, a copy of a borrowed initial state when needed, and its potential credit.  A fold whose steps allocate nothing has charge 0.  The bound calculation uses natural arithmetic over the array's word-sized count.  It adds no executable `Nat` counter.

### Bounds of recursive functions

For a tail loop, the bound equation sums native per-step charges with `Verified.Tail.costAt` over the proof-derived rank plus one.  The charges come from the ordinary expression-bound builder with a continuing call charged at zero.  A loop whose steps allocate nothing has bound 0 without evaluating its rank.  A loop that calls guarded code also has a frames equation expressed by `Verified.Tail.fitsAt`: each iteration checks its callees at the same available depth.  [The tail example](../Verified/Examples/Tail.lean) proves a zero allocation bound and includes a guarded callee.

For guarded recursion, `p.f.bound k x` and `p.f.fits k x` take the number of frames `k` first, and `p.f.trapFree` holds under `p.f.fits 1000 x = true ∧ heap.Within store p.module (p.f.bound 1000 x)`.  `p.f.fits_eq` and `p.f.bound_eq` state `p.f.fits (k + 1) x` and `p.f.bound (k + 1) x` for every `k`, with `p.g.fits k` and `p.g.bound k` at each depth-taking call, self-calls included.  For a function with a paid parameter, `p.f.cost_eq` states `p.f.cost (k + 1) x` in this way, with `p.g.cost k` and `creditCost` at a call of such a `g` with a paid parameter, and `p.f.bound_eq` states `p.f.bound k x` as the credits plus `p.f.cost k x`.  `p.f.fits 0 x = false` holds by `rfl`, so a property of `p.f.fits 1000 x` follows by induction on `k`.  In [`Recursion.lean`](../Verified/Examples/Recursion.lean), `chain_fits` shows in this way that `compiled.chain.fits k n` holds exactly when `n < k`, and `chain_trapFree` that the module computes `chain n` without a trap for every `n` below 1,000.  `fill_fits`, `fill_cost`, and `fill_trapFree` do the same for a recursion that extends a paid array parameter and moves it into the next call.

### WASI programs and their executables

The theorems about a WASI command form a chain from its native action to its Linux executable.  The generated theorems of `verified_compile_wasi` state the module's runs in Talos's semantics for every host that satisfies the WASI host specification.  The shim's theorems apply `compiled_native_start_run_with`, the general form of `p.start`, to the shim's environment and state a footprint, the Linux call layer's events of each run, and the executable's theorems take that footprint as a premise and state the run of the A64 process in the relation `ProcReachWith` of the layer's binding.

| Theorem | Statement | Premises |
|---|---|---|
| `p.f.implements`, `p.start` | Each run of the export or of `_start` with enough fuel performs the native action's ordered effects with the same result or terminal outcome, or, when the flag `aborts` is true, a prefix of them before a guest trap. | A host environment that satisfies `hostSpecWith host p.sysCalls`, or `hostSpec host` for a program without flat calls, the representations of the heap, the arguments, and the literal pool, the separation of the moved blocks from the regions that the call reads and of those regions from the low memory `[0, 4096)`, a memory cap of at most 65,535 pages, and, when `aborts` is false, `Heap.Within` and `Resource.CallPrefixBound` for a budget. |
| `p.f.total`, `p.total` | The export returns or exits with an accepted status, and `_start` exits with an accepted status. | Those of `p.f.implements` or `p.start` with `aborts` false, and `host.NoTrapsAlong` the native action. |
| `p.handles`, `p.f.handles` | `Action.BracketRuns`: every `Exec` and `Prefix` run of the action has a well-bracketed trace, so each use of a handle lies between its open and its close. | None: the theorem holds for every host. |
| `linuxEnv_satisfies` | The shim's environment `linuxEnv F L I replies calls` satisfies `hostSpecWith (linuxHost F L I replies) calls`. | Every call of `calls` lies in `shimCalls`, and the module imports at most the stream functions and the calls of `calls`. |
| `shim_footprint` | Every run of `_start` under `linuxEnv` with enough fuel ends in a Talos trap, which is also how an exit ends a run in Talos.  The Linux call layer's events of the run extend the world's events by the images of a WASI trace of the action, the layer events that `Image` admits for each WASI event, each of which holds its reply of the sequence (`Carried`) and writes within the guest's `2^32` bytes or into the timespec or the `statx` record of the shim's scratch (`WritesWithin`).  The trace ends at an accepted exit, a rejected exit, or a trap of the shim, or, when `aborts` is true, at a guest trap after a prefix. | Those of `p.start`, with the flat calls in `shimCalls`, for every choice of open flags, layout, launch, and reply sequence. |
| `footprint_namesHeld` | The layer events of such a run name only the standard streams and the numbers of `openNumbers`, which the shim holds open: 3 when the launch grants it, and each number below `descriptorLimit`, 1,024, that an `openat2` returned, each until its close. | A run that `Footprint` describes. |
| `wasiElf_footprint` | The process of the executable that `genWasiElf` writes reaches `exit_group` in `ProcReachWith`.  Its trace holds the events of the check of descriptor 3 and then the images of a run of the action under `linuxHost`, each of which writes within linear memory or into the timespec or the `statx` record of the shim's scratch, and X0 holds the accepted exit's status, 1 after a rejected exit, 2 after a trap, or 67 when the check of descriptor 3 ends the run.  `wasiElf_run` states the same run for a fuel at which Talos's run of `_start` traps, and `wasiElf_footprint_with` takes a footprint of one reply sequence. | The kernel's check of the file's bytes and program headers, imports whose flat calls lie in `shimCalls`, a stack's room that is a multiple of 16 and holds `wasiStackBound`, the loader's placement of the file (`ElfLoaded`), Linux's initial stack (`InitialStack`), the program counter at the entry, an empty trace, and the footprint at the executable's memory cap for every launch and reply sequence. |
| `readall_elf`, `environ_elf`, `prestat_elf`, `clockrandom_elf`, `sys_elf`, `files_elf` | `wasiElf_footprint` at `environ.elf`, `prestat.elf`, `clockrandom.elf`, `sys.elf`, or `files.elf`, with the bytes that the process wrote to descriptor 1 for each but `prestat.elf`, and with the descriptor numbers that the events name for `files.elf`.  `readall_elf` holds for every choice of open flags and launch, since `readall.elf` makes no flat call and no check of descriptor 3, and it states that each event writes within linear memory and the bytes that the process read from descriptor 0 and wrote to descriptor 1. | `ElfLoaded`, `InitialStack`, the program counter at the entry, and an empty trace. |
| `readall_elf_message` | The readAll executable writes to descriptor 1 the bytes that its reads of descriptor 0 returned, and it exits with status 0 when they number at most 1,000,000 and 1 otherwise. | Those of `readall_elf`, and replies of the class `Steady`, which holds Linux's replies when the standard input is a regular file or a pipe, the standard output is a regular file or a pipe, and no call reports an error. |

A command's executable theorem follows in three steps, as the files command's modules show.  `calls_supported` of [the files command's footprint](../Verified/Examples/WasiFilesShim.lean) decides with `decide +kernel` that the command's flat calls lie in `shimCalls`, and `linux_footprint_native` of [its native footprint](../Verified/Examples/WasiFilesNative.lean) applies `command.start` at the executable's store `nativeStore` with `aborts` true and the budget 0, so it needs no resource premise.  [The executable's theorem module](../tests/TestSupport/A64/ImageFilesWasiFiles.lean) reads the file with `file_nat%`, checks its bytes, program headers, entry, and stack bound with `decide +kernel`, and applies `wasiElf_footprint`.  The module lies outside every build target, since the file must exist when Lean elaborates it, and `tests/linux/a64-wasi-files.sh` elaborates it in the file's directory.

The shim's and the executables' theorems hold for every reply sequence of the Linux call layer, and only `readall_elf_message` and the manifest checker's `manifest_elf_meets` assume a property of the replies.  [The layer's reply properties](../LeanExe/Linux/Replies.lean) name the properties of Linux's replies that a theorem may assume: `LeanExe.Linux.FreshOpens`, that a call that returns a descriptor returns an error or a number that is not open, `NsecBound`, `RandomCount`, and `WrittenPrefix`.  `LeanExe.Linux.FreshOpens` concerns the layer's events, and `LeanExe.Wasi.FreshOpens` is the assumption on WASI traces under which `Action.BracketRuns.exec_descriptors` gives the descriptors that a run holds open.

`linux_message` of [the message corollary](../Verified/Examples/WasiReadAllMessage.lean) states what the command writes and its status under `linuxHost` when its reads and writes succeed, for a budget that fits the memory and bounds every resource prefix of `main`.  `linux_exec_message` and `linux_exec_succeeded` state the same facts from an `Exec` run and the images of its trace, the form in which `wasiElf_footprint` states a run, the second when the run's WASI events meet `Succeeded`.  `budget_bounded` of [the class corollary](../Verified/Examples/WasiReadAllSteady.lean) proves such a bound for every reply sequence, and `linux_steady` states the accepted exit and the copied bytes for every reply sequence of the class `Steady`.  `readall_elf_message` takes from `wasiElf_footprint_with` and `linux_footprint_budget` of [the native footprint](../Verified/Examples/WasiReadAllNative.lean), the footprint at `nativeStore` without a guest trap for every reply sequence and every cap from 16 to 65,535 pages, an `Exec` run that ends at an exit, and from `linux_exec_succeeded` its status and its copied bytes.  [The WASI manual's section on the shim](wasi.md#the-linux-shims-specification) and [the AArch64 document's section on WASI commands](a64-bare-metal.md#wasi-commands) state these theorems in full.

### The theorems of a WASI command

The generated `p.start` and `p.total` relate every run of `_start` to the native action `main` followed by its exit, so a theorem about what a command does is a theorem about the runs of that action under `Exec` of [the semantics](../LeanExe/Wasi/Semantics.lean).  The demos state each request as a predicate over a run's events and prove it of every run of the action, and further theorems state it of the module, of total execution, and of the native executable.  The table names the declarations of [the random-residue histogram](../Demos/RandomHistogram/README.md).  [The random choice](../Demos/RandomChoice/README.md) and [the manifest checker](../Demos/ManifestCheck/README.md) use the same names in their own namespaces, with the additions that the table marks.

| Declaration | Statement | Premises |
|---|---|---|
| `Meets host world events code` | The request over the events of a run from `world`, which record each call and the host's reply, and its status `code`: the events of `args`, then those that the request asks for that argument buffer, with the status that it asks for.  Its module, `CommandSpec.lean`, imports the reviewed specification and none of the command's definitions. | A definition |
| `exec_main` | Every run of `main` followed by its exit that ends with the status `code` has the events `events ++ [.exit code]`, where `events` meet `Meets`, and `code` is at most 77, or 78 for the random choice. | None: it holds for every `Host` |
| `Ends`, `start_ends` | Every run of `_start` from the command's initial store with enough fuel ends at the accepted exit after events that meet `Meets`, at a trap of the host or an exit that the host rejects after a run of `main`, or at a guest trap at `unreachable` after a prefix of `main`. | A host environment that satisfies `hostSpecWith host command.sysCalls` |
| `total_meets` | Every such run ends at the accepted exit after events that meet `Meets`. | Those of `start_ends`, a budget that fits the initial store's free memory and bounds every resource prefix of `main` (`Resource.CallPrefixBound`), and `host.NoTrapsAlong` the action |
| `body_bounded`, `call_prefix_bound`, and `budget_fits` or `initial_within` | Every run and every prefix of `main`'s body charges at most `budget`, `call_prefix_bound` gives `CallPrefixBound` from it, and the budget fits the memory.  The manifest checker's `body_bounded` bounds them from one world, by the world-indexed rules. | A bound on the host's successful replies that size a block: those of `args_sizes_get`, and for the manifest checker the reply to the manifest's `fd_filestat_get` along `main` (`StatAlong`) |
| `total_meets_every` (random choice), `total_meets_budget` (manifest checker) | `total_meets` with its budget premises proved. | The bound on the replies and `NoTrapsAlong` |
| `SoFar`, `stops_soFar` (manifest checker) | The events of every run that stops without an accepted exit, at a trap of the host, a rejected exit, or a guest trap, meet `SoFar`: confinement, the use of descriptors, and the verdicts of the lines written before the stop. | None |
| `histogram_elf_counts` (histogram) | The process of the AArch64 Linux executable reaches `exit_group`, and when the results of its system calls lie in Linux's ranges (`InRange`), its status and its system calls meet `Counts`, the statement of `Meets` over the calls, with each `random_get` as its group of `getrandom` calls (`RandomGroup`). | The loader's placement of the file, Linux's initial stack, the program counter at the entry, an empty trace, and arguments whose strings and eight-byte pointers take at most `argsLimit` bytes |
| `choice_elf_choices` (random choice) | The process reaches `exit_group`, and when its system calls meet `InRange`, its status and its system calls meet `Choices`: the calls are groups, each of which mirrors one WASI event of a run whose events make the passes of `Rounds` (`Mirrors`), with the random bytes that the groups of the successful `random_get` calls returned. | Those of `histogram_elf_counts` |
| `manifest_elf_meets` (manifest checker) | The process reaches `exit_group`, with status 67 when the check of descriptor 3 ends the run, and otherwise, when the results of its system calls lie in Linux's ranges (`InRange`), its status and its system calls meet `NMeets` for the check's grant of descriptor 3, the statement of `Meets` over the calls. | Those of `histogram_elf_counts`, and replies that meet `StatxAfterCheck`: the reply to the manifest's `statx`, when the shim reads errno 0 from it, reports at most 1 MiB or at least `2^32` bytes |
| `histogram_elf_witness`, `choice_elf_witness`, `manifest_elf_witness` | Each gives a reply sequence and a process that meet the premises of its native corollary together with its `InRange`, and the process's run to `exit_group`, the histogram's with a short `getrandom` read. | None |

The proof of `exec_main` follows `main`.  `Exec.unbind` separates the run of `main` from that of its exit, and lemmas about each part give the events of a call, of a loop by induction on its passes, such as `draw_loop` of the histogram and `checks_loop` of the manifest checker, and of `writeAll` from `WriteAllRun.taken`.  The theorem holds for every host, so it covers every reply that a host's specification admits, errnos of every call, short reads, and short writes among them.  Each status that `main` returns is an errno, from 0 to 76, or one of the demos' own statuses, 2, 77, and 78, all below 126, at which Wasmtime 44 and the shim reject an exit, so every exit of a run is accepted.

`start_ends` applies `command.start` with `aborts` true and a budget of 0, so it takes no resource premise and admits the guest's trap after a prefix of `main`.  `total_meets` applies `command.total`, which excludes that trap under a budget for the heap that every prefix of `main` allocates, and that heap holds the block of `args`, whose size the host's replies set, so the budget holds only under a bound on those replies.  `Ends` names the three outcomes so that a theorem can state what each one implies, as the manifest checker's `start_ends` gives `SoFar` of the events in both trap cases, from `stops_soFar` and the lemmas of [the runs that stop](../Verified/Wasi/Stops.lean).  No theorem shows that a host meets the premises of `total_meets` together.  `histogram_elf_witness`, `choice_elf_witness`, and `manifest_elf_witness` show it for the premises of the native corollaries: each gives replies and a process whose memory holds the file and an initial stack, `loadedMem` of [the shared witness](../tests/TestSupport/A64/ElfWitness.lean), and states the process's run under those replies to `exit_group`.

`Bounded` of [the resource rules](../Verified/Wasi/ResourceRules.lean) bounds every run and every prefix of a command from every world, and `body_bounded` proves it of the reflected body `command.main.func.body`.  `reported_rule_observed` of [the rule premises](../Verified/Wasi/SysRule.lean) turns the bound on `args_sizes_get` replies into the charge of the block of `args`, and the tactics of [the budget tactics](../Verified/Wasi/BudgetTactics.lean) apply the rules of the other commands, with `loop_bounded` or `loop_bounded_sum` for each loop.  The demos' limit `argsLimit`, 6 MiB, is the most that Linux 4.13 and later let the strings and pointers of `argv` and `envp` take together, so every process that Linux starts meets the premise on the arguments.  The histogram's budget is 6,312,920 bytes and the random choice's 6,306,448 bytes, for every input, and the manifest checker's `budget M` is at most `181 M + 12,649,115` bytes for manifests of at most `M` bytes.

The histogram's native corollary composes the footprint of [the shim](wasi.md#the-linux-shims-specification) with `exec_main`.  `calls_supported` decides that the command's flat calls lie in `shimCalls`, `linux_footprint_native` applies `command.start` at the executable's store `nativeStore` under `linuxEnv`, and `linux_footprint_bounded` applies it with `aborts` false and the budget, which `call_prefix_bound` gives from the shim's answer to `args_sizes_get`, so a run has no guest trap.  `linux_exec_counts` takes an `Exec` run under `linuxHost` and the `Images` of its trace that meet `InRange` and `Sized` and gives the accepted exit with `Counts`: a trapped call has no image that meets `InRange` (`main_trapped` and `image_untrapped`).  `histogram_elf_counts` of [the executable's theorems](../tests/TestSupport/A64/ImageFilesRandomHistogram.lean) composes these with `wasiElf_footprint_with` at the file's bytes, and `carried_sized` gives `Sized` from the replies that the events hold.  `InRange` holds when every `getrandom` returned an error number or a count of at most its length, positive for a positive length, and every `write` an error number or at most its count, the results at which the shim does not trap.  The shim answers a `random_get` with `getrandom` calls until the buffer is full, and `random_group` states the image of a `random_get` as its group of calls, whose bytes are the concatenation of the calls' outputs, each cut at its count.  [The histogram's guide](../Demos/RandomHistogram/README.md#the-native-executable-writes-the-counts) states the Linux facts that `InRange` assumes and the runs with short counts.

The random choice's corollary takes the same steps with `linux_exec_choices` and the histogram's `InRange` and `Sized`.  `Choices` states the request with `Mirrors`, which names, for each kind of WASI event of the command, the system calls that the shim makes for it under `InRange`: a group of `getrandom` calls for a `random_get` and one `write` for a write.  `Choices` requires the system calls to be groups that mirror WASI events that make the passes of `Rounds`, so the reviewed passes apply without a restatement over system calls.  `rounds_mirrors` builds the groups and their mirrors from the images of the passes, and `Images.writeData` gives the bytes that the writes took.

The manifest checker's `NMeets` restates `Meets` over the system calls, and `run_native` and `handled_native` translate `Run` and `Handled` through the image of each WASI event.  Its `linux_exec_meets` excludes a trapped run with `exec_trapped_call`, which finds a trapped call among the events of a run that traps, and `image_untrapped`, under which no call whose image meets `InRange` traps.  The manifest checker's budget depends on the size that `fd_filestat_get` reports, and `linuxHost` answers that call at a world from the reply that the world's number of layer events indexes, so `body_bounded` bounds the body from one world by the world-indexed rules of [`ResourceRulesAt.lean`](../Verified/Wasi/ResourceRulesAt.lean), and its premise `StatAlong` constrains only the replies to the requests of `fd_filestat_get` that the prefixes of `main` make.  `StatAlong` and `StatxBounded`, like `NoTrapsAlong`, are `Host.Along` of a property: each states its property of the remaining action and the reached world at every prefix of the action.  `StatxBounded` states the bound over the reply sequence at each prefix whose next request is that call, so it bounds only the reply to the manifest's `statx`, as [the manifest checker's guide](../Demos/ManifestCheck/README.md#the-native-executable-checks-the-manifest) describes.

### Axiom checks

A theorem may depend only on `propext`, `Classical.choice`, and `Quot.sound`.  Modules such as [the GCD compilation](../Library/Numerics/Arithmetic/Gcd/Compiled.lean) end with `#print axioms` for their theorems, and the build of [`tools/check`](../tools/check) runs at log level info and fails on a report from a file of this repository that names any other axiom.  It then runs [the axiom walk](../tests/verified/AllAxioms.lean), which follows the constants of every declaration of `LeanExe`, `Examples`, `Demos`, `Verified`, `Library`, and `TestSupport` and fails on any other axiom, so a theorem that no `#print axioms` names is checked as well.  A check of other theorems is a Lean file outside the repository that imports their module and prints their axioms, run through [`tools/leanrun`](#toolsleanrun-and-the-shared-lock).  Any further axiom, such as `sorryAx` from an incomplete proof or the axiom that `native_decide` adds, is a failure.

```lean
import Library.Numerics.Arithmetic.Gcd.Compiled
#print axioms Library.Numerics.Arithmetic.Gcd.gcd_call
```

```text
'Library.Numerics.Arithmetic.Gcd.gcd_call' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Testing

### Module cases

[`tests/verified/run.sh`](../tests/verified/run.sh) writes each example's module to `build/verified/`, validates it with `wasm-tools`, and compares every case of [`Verified/Examples/Cases.lean`](../Verified/Examples/Cases.lean) between the Wasmtime host and native Lean.  `Cases.lean` prints one line per case, `module|export|result kind|host arguments|expected result`, computed by native Lean, with an optional sixth field, the number of blocks that must stay allocated after the call, and a seventh, a bound on the number of allocations, the host's included.  The expected result `trap` requires a trap at `unreachable`.  Native Lean writes a panic message for each read, update, or `insertIdx!` past the end, and the script counts these messages and fails on any other output to standard error.  The full invocation needs `lake build`, whose default targets include the module cases of the Euler check, `lake build Verified Library`, and the Wasmtime host `build/tools/leanexe-wasmtime-host`.  The driver adds the default install directories of Cargo and `uv` to its search path.

`tests/verified/run.sh --cases frontend` builds and emits the selected module, validates it, builds its case executable, the one that [the table of case executables](../tests/verified/case-generators.txt) names or otherwise `verified-cases`, and compares its checked cases, including allocation counters.  Its insertion cases cover empty arrays, indices at and beyond the end, the largest word, a computed index, fresh and aliased inputs, and float and record elements.  The full invocation also runs the numerical byte/file proofs and native accuracy checks.  Each module has an entry in [the module registry](../tests/verified/modules.txt) and a checked corpus.  Without `--cases`, the driver also runs the case executables of the modules whose cases `Cases.lean` does not import, and it fails when a module of the registry has no case, except the modules of [the list of other drivers](../tests/verified/no-cases.txt), whose cases other drivers run.  `tools/source-layout` fails when a module of the registry other than `byhand` has no entry in the file-theorem registry.  [The library case map](../tests/verified/library-cases.txt) reuses the compiler fixtures' cases for the shared library compilations.

`tests/verified/run.sh --cases fold` checks word and float folds, record elements without an `Inhabited` instance, owned array and pair accumulators, a borrowed input that is also the initial accumulator, nested folds, and calls in fold bodies.  Allocation counters check retained blocks and growth in place.  A recursive callee runs at depth 999, and the next frame at depth 1,000 must trap.

`tests/verified/run.sh --cases tail` checks default loop compilation through 4,096 iterations, scalar pairs and exceptional floats, record arrays, owned-array growth, swapping and replacement, an aliased seed, calls between tail functions, and a guarded callee.  It checks retained blocks and allocation counts.  The Recursion and Fold examples set `verified.tailLoops` to false to retain their guarded-depth tests.  `tests/verified/run.sh --cases tailconditions` checks Boolean coercions, word inequality, a proof-named conditional, destructured scalar tuples, and borrowed pair and record states through 4,096 iterations.  The borrowed-state cases require one retained input block and no additional allocation.

`tests/verified/run.sh --cases scalarcomposition` checks generated store-preserving scalar
functions: division, conditional calls, tail recursion through 4,096 iterations, float call
chains, and binary32 bit conversion and nearest-even rounding.  Every case checks zero
allocations and retained blocks.  `tests/verified/run.sh --cases relocation` reuses that scalar corpus with its functions
relocated after those of another compiled program.  It also checks the retained library function and a
caller that invokes functions from both libraries.

`tests/verified/run.sh --cases lists` checks construction, duplication, nested calls, matching,
head and tail access, reconstruction, and head updates on lists through 4,096 cells.  It checks
retained blocks and allocation counts, including reconstruction with no allocation beyond the
host's input cells.  `tests/verified/run.sh --cases listrecursion` checks guarded summation and recursive increment.
Depth 999 returns, and depth 1,000 traps at `unreachable`.  Increment reuses each consumed cell.
`tests/verified/run.sh --cases listloops` checks list construction and extension in word-counted
loops through 4,096 iterations, including empty and nonempty seeds.
`tests/verified/run.sh --cases listtail` checks borrowed tail summation and consumed reversal
through 4,096 cells.  Both compile as loops.  Reversal reuses the input headers and retains the
input and accumulator cells in its result.

`tests/verified/run.sh --cases taggedtypes` checks each function of the tagged example on every
constructor, on chains of 998, 999, and 1,000 negations and of 999, 1,000, and 4,096 additions,
and on 20 arbitrary terms of at most 190 constructors, and it checks `add` on 64 pairs of these
terms.  The allocation counts show that `swap` and `right` allocate nothing beyond the host's
records, so `swap` reuses the matched record and `right` releases the rest of its argument, and
that `double` allocates one copy of its argument and one record.  `eval` and `size` return at
depth 999 and trap at `unreachable` at depth 1,000, and `spine` compiles as a loop and returns on
every chain.

`tests/verified/run.sh --cases heapsums` checks the sums with `Bytes`, array, tree, and list
fields: construction from owned arguments, borrowed reads, copies into results and pairs, an owned
match on a constructed value, and two loops whose state is such a sum.  Each case states the blocks
that stay allocated and bounds the allocations, from the costs of the code: the empty array that a
construction of a text, a tree, or an empty item allocates, one block for each array, nonempty
bytes, and tree node of a copy, and the release of each component that a branch does not use.
`grow`, whose wildcard names the matched state, copies its state at every step, and `regrow`, which
rebuilds each constructor, allocates only the rebuilt constructor's empty array.  A guarded call
inside a match returns on 998 cells and traps on 999.  Before the cases, the driver checks that
every theorem of the example uses only the three permitted axioms.

`tests/verified/run.sh --cases typedtrees` passes and prints the trees whose records hold `Bool`,
float, structure, enumeration, and sum fields in the host's `records-u64` form, which native Lean
computes from each type's `Encode` instance, so each case also checks the slot words of the typed
fields.  The cases construct, copy, borrow, and rebuild records and read fields through nested
structures.  The recursions return at depth 999 and trap at `unreachable` on a chain of 1,200
records, and the loops return on that chain.  Each case states the blocks that stay allocated and
bounds the allocations.  Before the cases, the driver checks that every theorem of the example and
of its derived declarations uses only the three permitted axioms.

`tests/verified/run.sh --cases gpt` tests binary64 GPT with the corpus of [`tests/gpt/Cases.lean`](../tests/gpt/Cases.lean) and the release and cache-growth checks of [`tests/gpt/sessions.sh`](../tests/gpt/sessions.sh).  `tests/verified/run.sh --cases euler` uses [the Euler corpus](../Demos/Euler/Cases.lean) through `tests/modules/run.sh --module euler PATH`.  The full invocation includes both application checks.  `tests/verified/run.sh --cases slew` compares the slew planner with native Lean on plans and `atan2` calls that [a generator in Lean](../tests/TestSupport/Slew/Cases.lean) builds from SplitMix64.  [`tests/slew/edges.sh`](../tests/slew/edges.sh) compares the module's `edgeOk` export with native Lean on single-cone edges in one host session, and the same run checks the planner's theorems with [the axiom audit](../tests/slew/Axioms.lean) and its file theorems against the written module.

The cases cover words near 0, `2^32`, `2^63`, and `2^64`, zero divisors, shift amounts of 64 or more, loop counts of 0, 1, and up to 65,537, empty arrays, reads and updates past the end, and floats that are zeros of both signs, infinities, NaN, and the smallest subnormal.  Native Lean returns the canonical NaN for every NaN result, and the host enables Cranelift's NaN canonicalization, so the cases compare float results bit for bit.  The release counts show that a call leaves allocated exactly the result's arrays and the host's arrays at borrowed parameters.  The allocation counts show the updates in place and the growth by doubling: a loop of `n` pushes allocates at most `2 + log₂ (n + 1)` blocks, and an insertion sort of `n` elements at most `3 + log₂ (n + 1)` with the host's array.  One case requests an array of `2^29` words and must trap.  A recursion case runs `deep`, whose frame has 32 positions, 26 of them live across the self-call, to depth 999, where its deepest frame calls `top1` and `top2`, two functions without the call depth that hold many values live.  The drone's cases include the terrains of [`tests/drone/corpus.txt`](../tests/drone/corpus.txt).

### Accuracy checks

Before the module cases, the driver builds the byte-theorem modules of [the file-theorem registry](../tests/verified/numerics.txt) and checks each file module against the file it emitted.  The registry holds every module of the module registry except `byHand` of `Modes`, which has no `p.module`.  Each file module proves that its file holds the encoding and decodes to the module of its byte theorem, with one command, `file_theorems NAME p "PATH" from B₁, …, Bₙ`, which states `NAME_file` and `NAME_file_decode` for `p.module` and prints their axioms.  The proof of `NAME_file_decode` takes its bytes from the byte theorem `B₁` and contains every `Bᵢ`, so its axiom report covers them all.  The registry modules built without the reflector have no byte theorem, so their file modules leave `from` out, and the command proves the decoding with `Wasm.Encoding.decode_encode`.  The driver requires both file theorems to report only `propext`, `Classical.choice`, and `Quot.sound`.  The native accuracy checks then compare implementations with integer references over the argument sets stated in each function's document, including the worst inputs of [`WorstCases.lean`](../tests/TestSupport/Numerics/WorstCases.lean).  They also check fused multiply-add, limb arithmetic, and the parser and printer fixtures in `data/strconv/`.

The checks of `Trig`, `Exp`, and `Log` also compare the stored tables with integer references.  `FourierAccuracy.lean` checks impulse and single-frequency transforms, the round trip, Parseval's identity, the power spectrum, and agreement with an exact transform within its stated tolerance.  Each function's document gives its argument sets, measured distances, and proved accuracy bound.

### Recorded checks

`tests/verified/run.sh` records each check that passes as the SHA-256 hash of the check's inputs, in `build/verified-checks/checked/`, or in `build/verified-checks/fast/` after a [fast build](#fast-builds), and in a later run of the same mode it skips a check whose inputs still have the recorded hash.  A failed check leaves no record and runs again, and `--no-cache` runs every check and records the passes.  The driver prints `run: CHECK` before a check that runs and `unchanged: CHECK` for one that it skips, the number of cases that it did not run after `verified: passed P failed F`, and the counts of both kinds of check at its end.  The build of the targets, the case executables, and the check of their standard error run every time, since the case lines that the executables print are inputs of the case checks.  [The repository instructions](../AGENTS.md#builds-and-checks) require `--no-cache` in the periodic full run, and every item of `tools/check` passes it.

| Check | Inputs |
|---|---|
| `emit NAME`, the emission, decoding, and validation of a module | `tools/Emit.lean`, the module and constant names, the version of `wasm-tools`, and the Lean inputs of the module and of `Emit.lean`; the record also holds the hash of the written file, which must not have changed |
| `file NAME`, a file theorem module | the file theorem module, its Lean inputs, and the written file |
| `audit FILE`, an axiom audit or another elaborated file | the file and its Lean inputs |
| `cases NAME`, the module's cases in the host | the module's case lines after the library case map, the written file, the host, and the Wasmtime library that `ldd` finds for the host |
| `gpt`, `module cases euler`, `module cases shapes`, and `slew edges` | the driver scripts, the Lean file that they run and its Lean inputs, the written file, and the host |
| `accuracy FILE`, a native accuracy check | the file, its Lean inputs, and, for the parser and printer checks, the data file that they read |

Every check has `tests/verified/run.sh` among its inputs.  The Lean inputs of a file or module are the files that fix the dependencies, `lean-toolchain`, `lakefile.lean`, `lake-manifest.json`, and the commit and changed tracked files of each package in `.lake/packages`, and the hash of the `.olean` file, in the mode's build directory, of every module of the package that the file or module is or imports, directly or through other modules of the package.  A module's `.olean` file holds its declarations and their compiled code, so its hash changes whenever the module changes what a check can read, and a source edit that leaves the file's bytes unchanged keeps the records.  A file that a check reads at run time is an input only when the driver names it, as it names the data files of the parser and printer checks.  On an 8-CPU x86-64 host, `tests/verified/run.sh --cases conjunction` took 32 s, and a second run, which skipped every check, 10 s.  In a full run on another 8-CPU host, the checks after the build took 71 minutes: the emission 16, the file theorems 15, the host's cases 10, the accuracy checks 22, the application drivers and the axiom audits 7, and the case executables, which always run, 1.5.

### WGSL tests

`tests/wgsl/run.sh` emits the verified compiler's kernels of [the binary32 example](../Examples/Binary32/Compiled.lean), under the names `scale`, `axpyArray`, `matVec`, and `condMix`, and of [the binary32 GPT-2 compilation](../Demos/Gpt32/Verified.lean) with `tools/EmitWgsl.lean`, which checks each text with the parser.  It computes the cases of [`tests/wgsl/Cases.lean`](../tests/wgsl/Cases.lean) and `Demos/Gpt32/VerifiedGpuCasesMain.lean` with native Lean and runs every case on the SwiftShader and llvmpipe Vulkan drivers with `leanexe-webgpu-host`, comparing each output word.  `tests/wgsl/run.sh --verified` runs the kernels of [the kernel examples](../Verified/Examples/Wgsl.lean) and the binary32 example's kernels under their own names on the cases of [`WgslCasesMain.lean`](../Verified/Examples/WgslCasesMain.lean).  `tests/verified/run.sh --cases wgsl` and `tests/verified/run.sh --cases gpt32` check the Wasm results and allocations of the same functions.  With `--emit-only` the driver writes the kernels and the cases and stops, and with `--drivers-only` it runs ones already written, so that a machine without Lean can run the drivers.

`tests/gpt32/native.sh` emits the verified `gpt32.wasm` and runs small random GPT-2 models through the Lean driver of [`tests/gpt32/VerifiedNative.lean`](../tests/gpt32/VerifiedNative.lean), with the verified kernels, on that module and on both drivers.  It compares every step's scores with native Lean's `step32` bit for bit.  The driver uses the three random-model configurations of [the native cases](../Demos/Gpt32/NativeCases.lean).

### Talos conformance

[The Talos conformance driver](../tests/talos/run.sh) tests Talos, the semantics of the WebAssembly theorems, against the official WebAssembly testsuite at the revision that Talos's submodule `vendor/testsuite` records.  It builds the testsuite runner of the pinned Talos revision and runs it over the suite, and it fails if the runner records a failed command, an interpreter error, or exhausted fuel.  It then requires the runner's report, one line per command with its outcome, to equal `testsuite_report.txt` at the root of Talos, the report that Talos's continuous integration checks.  The runner converts each script with `wasm-tools json-from-wast`, so the driver requires the pinned `wasm-tools` 1.251.0.  The driver uses Lake's checkout of Talos for WasmInterpreterLean, the package of the runner, and Lake leaves its submodule uninitialized, so a first run needs `git -C .lake/packages/WasmInterpreterLean submodule update --init vendor/testsuite`.

### WASI and Linux tests

Every script but `tests/linux/sys-run.sh` builds Lean modules, and the scripts of `tests/linux/` need an AArch64 Linux host with `qemu-aarch64`, QEMU's user-mode emulator.  A script that writes an executable with theorems has Lean elaborate the theorems' module against the file that it wrote, and the kernel check it, and runs the executable on the host's processor and under `qemu-aarch64`.  A script of WASI commands compares the runs from files with the Wasmtime host's runs of the command's module, and it compares the others, such as runs from pipes, with closed streams, under QEMU without `openat2`, and at the descriptor limit, with outputs and statuses that it computes.  [The WASI manual's tests](wasi.md#tests) and the AArch64 document's [runs](a64-bare-metal.md#runs) and [WASI commands](a64-bare-metal.md#wasi-commands) give the cases and their results.

| Script | Tools beyond Lean | What it tests |
|---|---|---|
| [`tests/wasi/run.sh`](../tests/wasi/run.sh) | Without `--foundations-only`, the Wasmtime host and `wasm-tools` | Builds the WASI proofs, audits their axioms, and runs the native interpreter, handle check, poll layout, wrapper-code, and exit-model tests.  Without `--foundations-only` it also runs the byte and literal modules' cases in the Wasmtime host and the drivers of code generation, reflection, the scripted host, the Wasmtime host, acceptance, readAll, the flat call examples, and the running sums. |
| [`tests/wasi/sys-run.sh`](../tests/wasi/sys-run.sh) | The Wasmtime host, `wasm-tools`, and `uv` | Checks the call table, the typed functions, the reflection equations, and the frame test against the generator's output from the pinned witx, and the call table against an independent lowering, and runs in Wasmtime 44 the frame test of every flat call, the frame tests with seeded faults, and the rejection sweep of the enum and flags parameters. |
| [`tests/wasi/sys-example-run.sh`](../tests/wasi/sys-example-run.sh) | The Wasmtime host and `wasm-tools` | Audits the axioms of the flat call examples, checks a witness host for the flat call example's total theorem, and runs the examples natively against scripted replies and in the Wasmtime host. |
| [`tests/wasi/readall-run.sh`](../tests/wasi/readall-run.sh) | The Wasmtime host and `wasm-tools` | Audits the axioms of `readAll`'s proofs and its example, and runs the example natively and in the Wasmtime host on inputs from files and pipes around a read's capacity and the limit, with a read error and a write error. |
| [`tests/linux/sys-run.sh`](../tests/linux/sys-run.sh) | No Lean, and a C compiler, `qemu-aarch64`, `uv`, and `systemd-run` | Checks the Linux call layer's table and frame test against the generator's output from the pinned syzlang files, and the table against an independent lowering, and runs the frame test, which issues each described call against guard pages, natively and under `qemu-aarch64`, with seeded faults. |
| [`tests/linux/a64-elf.sh`](../tests/linux/a64-elf.sh) | `qemu-aarch64` and `systemd-run` | Writes `flip.elf` and `stamp.elf`, elaborates their theorems, and runs them on messages from files and pipes and on the error paths. |
| [`tests/linux/a64-wasi.sh`](../tests/linux/a64-wasi.sh) | The Wasmtime host, `qemu-aarch64`, `strace`, `uv`, and `systemd-run` | Writes `readall.elf`, `environ.elf`, `clockrandom.elf`, and `sys.elf` and elaborates their theorems, writes `args.elf`, and runs them with inputs, arguments, and environments at their edges, and runs the modules that call `args_sizes_get` and `args_get` with overlapping regions and regions at the memory's end.  It also writes `histogram.elf`, `choice.elf`, and `manifest.elf`, the demos' executables, and elaborates their theorems, and the demos' drivers run them. |
| [`tests/linux/a64-wasi-clocks.sh`](../tests/linux/a64-wasi-clocks.sh) | The Wasmtime host, `wasm-tools`, `qemu-aarch64`, `strace`, `uv`, and `systemd-run` | Runs the stubs of `clock_time_get` and `random_get` on requests at their edges, each from a module in WAT. |
| [`tests/linux/a64-wasi-preopen.sh`](../tests/linux/a64-wasi-preopen.sh) | The Wasmtime host, `wasm-tools`, `qemu-aarch64`, and `strace` | Writes `prestat.elf` and elaborates its theorems, and runs it and a module that asks about descriptor numbers up to `2^32 - 1` with descriptor 3 a directory, closed, and a file, and with faults injected into the check of descriptor 3. |
| [`tests/linux/a64-wasi-files.sh`](../tests/linux/a64-wasi-files.sh) | The Wasmtime host, `wasm-tools`, `qemu-aarch64`, `strace`, and `uv` | Writes `files.elf` and elaborates its theorems, and runs it and the scenarios of `path_open`, `fd_close`, and the handle forms, among them open flags, closes, magic links, the descriptor limit of 1,024, and faults injected into `openat2` and `close`. |

`tests/linux/a64-wasi-preopen.sh --runs DIR` and `tests/linux/a64-wasi-files.sh --runs DIR` build and check nothing and run the executables and modules that a run of the script left in `DIR`, on a host that needs neither Lean nor `wasm-tools`.  `tests/linux/sys-run.sh` takes an optional directory of syzlang files, and the other scripts of `tests/linux/` take no arguments.  The full check runs `tests/wasi/run.sh`, `tests/wasi/sys-run.sh`, and the drivers of the random histogram, the random choice, and the manifest checker, and, on an AArch64 Linux host, every script of `tests/linux/` in the table.

The demos' drivers, [`tests/random-histogram/run.sh`](../tests/random-histogram/run.sh), [`tests/random-choice/run.sh`](../tests/random-choice/run.sh), and [`tests/manifest-check/run.sh`](../tests/manifest-check/run.sh), write the demos' executables from the same modules as `a64-wasi.sh` and run each command in the Wasmtime host, on the host's processor, and under `qemu-aarch64`, which `RUNNERS` selects, with runs under `strace` on the host's processor.  The histogram's and the random choice's drivers also run their modules in the Wasmtime host with `--random-bytes` and require the output and the status that the specification gives for those bytes.  The manifest checker's driver requires QEMU 9.2 or later, which `QEMU_USER` names when the system's emulator is older.  [The histogram's guide](../Demos/RandomHistogram/README.md#building-running-and-testing), [the random choice's](../Demos/RandomChoice/README.md#building-running-and-testing), and [the manifest checker's](../Demos/ManifestCheck/README.md#building-running-and-testing) give the cases and their results.

### The full check

The full library includes the numerical proofs and can take several hours.  The lgamma root-range proofs need `--memory-high 10G`, which sets a 12 GiB memory maximum.  The [compilation example](#compiling-and-running) builds only its selected module and imports at the default limits.

[`tools/check`](../tools/check) runs the full check across the machines that a hosts file names, and writes its record to `STATUS.md` at the root, which Git ignores: the checked commit and the paths that differ from it, the dates of the commit and of the run, the toolchain, the platforms, each step's status, duration, and the counts that its drivers print, the axiom reports of the dependencies' files that name an axiom beyond `propext`, `Classical.choice`, and `Quot.sound`, the items that failed, and the checks that did not run.  It builds every module of `LeanExe`, `Examples`, `Demos`, `Verified`, `Library`, and `TestSupport` with the executables that the check's drivers run in one `lake build` on the primary machine, with as many Lake jobs as that machine's budget holds at 7 GiB a job, at log level info so that it can count the build's axiom reports, and with `LEANRUN_FAST=0`, so that no item uses a [fast build](#fast-builds).  It then copies the built tree with `rsync` to the other machines at the same path and runs the items of [the manifest](../tests/items.py), each in the tree's root on a machine with the tools it needs, as many at once as each machine's budget holds.  A machine's budget is its memory and CPUs less a reserve, less the work that the hosts file reserves, and less the limits of the other systemd scopes running there, which the scheduler reads every ten seconds.  An item counts against a machine's CPUs the processors that it used in its last recorded run, which `build/check/cpus.json` records, or else its declared CPUs, which remain its scope's quota.  Each item runs in a systemd user scope with its memory as `MemoryMax` and without swap, and its Lean commands run under `tools/leanrun` with a lock directory of their own and `LEANRUN_MEMORY_HIGH` 2G below the item's memory.  The output of each item lies in `build/check/logs/ITEM.log`, and `build/check/items.md` gives each item's machine, time, CPU time, and memory.

An item runs a driver with its own pass criterion: [the axiom walk](#axiom-checks), a part of `tests/verified/run.sh` that `--part` names, such as the emission of a group of modules, a group of file theorems, the cases of a group of modules, an axiom audit, or an accuracy check, `tests/drone/run.sh` and `tests/modules/chunks.py` on the modules that the emission writes, the native drivers, `tests/wasi/run.sh`, `tests/wasi/sys-run.sh`, the drivers of the random histogram, the random choice, and the manifest checker, the scripts of `tests/linux/`, the bare-metal drivers under TCG, `tests/baremetal/verified.sh` on a group of modules, `tests/isla/theorems.sh` or `m7-theorems.sh` on one module, the VKB check, `rocq/check.sh`, `tests/native/clight-rocq.sh`, `clightn/check.sh --mutations`, `tests/wgsl/run.sh` with and without `--verified`, `tests/gpt32/native.sh`, `tests/ptx/run.sh`, `tests/baremetal/m7-board.sh check bms` and `m7-qemu.sh bms`, which check the file theorems of the BMS step's images, [the Talos conformance driver](../tests/talos/run.sh), each check against an independent reference, `sha3-vectors` on one function, and `tools/source-layout` and `tools/check-doc-links.mjs` on the primary machine.  The steps of `STATUS.md` group the items as the serial check's steps did, so that each count means what it meant there.  An item whose dependency failed does not run, a failed build leaves every item but `tests/linux/sys-run.sh`, `rocq/check.sh`, and the Talos driver unrun, and the failure of an item stops no other item.  An item whose inputs hash as they did at its recorded pass does not run again, unless `--all` is given, and the record counts its recorded output; `--affected` selects the items of the drivers, modules, and Lean files that `tools/affected` reports for a change.  The integration check of a branch runs with `--all`.

An item runs only on a machine with its tools, and an item that no machine can run is recorded as not run: the GPU items need the SwiftShader and llvmpipe Vulkan drivers and `leanexe-webgpu-host`, `tests/ptx/run.sh` needs `ptxas` and `leanexe-cuda-host`, the Rocq items need `coqc` and a CompCert tree whose proofs are built, which `COMPCERT_TREE` names, `clightn/check.sh` one configured for AArch64, the Talos driver `wasm-tools` and the `vendor/testsuite` submodule of `.lake/packages/WasmInterpreterLean`, and the scripts of `tests/linux/` and the demos' drivers `qemu-aarch64` of QEMU 9.2 or later, which `QEMU_USER` names, with the tools that [the table of WASI and Linux tests](#wasi-and-linux-tests) names.  The items that run the tree's executables need an AArch64 Linux machine; the Isla items, the file theorems, audits, and accuracy checks of `tests/verified/run.sh`, and the SHA-2 and HMAC vector checks read only modules and written files and run on any machine with Lean, whose module files do not depend on the processor.  The hosts file can bound the memory of each item on a machine and admit there only items whose expected or recorded peak lies below a limit, which `build/check/peaks.json` records for each item.  The Isla items elaborate the committed traces and need neither Isla nor Z3.  The hosts file gives each machine's `PATH`, `CCOMP`, `CLIGHTGEN`, `CCOMP_STDLIB`, `COMPCERT_TREE`, and `QEMU_USER`.  On a host with about 12 GiB of memory, a cold numerical proof cache first needs the [separate one-worker builds](#memory-heavy-numerical-proofs).  The order book's allocation charges, `Demos/OrderBook/ProcessCharges.lean`, which the build reaches through the process theorem that `Demos.lean` imports, need more than 10 GiB at one thread: under a memory high limit of 10G the module completes below the 12 GiB maximum while the kernel throttles it, which took 201 seconds with a peak of 10.4 GiB on an 8-CPU x86-64 host, and a limit of 16G or more avoids the throttling.  The serial check that ran the steps one after another took 13 hours on an AArch64 host, of which `tests/isla/theorems.sh` took 5 hours and 15 minutes, `tests/baremetal/verified.sh` 130 minutes, the checks against independent references 138 minutes, and `tests/verified/run.sh` 73 minutes.  The first run of `tools/check`, on the v4.36.0 integration commit, ran its 189 items in 89 minutes and 26 CPU hours on two AArch64 machines, one of which joined after 23 minutes, and two x86-64 machines, within budgets of 63 and 81 GiB and 8 to 18 CPUs on the AArch64 machines and one 9 GB item at a time on the others.  The A64 Isla modules elaborate their lemmas one after another on one thread, so that the memory peak is that of one lemma, and `FloatSSme`, the longest item, took 3,908 seconds alone; the bare-metal groups, whose cases differ in cost, took 92 to 2,106 seconds.

After a change to the verified compiler or its examples, `tools/leanrun --threads 2 --memory-high 10G --timeout 12h lake build Verified Library` must finish with no `sorry` warning, and `tests/verified/run.sh`, run with `LEANRUN_THREADS=3` and `LEANRUN_MEMORY_HIGH=10G`, must pass with no failed case.  A new pure compiler fixture needs an import in [`Verified.lean`](../Verified.lean), an entry in [the module registry](../tests/verified/modules.txt), and checked cases.  Reusable algorithm compilations belong in [`Library.lean`](../Library.lean), verified application compilations belong in [`Demos/Verified.lean`](../Demos/Verified.lean), and compilations of the compiler fixtures belong in [`Examples/Verified.lean`](../Examples/Verified.lean), the last two of which `Verified` imports.  Other pure examples add cases to `Verified/Examples/Cases.lean`.  [The WASI driver](../tests/wasi/run.sh) and `tests/wasi/sys-run.sh` test the WASI compiler, and the scripts of `tests/linux/` that [WASI and Linux tests](#wasi-and-linux-tests) lists test the shim, its AArch64 binding, and the Linux call layer on an AArch64 Linux host.

## Examples

The [compiler fixtures](../Verified/Examples) compile their own definitions or import native programs from `Examples` and `Library`.  A fixture can use `verified_compile` or construct a typed source program directly, as [the tuple example](../Verified/Examples/Tuples.lean) does.  Its byte theorem states that the emitted bytes decode to the module that computes those definitions.

Reusable implementations and their compilations are in [the library](../Library/README.md), and applications are in [the demos](../Demos/README.md).  [The algorithm index](../index.md) lists the elementary and special functions, software fused multiply-add, limb arithmetic, decimal parsers and printers, and their numerical and byte theorems.  Each numerical function has a document in the directory of its implementation with the proof modules, exceptional values, and limits.  The LCG, Park–Miller, and xorshift64 families under `Library/Random/` hold native definitions in `Program.lean`, compilation in `Verified.lean`, and period and other mathematical results in separate proof modules.  [The shared orbit theory](../Library/Random/Orbit/README.md) proves facts about their iterates.

| Example | Contents |
|---|---|
| [`Poly`](../Verified/Examples/Poly.lean) | `a * b + c * c - 7`. |
| [`Mix`](../Verified/Examples/Mix.lean) | Division, remainder, the bitwise operations, and the shifts. |
| [`Signed`](../Verified/Examples/Signed.lean) | `Int64` arithmetic, division, remainder, and shifts, the signed comparisons as `Bool` values and in an `if` with word branches and one with `Int64` branches, `min`, `max`, `set!`, `push`, and `LeanExe.build` on `Array Int64`, a loop and a `repeatWhile` with `Int64` state, a tail recursion that tests an `Int64`, a structure with an `Int64` and an array of `Int64`, and literals.  [The WASI command](../Verified/Examples/WasiSigned.lean) reads and returns `Int64` values, and [the CIC filter over `Int64`](../tests/TestSupport/A64/CicSigned.lean) compiles to the module of the filter over words. |
| [`Lets`](../Verified/Examples/Lets.lean) | Four `let` bindings, the last of them inside an operand of `+`, with a division in its body. |
| [`Select`](../Verified/Examples/Select.lean) | `Bool` bindings, `if` on a `Bool` and on `<`, `>`, and `≠`, a `Bool` parameter, and a `Bool` result. |
| [`Pairs`](../Verified/Examples/Pairs.lean) | Pairs as parameters and results, `.1`, `.2`, and `match` on a pair, a pair inside a pair, calls that pass and return pairs, and patterns that destructure nested pairs on the left and on the right, skip a component, bind a whole pair, destructure a pair built in place, and destructure a triple that holds arrays. |
| [Packed byte values](../Verified/Examples/Bytes.lean) | Identity, duplication, selection, cleanup, swapped results, empty buffers, UInt64 lengths, byte indexing, and construction with captured buffers and nested builders.  [The WASI driver](../tests/wasi/run.sh) checks empty inputs, out-of-bounds reads, allocation and release counts, and oversized construction. |
| [Byte updates](../Verified/Examples/BytesSet.lean) | `Bytes.set` on an owned buffer, twice in a row, in a loop whose state is the buffer, on a buffer that the function reads again after the update, and on the empty buffer.  [The WASI driver](../tests/wasi/run.sh) and [the native byte driver](../tests/native/bytes.sh) run the cases of `tests/wasi/bytes-set.tsv`, which count one allocation, the host's argument block, for an update in place, and two for `setKept`, whose update copies the buffer. |
| [Byte literals](../Verified/Examples/Literals.lean) | Static-pool deduplication, fresh owned copies, empty and conditional literals, ordinary and recursive helpers, and literals inside loop, build, fold, and tree-match bodies. |
| [Array literals and conditions](../Verified/Examples/Forms.lean) | Literals of words, floats, and `Bool`s, a literal as a loop's state, and conjunctions and disjunctions of comparisons in conditions, decisions, the elements of a build, and the conditions of two tail recursions, which [the section on these forms](#array-literals-and-conditions-on-propositions) describes. |
| [Structure patterns](../Verified/Examples/Patterns.lean) | Matches on structures whose patterns fix one field or two to enumeration constructors, fix different fields in different alternatives, fix every field, bind the value, or cover every constructor, on parameters, a structure built in place, a call, a loop's state, and a record that holds an array, which [the section on structure patterns](#structure-patterns) describes, and a pattern that fixes a `Bool` field and a match on word literals, whose rejection messages the example checks. |
| [WASI stdin and stdout](../Verified/Examples/WasiStdio.lean) | `copySome` and closed main of the WASI manual, compiled in callable and command forms.  One read and one write expose errno handling and short-transfer limits. |
| [WASI reflection](../Verified/Wasi/ReflectCommandCases.lean) | Public source-to-export declarations with hidden tables, literals, owned and borrowed bytes, records, computed call arguments, and command main. |
| [Flat WASI calls](../Verified/Examples/WasiSys.lean) | A command that writes its arguments, their count and size, readings of the realtime and monotonic clocks, and 16 random bytes, with [a total theorem](../Verified/Examples/WasiSysTotal.lean) for every host whose `args_sizes_get` replies ask for blocks of at most 4,294,897,328 bytes.  [The input example](../Verified/Examples/WasiSysInputs.lean) creates and removes a directory, [the record example](../Verified/Examples/WasiSysRecords.lean) writes the records of the preopened directory and of a file that it opens with `withOpen`, [the environment example](../Verified/Examples/WasiSysEnviron.lean) writes its environment, [the nested example](../Verified/Examples/WasiSysNested.lean) writes and reads a file with `fdWrite`, `fdPwrite`, `fdPread`, and `fdRead` and polls the clock and the file, and [the prestat example](../Verified/Examples/WasiSysPrestat.lean) copies the preopened directory's name through a file. |
| [readAll](../Verified/Examples/WasiReadAll.lean) | A command that copies its standard input to its standard output through `readAll 1000000` and returns 1 when the input exceeds the limit, with the footprint under the shim, the message corollary, the corollary for the class `Steady`, and the executable `readall.elf`. |
| [Commands of the Linux executables](../Verified/Examples/WasiFiles.lean) | The files command of [`verified_compile_wasi`](#verified_compile_wasi), [the clock and random command](../Verified/Examples/WasiClockRandom.lean), which reads three clocks and fills buffers of 16 and 5,000 bytes, and [the prestat command](../Verified/Examples/WasiPrestat.lean), which writes what the host answers about the preopened directory, each with its footprint at the native memory cap and its executable, `files.elf`, `clockrandom.elf`, or `prestat.elf`. |
| [`Calls`](../Verified/Examples/Calls.lean) | `sq`, `sumSq`, `small`, and `pick`, in which `sumSq` calls `sq` and `pick` calls the others, with a call as an argument of a call and a `Bool`-valued call as the test of an `if`. |
| [Frontend forms](../Verified/Examples/Frontend.lean) | Nested `@[inline]` helpers and `abbrev`s, helper calls in loops and array expressions, listed inline callees, direct array methods, `insertIdx!` with its empty result past the end, empty arrays of words, floats, and records, including a record without an `Inhabited` instance, and Boolean equality, decisions, and conditions with record results, record-array results, and operand calls that consume arrays. |
| [Array folds](../Verified/Examples/Fold.lean) | Words, floats, record elements without an `Inhabited` instance, owned array and pair accumulators, a borrowed initial-state alias, nested folds, calls inside a fold, and the frames condition of a recursive call.  `words_bound` proves the word fold's allocation bound is zero. |
| [Lists of words](../Verified/Examples/Lists.lean) | Construction, identity, duplication, nested calls, matching, head and tail access, reconstruction, and head updates.  Allocation counts check last-use header reuse. |
| [Guarded list recursion](../Verified/Examples/ListRecursion.lean) | Summation, recursive increment with header reuse, and the depth boundary. |
| [List loops](../Verified/Examples/ListLoops.lean) | Construction and extension of list state in word-counted loops. |
| [List tail recursion](../Verified/Examples/ListTail.lean) | Borrowed summation and consumed reversal with header reuse, including chains beyond the guarded call-depth limit. |
| [User-defined recursive values](../Verified/Examples/RecursiveTypes.lean) | Construction, matching, identity, duplication, subtree release, guarded size and increment with header reuse, loop state, tail summation and reversal, and owned right-spine traversal over the `Words` and `KeyTree` types, whose conversions and encoding proofs [the `Words` derivation](../Examples/Words/Reflected.lean) and [the `KeyTree` derivation](../Library/Trees/WordTree/Reflected.lean) give. |
| [Tagged recursive values](../Verified/Examples/TaggedTypes.lean) | Type `Term` with a null constructor and four tagged record constructors: construction, duplication with a copy, matching, guarded evaluation and size, header reuse, subtree release, and tail recursion. |
| [Tail loops](../Verified/Examples/Tail.lean) | Word accumulation, scalar pairs, record arrays, owned growth, swapped and replaced array parameters, aliases, calls between tail functions, and a guarded callee. |
| [Tail conditions and borrowed states](../Verified/Examples/TailConditions.lean) | Boolean and inequality conditions, a proof-named conditional, tuple destructuring, and borrowed pair and record parameters. |
| [Binary64 GPT-2](../Demos/Gpt/Verified.lean) | Unchanged functions of [the GPT example](../Demos/Gpt/README.md), including full-sequence inference, cached steps, and sampling.  The compiler derives each function's execution, allocation-bound, and trap-free theorems and the module's bytes theorem. |
| [Binary32 GPT-2](../Demos/Gpt32/README.md#verified-compiler) | Unchanged kernel functions, with generated Wasm execution and byte theorems, proved WGSL lowering, native dispatch theorems, and the application's host-generation proof instantiated with these kernels. |
| [Euler solvers](../Demos/Euler/Verified.lean) | Functions of [the Euler example](../Demos/Euler/README.md), with buffered solvers that keep three grids in their loops under the names `solve` and `reconstructedSolve`, and that `solve_eq` and `reconstructedSolve_eq` equate with the example's solvers.  `euler_solve_call` states both calls from the store in which the module starts with a memory cap of at least `solvePages n` pages, which `solvePages_le` bounds by 1,563 for every grid. |
| [`Loops`](../Verified/Examples/Loops.lean) | Loops over a word, over a pair, and over a pair with a `Bool`, a loop inside a loop, a loop whose body branches, and a loop whose body calls an earlier definition. |
| [`Arrays`](../Verified/Examples/Arrays.lean) | Sums, a dot product, a count, and a search over arrays in loops, reads at computed positions, a pair of arrays passed to calls, and an array chosen by an `if` and bound with `let`. |
| [`Owned`](../Verified/Examples/Owned.lean) | Array results, copies of parameters, owned call results that a reader, a call, a branch, or an unused binding releases, a moved result, a loop whose state is an owned array, a pair of owned arrays destructured, and arrays built with `LeanExe.build`, one whose element builds and releases an array of its own and one whose element reads an owned array that the code releases after the build. |
| [`Updates`](../Verified/Examples/Updates.lean) | Updates of a parameter, of a built array, of a loop's state, two updates in a row, and an update of an array that stays live. |
| [`Grow`](../Verified/Examples/Grow.lean) | `push` and `++` on parameters, built arrays, and loop states, onto an array that stays live, an array appended to itself, and an owned right operand. |
| [`Modes`](../Verified/Examples/Modes.lean) | Parameters that a function returns, updates, or moves into an owned parameter, also from a loop's state and before a later argument reads the array, parameters that stay borrowed because the body uses them again, and owned tuple parameters: `swapPair` returns the components of its pair, and the loop of `parse` moves its state, a word, a flag, and an array, into `parseStep`, which extends the array in place.  Its `byHand`, written without the reflector, has an owned parameter that the body never reads and one that it reads last. |
| [`Floats`](../Verified/Examples/Floats.lean) | Piecewise function, scaled hypotenuse, float comparisons as conditions and as `Bool` values, `min`, `max`, negation, loop over a pair of floats, function with a word, a float, an array, and a pair as parameters and a pair result with a float, call of float functions, conversions between words and floats, power of two built from its exponent field, and literal NaN patterns. |
| [Binary32 operations](../Verified/Examples/Floats32.lean) | Arithmetic, comparisons, conditional branches, square root, signs, nearest, unsigned and signed word conversions, bit-pattern conversions, mixed f32/f64 parameters and results, arrays, updates, folds, builds, and tail loops.  Guarded recursion includes a proved 32-position mixed-format frame. |
| [Sums with fields](../Verified/Examples/Sums.lean) | The `Shape` program of `Examples.Shape`, matches and wildcard bindings, constructors, calls, arrays, updates, folds, loop state, and mixed Float32 and enumeration fields. |
| [Sums with heap fields](../Verified/Examples/HeapSums.lean) | Sum with `Bytes`, array, tree, word, and float fields and sum with a list field: construction from owned arguments, borrowed and owned matches, wildcards that name the matched value, results, pairs, loop state, and guarded call inside a match. |
| [Trees with buffer fields](../Verified/Examples/BufferTrees.lean) | Tree whose records hold a byte buffer in addition to a word and two children: construction from owned and borrowed buffers and from the empty buffer, owned matches that move the buffers out and release those that are not used, borrowed reads of a buffer's bytes and size, and copies of a borrowed tree that copy each record's buffer. |
| [Trees with array fields](../Verified/Examples/ArrayTrees.lean) | Tree whose records hold an array of words in addition to a word and two children: construction from owned and borrowed arrays, owned matches that move the arrays out and release those that are not used, borrowed reads of the arrays' elements, record reuse, and copies of a borrowed tree that copy each record's array. |
| [Trees with typed fields](../Verified/Examples/TypedTrees.lean) | Tree with `Bool`, binary64, binary32, and word fields, tree whose records hold a structure with a nested structure, tree with an enumeration field, and tree with a sum field: construction, copies, record reuse, borrowed reads, matches on the sum, recursion, loops, and functions that take or return the fields. |
| [`Records`](../Verified/Examples/Records.lean) | Structures with a nested structure and a `Bool` field, built, updated with `{ s with … }`, read field by field, destructured with `match`, chosen with `if`, passed to calls, and used as a loop's state, with theorems stated for the structures. |
| [`Tuples`](../Verified/Examples/Tuples.lean) | Arrays of tuples of a float and a word and of a nested tuple, built, read along a path, updated in place, extended, and appended, written without the reflector, with an `example` per function stating by `rfl` that it means a Lean function. |
| [`OwnedTuples`](../Verified/Examples/OwnedTuples.lean) | A pair of an array and a word as an owned parameter, which the body splits at entry and whose array it extends in place and returns or reads last and releases, written without the reflector, with theorems that take the argument as `Moved (Array UInt64 × UInt64)`. |
| [`Grids`](../Verified/Examples/Grids.lean) | Arrays of the structures of `Records.lean`, built, read element by element and field by field, also past the end, updated in place in a loop, extended with a new structure, appended, counted, reduced to a total and a `Bool`, and returned in a pair with a total, and a local array of pairs. |
| [`Repeat`](../Verified/Examples/Repeat.lean) | `LeanExe.repeatWhile` over words, a float, pairs that hold arrays, and a structure, stopping early under fuels up to `2 ^ 64 - 1`, with a condition that reads an owned array of the state and a step that updates it in place, and loops over literal data inside a pair result, under a `match`, in a call with literal arguments, and in a closed term. |
| [`Enums`](../Verified/Examples/Enums.lean) | Enumerations flattened by `ctorIdx`, by a `match`, by a constant for the one with a single constructor, and by a `match` to the words 0 and 200, as parameters, results, a structure field, a loop state's field, and array elements, with `match` that has a wildcard binding the value, `match` on an array element, `==`, `!=`, `decide`, and `if` on enumerations, and an update in place. |
| [`Recursion`](../Verified/Examples/Recursion.lean) | Recursion once and twice per call over words, floats, a pair, a structure, an array of structures, and an owned array that each call extends and moves into the next, a function that calls two recursive ones, a recursion that returns at depth 999 and traps at depth 1,000, a recursion that calls another, and `spread`, which calls them inside a loop, a build, a `repeatWhile` condition, a destructured pair, an update, the argument of a function without the call depth, and conditions on a `Bool`, a float, and `≠`, with the theorems `chain_fits`, `chain_trapFree`, `fill_fits`, `fill_cost`, and `fill_trapFree`. |
| [`Fields`](../Verified/Examples/Fields.lean) | Records with array fields, built, read field by field and element by element, also past the end, updated in place with `{ r with … }` on an owned parameter and in a loop's state, read through a borrowed parameter, passed to a call, also as a record built in place whose tuple ends in two words, destructured with `match`, chosen with `if`, returned in a pair, and held in another record, with a `Flat` instance written as a pattern, a loop that extends a field's array, and bound equations that name the fields. |
| [`Trig`](../Library/Numerics/Float64/Trig/Program.lean) | `sin` and `cos` ported from fdlibm, with its reduction by multiples of `π/2` below `2 ^ 20 · π/2`, a Payne–Hanek reduction in word arithmetic above, after Go's `math.trigReduce`, which reads the bits of `2/π` and `π/2` from tables so that no call allocates, `sinWith` and `cosWith` with the tables as parameters and `sin` and `cos` as wrappers, with theorems that allow no trap, and fdlibm's minimax kernels, written with the constants' bit patterns. |
| [`Fourier`](../Library/Numerics/Fourier/Program.lean) | Discrete Fourier transform of a signal of interleaved complex floats by the `n²` products of the definition, its inverse, and power spectrum of real samples, with factors from `Trig.cosWith` and `Trig.sinWith`, compiled in the same program, with Trig's tables passed by the wrappers `dft`, `inverse`, `powerSpectrum`, and `twiddle`. |
| [`Exp`](../Library/Numerics/Float64/Exp/Program.lean) | `exp` ported from Arm's optimized-routines, with its table of 256 words in a data segment, `expWith` with the table as a parameter and `exp` as its wrapper, and the paths for results that overflow or underflow. |
| [`Tanh`](../Library/Numerics/Float64/Tanh/Program.lean) | `expm1` and `tanh` ported from fdlibm, with fdlibm's signed reduction count represented as a sign and a magnitude. |
| [`Log`](../Library/Numerics/Float64/Log/Program.lean) | `log` ported from Arm's optimized-routines, with two tables of 256 words in data segments and `log` as the wrapper that passes them. |
| [`Tables`](../Verified/Examples/Tables.lean) | Two tables read by wrappers, in range and past the end, and an owned array updated and extended from a table, with the theorem `pushSquare_bound` for a wrapper whose callee has a paid parameter. |
| [`Insert`](../Verified/Examples/Insert.lean) | `LeanExe.insertAt` and `LeanExe.eraseAt` on parameters, built arrays, an array that stays live, a loop's state in an insertion sort and in a removal loop, a local array of pairs, arrays of structures, and the two arrays of a book side, which a command loop passes through calls, also past the end. |
| [`OrderBook`](../Demos/OrderBook/Verified.lean) | Two-sided order book of [`Demos/OrderBook`](../Demos/OrderBook/README.md), whose `run` consumes the book's seven arrays and a stream of commands and returns the new book and the event words, and whose `top` reads a book, with the theorems `run_call` and `top_call` of [the call module](../Demos/OrderBook/VerifiedCall.lean), from `compiled.run.trapFree`, `compiled.top.trapFree`, and the refinement's `run_eq` and `top_eq`, that the module's results are those of `Spec.run` and `Spec.top`. |
| [`Drone`](../Demos/Drone/Verified.lean) | Drone planner of [`Demos/Drone`](../Demos/Drone/README.md), compiled unchanged, with its named constants reflected as their values, and the theorems `drone_compute` and `drone_safe`, from the planner's `compute_correct` and `compute_safe`, that the module's results are optimal and safe flights, and `drone_trapFree`, from `compute_bound` on `compiled.compute.bound_eq`, that the module computes `compute` without a trap whenever `top` is at least 2,251,064 bytes below the memory's cap. |
| [`Slew`](../Demos/Slew/Verified.lean) | Slew planner of [`Demos/Slew`](../Demos/Slew/README.md), which plans rest-to-rest eigenaxis rotations of a spacecraft under cone constraints through a graph of waypoint attitudes, compiled with the library's `atan` and `atan2` into one module, with the generated `implements`, `trapFree`, and bytes theorems, and [`slew_trapFree`](../Demos/Slew/Bound.lean), from `plan_bound` on `compiled.plan.bound_eq`, that the module computes `plan` without a trap whenever `top` is at least 123,464 bytes below the memory's cap. |
| [`Elements`](../Verified/Examples/Elements.lean) | Sum, dot product, and maximum over arrays of floats, grid built from converted indices, `axpy` that updates an owned array of floats in place, extension, flags of negative elements, count and selection by flags, update and push of an owned array of `Bool`s, and sieve of Eratosthenes. |
| [`Lcg`](../Library/Random/Lcg/Verified.lean), [`ParkMiller`](../Library/Random/ParkMiller/Verified.lean), [`Xorshift`](../Library/Random/Xorshift/Verified.lean) | Generators of [`Library/Random/Lcg`](../Library/Random/Lcg/README.md), [`Library/Random/ParkMiller`](../Library/Random/ParkMiller/README.md), and [`Library/Random/Xorshift`](../Library/Random/Xorshift/README.md), compiled unchanged, with the theorems `lcg_advance`, `parkMiller_advance`, and `xorshift_advance`, which combine each module's bytes with the generator's theorems about `advance`, and `lcg_jump` and `xorshift_jump`, which state that the modules' jump-ahead functions compute `advance`, the second when `top` is at least 36,920 bytes below the memory cap, by `jump_bound`. |
| [`Gcd`](../Library/Numerics/Arithmetic/Gcd/Compiled.lean), [`PrimeFactors`](../Library/Numerics/Arithmetic/PrimeFactors/Compiled.lean), [`Mean`](../Library/Numerics/Statistics/Mean/Compiled.lean), [`SumSquares`](../Library/Numerics/Statistics/SumSquares/Compiled.lean), [`SplitMix64`](../Library/Random/SplitMix64/Compiled.lean) | Library programs, with `gcd_call` and `primeFactors_call`, which compose the generated store-preserving theorems with `gcd_eq` and `compute_eq`, and `prng_module`, which combines the module's bytes with the store-preserving theorems of `splitMix` and `unitFloat`. |
| [`Lookup`](../Examples/Lookup/Compiled.lean), [`TreeLookup`](../Examples/TreeLookup/Compiled.lean), [`Increment`](../Examples/Increment/Compiled.lean), [`Below100`](../Examples/Below100/Compiled.lean), [`RemoveZero`](../Examples/RemoveZero/Compiled.lean), [`Binary32`](../Examples/Binary32/Compiled.lean) | Small examples and the binary32 example, with `lookup_call`, `treeLookup_call`, `increment_call`, `below100_call`, and `removeZero_call`, which compose the generated trap-free theorems with the examples' specification theorems through `Examples.arrayCall` of [the shared call theorem](../Examples/ArrayCall.lean), and the WGSL kernels of `scale32`, `axpyArray32`, `matVec32`, and `condMix32` with dispatch theorems. |
| [`Convert`](../Examples/Convert/README.md) | The conversions between `Int64` and the floats and a gain applied to an `Int64` through binary64, with specifications that are WebAssembly's signed conversion instructions in Talos's functions, `toDouble_call`, `toSingle_call`, `ofDouble_call`, `ofSingle_call`, and `scale_call`, the results at the special values by the kernel's evaluation, and AArch64 Images of `toDouble`, `toSingle`, `ofDouble`, and `scale` with theorems that state the specified words. |
| [`Floor`](../Examples/Floor/README.md) | `Int64` floor division, the floor of the mean, and a clamp, with `floorDiv_spec` and `average_spec` over `Int.fdiv` and `clamp_spec` over `max` and `min`, `floorDiv_call`, `average_call`, and `clamp_call`, which compose them with the generated `pure` theorems, and AArch64 Images of both functions with theorems that state the specified integers. |
| [`Scale`](../Examples/Scale/Compiled.lean), [`SumArray`](../Examples/SumArray/Compiled.lean), [`SumCount`](../Examples/SumCount/Compiled.lean), [`PairSum`](../Examples/PairSum/Compiled.lean), [`ScaledHypot`](../Examples/ScaledHypot/Compiled.lean), [`Piecewise`](../Examples/Piecewise/Compiled.lean), [`Axpy`](../Examples/Axpy/Compiled.lean), [`Bucket`](../Examples/Bucket/Compiled.lean), [`Bools`](../Examples/Bools/Compiled.lean), [`Lists`](../Examples/Lists/Compiled.lean), [`Updates`](../Examples/Updates/Compiled.lean), [`Grids`](../Examples/Grids/Compiled.lean), [`Calc`](../Examples/Calc/Compiled.lean), [`Trees`](../Examples/Trees/Compiled.lean) | Compiler fixtures whose generated theorems state that the module computes each Lean function.  `Bools`, `Grids`, and `Calc` take the `Flat` instances of their `Flat.lean`, and the registry names the modules of `Lists`, `Updates`, `Grids`, and `Trees` `exampleLists`, `exampleUpdates`, `exampleGrids`, and `exampleTrees`.  The reflector reads the structure patterns of `Calc.undo`, which fix the field `last`, as tests of its word. |

## From an English request

[The verified-request skill](../.claude/skills/verified-request/SKILL.md) instructs an agent to derive, from a request in English, a program of this compiler and a call theorem that the module's export returns, without a trap, the value of a specification reviewed against the request.  Its first stage produces the specification `expected`, its samples, and a review by a fresh agent that reads only the request, the specification, and the samples.  The agent then writes the program, `compute_eq` in a module that imports only the program, the specification, and lemmas about the dialect, and the call theorem `compute_callSpec`, which composes `compute_eq` with the generated `trapFree` theorem through `Verified.ImplementsTables.call` and `Verified.Call.spec` of [the call theorem](../Verified/Call.lean).  The skill covers parameters of `UInt64`, `Array UInt64`, or tuples of these, and results of `UInt64` or `Array UInt64`, which `Verified.CallSpec` covers through `Represent`.

[`tools/verified-request-check`](../tools/verified-request-check) accepts or rejects the result.  `--spec NAME` prints each sample with the specification's output, `--freeze NAME` records the hashes of the reviewed `Spec.lean` and `Samples.lean`, and `--run NAME` emits `compiled.module` with [the module emitter](../tools/Emit.lean) and runs the samples in Wasmtime without proofs.  Both `--run` and the check first reject a run whose Lean files declare a global or scoped instance, notation, macro, syntax, or elaborator, or code that runs at import, since the check elaborates its statement with the run's modules imported, and each rejection names the file and line.  Without a flag, it checks the hashes of the reviewed specification and samples, writes the statement `Verified.CallSpec compiled.module compiled.tables K expected compiled.compute.bound` for the export's index `K`, and requires `compute_callSpec` to prove it with no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.  It proves in the kernel that the export is function `K`, emits `build/verified-request/NAME/NAME.wasm`, and runs the samples in Wasmtime against `expected`.  When `ccomp` and `clightgen` are found, it also builds the module's translation to C with `native-verified build`, as [the native driver](../tests/native/verified.sh) does, and runs the samples in the native program.

## Development practice

### `tools/leanrun` and the shared lock

Every `lean` and `lake` command runs through [`tools/leanrun`](../tools/leanrun), as [the repository instructions](../AGENTS.md) require.  The runner limits memory and CPU time through a systemd user scope, sets `LEAN_NUM_THREADS`, and holds a lock in the directory that `LEANRUN_LOCKDIR` names, by default one for each user of the machine, so that one runner command runs at a time and other sessions wait for the lock.  `--timeout` sets the command's limit and `--lock-timeout` the seconds to wait for the lock, 900 by default.

`--threads N`, 1 by default, sets `LEAN_NUM_THREADS=N`.  Lake takes its number of parallel build jobs from `LEAN_NUM_THREADS`, and each Lean process it starts uses the same value for its own tasks, so parallel jobs share the scope's memory limit.  `--cpus N` sets a CPU quota of `N` CPUs, and `--cpus auto` uses every online CPU.  Without `--cpus` the quota equals the thread count, and without `--threads` the thread count equals the `--cpus` count.  `LEANRUN_THREADS` and `LEANRUN_CPUS` supply these settings to repository drivers without wrapping them in another runner.

The runner's command runs in a transient scope of its own, which `systemd-run --scope` names `run-ID.scope` and which holds the lock's descriptor.  A service or a shell that started the runner does not contain that scope, so `systemctl --user stop` of the service ends the service's processes and leaves the scope running with the lock held, and the next runner command with the same lock directory waits until the scope's command ends or reaches its `--timeout`, and fails when that takes longer than its own `--lock-timeout`.  A stop of such a job therefore also stops the scope that `/proc/PID/cgroup` of its `lake` or `lean` process names, with `systemctl --user stop run-ID.scope`.

`--log FILE` writes standard output and standard error to a file and preserves the command's exit status.  Passing the path as an argument keeps `tools/leanrun` as the first command token, so saved runner permissions cover later targets and logs.  The default memory limits are 4 GiB high and 6 GiB maximum, and `--memory-high SIZE`, in whole gibibytes such as `10G`, selects the high limit and a maximum 2 GiB above it.

```sh
tools/leanrun --timeout 30m --lock-timeout 1200 lake env lean FILE
```

After a target reaches its timeout without a diagnostic, [the repository instructions](../AGENTS.md) require dividing it, or adding a reusable lemma that reduces its elaboration, before running it again.  `LEANRUN_LOCAL=1` runs without the cgroup limits and only with the user's explicit authorization.  [`tools/leanrun-dev`](../tools/leanrun-dev) runs Lean on the remote machine that `LEANRUN_DEV_HOST` names, with the modes `sync`, `check`, or a command.

`lake env lean FILE` loads the existing build of each import without rebuilding it, so a check of a file whose imports changed must follow `lake build` of those imports.  `lake build` of a target rebuilds the imports whose sources changed.  A check can pass against the stale builds of modules whose sources were renamed, until it imports the old and the new module together.

### Fast builds

A fast build serves development only.  `tools/leanrun --timeout 1h lake -K fast=true build TARGET` builds the modules of this package with the Lean option `debug.skipKernelTC`, which makes `addDecl` add each declaration without the kernel's type check, and writes their outputs to `.lake/build-fast` in place of `.lake/build`.  [The Lake configuration](../lakefile.lean) reads the option with `get_config? fast` and sets the package's `buildDir` and `leanOptions` from it.  Lake puts a module's options in its trace, so the fast and the checked build of a module differ in trace as well as in directory, neither replaces nor reuses the other's outputs, and a change of mode rebuilds nothing that the other mode built.  The dependencies keep their checked builds, since the `-K` options reach only the root package.

Lake elaborates the configuration file once and keeps the result in `.lake/config` until `-R` elaborates it again, and it keeps the `-K` options of the last elaboration even after the file changes.  Run directly, a `-K fast=true` without `-R` has no effect on a configured checkout, and after `lake -R -K fast=true` every `lake` command of the checkout, `lake env` included, uses the fast build until `lake -R` without the option.  [`tools/leanrun`](../tools/leanrun) reads the options of the cached configuration, which Lake records in `.lake/config/0/lakefile.olean.trace`, and adds `-R` to a lake command whose options differ, or when it cannot read them, so through the runner a lake command builds checked unless it passes `-K fast=true`.  `LEANRUN_FAST=1` makes the runner add that option to every lake command, and `tests/verified/run.sh --fast` sets it for itself and the drivers it calls, while `tools/check` sets it to 0.  A change of mode costs one elaboration of the configurations of the package and its dependencies, about 5 s, and a command in the cached mode costs nothing more.

A fast build parses and elaborates every module.  The elaborator unifies each term with its expected type, runs every tactic, evaluates `decide` without `+kernel` by its own reduction, and runs each file's commands, such as `#print axioms`, `#guard`, and `#eval`, and elaboration code that calls the kernel's reduction, as the reflector calls `Kernel.whnf`, still runs it.  The compiled code of a definition does not depend on the option, so native executables, `lean --run`, and the emitted modules give the results of a checked build, and the axiom audits, cases, and accuracy checks of `tests/verified/run.sh --fast` test the same declarations and code.  The kernel checks no declaration of the package, so a proof term that a tactic or metaprogram builds wrongly, a definitional equality that only the kernel decides, a false `decide +kernel` goal, and a declaration beyond the kernel's limits on depth and time all pass.  With the option, `theorem bad : 10 + 10 = 21 := by decide +kernel` elaborates, and `#print axioms bad` reports no axiom, so an axiom report reveals `sorry` and added axioms but not a skipped check.  The byte theorems of `verified_compile` rest on `decide +kernel` and on theorems that the reflector adds with `addDecl`, and the file theorems on `decide +kernel`, so a fast build establishes none of them, and `--fast` does not run the file checks.  A checked build of the same target establishes them, and [the repository instructions](../AGENTS.md#builds-and-checks) list the checked builds and checks that a merge requires.

On an 8-CPU x86-64 host, with two threads and a memory high limit of 8 GiB, the checked build of `Demos.Conjunction.Verified` took 627 s and its fast build 49 s, and after a change of `Demos/Conjunction/Program.lean` the rebuild of that target through the runner took 637 s checked and 60 s fast.  The fast build of that module and of every module of the package that it imports took 1,400 s from an empty `.lake/build-fast`.  Their build times summed to 2,473 s, against 3,673 s for the median checked build times of the same modules on a second host of the same speed, and without `Demos.Conjunction.Verified` the sums are 2,424 s and 3,012 s, so the kernel's share is largest in the compiled programs.  A checked build of the same target afterward took 7 s, rebuilt nothing, and changed no file of `.lake/build`.

### Kernel time of declarations

A checked build reports each module's time, and two tools name the declarations behind it.  Lean's profiler, `-Dtrace.profiler=true -Dtrace.profiler.threshold=100` on a `lake env lean FILE` run, prints each kernel check over 100 ms with the declaration's name, from the trace node of class `Kernel` that `Lean/AddDecl.lean` opens around it.  [`tools/DeclStats.lean`](../tools/DeclStats.lean) works on a built module: `check MODULE all` adds each theorem and definition of MODULE again under a fresh name and prints the kernel's time for it with the constants that the kernel unfolded most often, `stats MODULE` prints the size of each declaration's type and value, and `diff MODULE NAME` shows where the inferred type of a declaration's value and its stated type first differ.  The unfold counts of `check` name the constants that a check unfolds most often, such as those of a program's byte literals or of its functions' signatures, and [the VKB entry on comparisons that make the kernel evaluate](../VKB/entries/kernel-evaluation-costs/README.md) gives the comparisons that cause such evaluations.  Run it as `tools/leanrun --timeout 1h lake env lean --run tools/DeclStats.lean check MODULE all` after a checked build of MODULE.

### Memory-heavy numerical proofs

Some gamma and lgamma range checks need several gibibytes each.  On a host with about 12 GiB of memory, a cold numerical proof cache uses the following one-worker builds before the two-worker aggregate of [the full check](#the-full-check).  Each target has a separate invocation, which bounds the working set to one memory-intensive proof and its imports, and the aggregate reuses the accepted results.

```sh
tools/leanrun --cpus auto --threads 1 --memory-high 10G --timeout 12h lake build MODULE
```

`MODULE` takes each of these values, in order:

1. `Library.Numerics.Float64.Tgamma.TgammaAccRangeC`
2. `Library.Numerics.Float64.Lgamma.LgammaRootF`
3. `Library.Numerics.Float64.Lgamma.LgammaRootE`
4. `Library.Numerics.Float64.Lgamma.LgammaRootD2`
5. `Library.Numerics.Float64.Lgamma.LgammaRootD1`
6. `Library.Numerics.Float64.Lgamma.LgammaRootD0`
7. `Library.Numerics.Float64.Lgamma.LgammaRootC`
8. `Library.Numerics.Float64.Lgamma.LgammaRootB2`
9. `Library.Numerics.Float64.Lgamma.LgammaRootB1`
10. `Library.Numerics.Float64.Lgamma.LgammaRootB0`
11. `Library.Numerics.Float64.Lgamma.LgammaRootA2`
12. `Library.Numerics.Float64.Lgamma.LgammaRootA1`
13. `Library.Numerics.Float64.Lgamma.LgammaRootA0`

The 12-hour limit allows for cold imports.  The measured leaf checks used 30-minute limits after their common imports had been built.  `TgammaAccRangeC` took 443 seconds with a sampled peak of 7.88 GiB, and the twelve lgamma checks took 138 to 490 seconds each with at most 6.98 GiB sampled.

### Repository rules and iterative development

[The repository instructions](../AGENTS.md) set the procedures that agents in this repository must follow: the runner and its limits, the approval boundaries for repository drivers, the required checks and the review of a proof iteration, and the proposal of VKB entries after a proof task.  [The style guide](../CLAUDE.md) sets the style of prose, comments, and commit messages.  Python tools declare their dependencies as PEP 723 metadata and run with `uv run`.  [The design document](design.md) gives the design, the decisions with their reasons, what is proved and tested, and the open work.  One of its decisions makes development iterative: each iteration compiles one program from Lean source to bytes, with a proved `Implements`, a Wasmtime comparison with native Lean, an axiom audit, and a commit, adding only what that program needs.

### Documentation links

Every Markdown document and prose README has a path of links from [LeanExe](../README.md).  Link text names the destination's subject, and the surrounding sentence explains the reason for the reference.  Current repository references use relative paths.  A historical reference includes the revision to which its claims apply in its link's URL, and no commit hash of this repository appears in the text.  Links to documentation lead to a file or a directory with a README, and links to source directories support code browsing.

A `References` or `Internal References` section lists the sources whose content a document uses, and an internal document appears there only when the text does not link it at the point of use.  Each item is a citation or a link titled with the destination's title and, for a section, its heading, and items contain no sentences.  One paragraph after the list may discuss the references when the body does not state that information: what was read or checked, peer-review status, the license of ported code, or a difference between a source and the implementation.  A directory README explains how its files work together, the assumptions they share, or how to build, test, or use them.

[The documentation checker](../tools/check-doc-links.mjs) checks local targets, heading anchors, and reachability from the root README.  It reads Git's tracked and unignored untracked files, so that drafts can be checked before staging, and [the documentation tests](../tests/README.md#documentation-tests) exercise its parsing and traversal on temporary files.  [The style guide](../CLAUDE.md#review-process) requires at least two passes of its review over a document: openings and puffery, filler words, passive constructions and weak verbs, jargon, redundancy and vague references, and grammar.
