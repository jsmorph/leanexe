# Verified Compiler Manual

This manual describes the verified compiler's pure dialect, the `verified_compile` command and its generated theorems, allocation and depth bounds, the Wasmtime and WebGPU hosts, tests, examples, and the runner `tools/leanrun`.  [The WASI manual](wasi.md) describes the separate `verified_compile_wasi` command for native Lean actions with stdin, stdout, stderr, and exit.  [The LeanExe compiler manual](leanexe-manual.md) describes the other compiler, and [the README](../README.md) compares the two.  [The verified compiler's internals](../Verified/README.md) describe its code scheme and the structure of its proof, and [the design document](design.md) gives the decisions and the open work.

## Compiler, theorems, and trusted base

### One theorem for every program

The verified compiler is a Lean function, `compileWith` in [`Verified/Compile.lean`](../Verified/Compile.lean), from a typed source language to a module of Talos, the WebAssembly interpreter written in Lean.  [Program correctness with a static pool](../Verified/Correct.lean), `Prog.correctStaticWith`, states that every source program computes its meaning when the supplied static pool covers its literals.  `Prog.correctWith` specializes the theorem to a program with no nonempty byte literals, and `Prog.correct` does so without tables.  The command `verified_compile p := [f, g, …]` reads ordinary Lean definitions, writes each as a source function, and proves with kernel-checked equations that each source function means its definition.  It then states, for each definition `f`, that the module computes `f` with Lean's own types, and that the module's bytes decode to the module.  The reflector that writes the source functions is meta code and is not trusted: a wrong reflection makes an equation fail in the kernel and cannot produce a false theorem.

`Verified.WGSL.compile` also translates supported typed array builds to WGSL and returns a kernel
with proofs of its translation and local layout.  [The WGSL section](#wgsl-kernels) describes
that subset and its dispatch theorem.

### The `implements` and `trapFree` theorems

For a program with an empty byte-literal pool, `p.f.implements` states `ImplementsA aborts p.module k f` ([`LeanExe/Pipeline/Implements.lean`](../LeanExe/Pipeline/Implements.lean)), where `k` is the index of `f`'s function or entry in the module.  From any heap and store with the allocator invariant, a memory cap of at most 65,535 pages, and arguments that represent `x`, whose moved blocks lie apart from one another and from the memory that the call reads, a run returns words that represent `f x` and that the caller owns.  The run keeps the allocator invariant and the cap, keeps every region of the caller's heap that lies apart from the moved blocks, and places the result apart from those regions.  When `aborts` is true, a run may instead trap at `unreachable`, which the code does only when an allocation finds no memory, an array would hold `2^29` words or more, a byte builder requests at least `2^32` bytes, or a recursion reaches depth 1,000.  `aborts` is true when the function's result holds arrays, a parameter is owned, the body builds, updates, extends, inserts into, or removes from an array, or the body calls a function whose `aborts` is true, whose code takes the call depth, whose result holds arrays, or which owns a parameter.  Byte construction and literals, and list construction and matching, also enable `aborts`.  The compiler uses this flag conservatively.  A generated `trapFree` theorem excludes a trap under its allocation bound and frames condition.

With an empty byte-literal pool, `p.f.trapFree` states `ImplementsA false` for each source function, and `ImplementsTables false` for a wrapper whose callee takes no call depth: the call returns `f x` without a trap and raises `top` by at most the function's allocation bound.  When `aborts` is true, the theorem requires a store in which `top` can rise by the bound within the memory cap.  For a function whose code takes the call depth, it also requires a frames condition, which states that every call of the run to a function of this kind happens below depth 1,000.  The reflector also states the bound and the frames condition as Lean terms in the function's parameters, so a concrete bound follows by rewriting, as [Bounds](#bounds-and-total-execution) describes.

A program with nonempty byte literals uses [the static call specification](../Verified/StaticImplements.lean), `ImplementsStatic p.literalPool aborts p.module k f tables Pre Post`.  `tables` is empty for a source function and contains the borrowed tables for a wrapper.  The specification adds `p.literalPool.Input heap store words x` as a separate premise on the machine argument words.  [The static input predicate](../Verified/Bytes/StaticInput.lean) requires the pool's bytes and heap region to be present and the blocks consumed by the call, `Represent.moves store words x`, to lie apart from that region.  The argument representation, table, heap-preservation, and result-ownership requirements remain the same.  `p.f.trapFree` uses `ImplementsStatic` with `aborts = false`, requires room for its allocation bound, and adds the frames condition for guarded calls.  Wrappers in these programs also receive this theorem, with the allowance stated by `Wrapper.bound`.  [The static program rules](../Verified/ProgramStatic.lean) state these preconditions and postconditions.

For scalar arguments and results in a program with an empty byte-literal pool, `p.f.pure` states `ImplementsPureA aborts`: every sufficiently
fueled call returns the Lean result and preserves the whole store, or takes the permitted trap.
It starts from any store.  The command generates this theorem when its instruction rules prove
store-independent execution.  Those rules cover scalar arithmetic and conversions, local
variables, branches, loops, and calls to earlier functions with generated store-preservation
proofs.  Heap operations and guarded self-calls fall outside this proof generator.  The
[scalar composition example](../Verified/Examples/ScalarComposition.lean) contains generated
theorems for both float widths, word division, tail recursion, and call chains.

### Trusted base

[The trusted-base document](trusted-base.md#v-webassembly-modules-of-the-verified-compiler) gathers the trusted components of every artifact, with the check and the source of each.  The trusted base is that of the LeanExe compiler: Lean's kernel with the axioms `propext`, `Classical.choice`, and `Quot.sound`, Talos's semantics, the binary decoder, and the step from a constant to a file that [the module emitter](../tools/Emit.lean) performs.  [The LeanExe compiler manual](leanexe-manual.md#trusted-base) describes each part.  The statements of the verified compiler add definitions of their own: `Heap.Within` in [the runtime facts](../Verified/RuntimeFacts.lean), which states that `top` plus a bound fits within the memory cap, the allocation bound of [the bound definitions](../Verified/Bound.lean), `ImplementsTables` for wrappers, and `initialHeap` and `tableAddr`, which `p.initial` uses.  The kernel checks the reflected equations, bound equations, and compiler proofs.

A statement's meaning comes from the definitions that it reaches.  In `LeanExe/Pipeline/` these are `Implements`, `ImplementsA`, and `Satisfies`, with `Separate`, `Apart`, and `Moved`; the class `Represent` and its instances, among them those of [the byte representation](../LeanExe/Pipeline/Bytes.lean) and [the flat records](../LeanExe/Pipeline/FlatRecords.lean); `Encode` and `EncodeWellFormed`; `Node` with `NodeOwned`, `NodeBorrowed`, and the record and slot predicates that they use, in [the `Implements` definitions](../LeanExe/Pipeline/Implements.lean); and the `Heap` predicates of [the runtime model](../LeanExe/Pipeline/Runtime.lean).  These definitions use four groups of definitions in other directories: `UInt64Array.At` in [the array lemmas](../LeanExe/ProofKit/Array.lean), which fixes the layout of every array; `FreeNode`, `freeHead`, `FreeNode.region`, and `FreeListAt` in [the free list](../LeanExe/Runtime/FreeList.lean); `regionsDisjoint` in [the model of release trees](../LeanExe/Runtime/Tree.lean); and `LeanExe.Bytes` in [the byte dialect](../LeanExe/Dialect/Bytes.lean).  The verified compiler's statements add `Heap.Within`, the allocation bound, `ImplementsTables`, `initialHeap`, and `tableAddr`, which the paragraph above names.  A statement over a type with an `Encode` or `Flat` instance also uses that instance, which a reader finds beside the type unless the `Implements` definitions give it, as they give `Encode (List UInt64)` and `Flat Bool UInt64`.  The namespace `LeanExe.Pipeline` does not mark trust: modules in other directories, such as [the release proof](../LeanExe/ProofKit/ReleaseTree.lean), declare names in it, and the files under `LeanExe/Pipeline/` also hold lemmas.  A lemma, in any directory, can only make a proof fail and never changes what a statement says.

The native theorems add the statements of the translation to C.  `p.f.native` states `NativeImpl`, built on `NativeA`, both of [the native theorems](../LeanExe/Native/Proof/Native.lean), or `NativeTablesImpl` on `NativeTablesA` or `NativeStaticImpl` on `NativeStaticA`, all four of [the native wrappers](../Verified/Native.lean), and `p.f.nativeAligned` states `NativeAlignedImpl` on `NativeAlignedA` of [the aligned native step](../LeanExe/Native/Proof/AlignedNative.lean) or `NativeTablesAlignedImpl` on `NativeTablesAlignedA` of [the aligned wrappers](../Verified/AlignedNative.lean), with `AlignedInput` and `AlignedOutput` of [the alignment predicates](../LeanExe/Pipeline/AlignedImplements.lean) and `Heap.Aligned` of [the aligned heap](../LeanExe/Pipeline/AlignedHeap.lean).  `NativeAlignedA` differs from `NativeA`, and `NativeTablesAlignedA` from `NativeTablesA`, by exactly the premise `AlignedInput` and, after a return, the conclusions `heap'.Aligned` and `AlignedOutput`.  `NativeAlignedImpl` and `NativeTablesAlignedImpl` take the theorem of `ImplementsA` or `ImplementsTables`, as `NativeImpl` and `NativeTablesImpl` do, and differ from them only in the statement that they name.  These reach `Env`, `StoreRel`, and `StatusRel` of [the relation](../LeanExe/Native/Proof/Relation.lean), `EnvOk` of [the straight-line proofs](../LeanExe/Native/Proof/Straight.lean), `ArgsTyped`, `argVals`, and `ResultRel` of [the call proofs](../LeanExe/Native/Proof/Calls.lean), `translate`, `Translation`, `funId`, `signatureOf`, `trapUnreachable`, and `nativeCap` of [the translator](../LeanExe/Native/Translate.lean), and `eval_funcall` and `bigstep_program_terminates` of [the big-step semantics](../LeanExe/Native/Clight/Bigstep.lean), with the rest of the Lean copy of Clight in [`LeanExe/Native/Clight/`](../LeanExe/Native/Clight).

The bare-metal statements add a whole program to the native ones.  The theorem `p.f.program` that `bare_program` of [the bare-metal command](../Verified/Bare.lean) proves reaches `bareProgram` of [the whole program](../LeanExe/Native/Proof/Whole.lean), `bareMain`, `OutKind`, `encodeWord`, `encodeArray`, and `outTrace` of [the generated `main`](../LeanExe/Native/Bare.lean), `PrefixOk` of [the bare-metal proof](../LeanExe/Native/Proof/Main.lean), and `E0` of [the events](../LeanExe/Native/Clight/Events.lean).  `sha256_input` reaches `inProgram` of the whole program, `inMain`, `inMax`, and `inTooLong` of the generated `main`, `Reads`, `InResult`, `inTrace`, `inLen`, and `inMsgByte` of [the input program](../LeanExe/Native/Proof/Input.lean), and `shaOut` and `message` of [the test's theorem](../tests/TestSupport/Bare/Input.lean), whose output is `SHS.SHA256.Impl.sha256` of [the SHA-256 implementation](../Library/Hashing/Sha2/Impl/SHA256.lean).  `InResult` also allows a run that ends with the code of `unreachable` and no output when `alloc` traps.  [The Rocq composition](../rocq/Clight2Asm.v) carries such a termination to the Asm program, and its theorems state that step in CompCert's own Coq definitions of Clight and Asm.

Every statement about a value of a recursive type uses its representation in [the `Implements` definitions](../LeanExe/Pipeline/Implements.lean): the null pointer, or a record whose header holds a mask of the slots that hold pointers.  A slot holds a word, a pointer to a child record, a pointer to an array object (`Slot.array`), or the root of a byte buffer (`Slot.bytes`).  The field `lengths` of `RecordHeader` and `RecordSlots` requires that the slot after a buffer's root is a word slot that holds the buffer's length.  An array in a record is owned or borrowed as an `Array UInt64` argument is, through `Heap.Owned` and `Heap.Borrowed`, and a buffer as a `LeanExe.Bytes` argument is, through the buffer predicate `Heap.Buffer` of [the runtime model](../LeanExe/Pipeline/Runtime.lean).  A borrowed buffer, in a record or as an argument, meets the full `Heap.Buffer`, including the count of 1.  In a record, a buffer's root is 0 exactly when the buffer is empty.  A `LeanExe.Bytes` parameter may instead have a nonzero root and no bytes, which a record cannot hold.  The blocks of a value, the regions that a call reads, and the objects that a moved value consumes include its arrays and nonempty buffers, and `release` frees them with the records.

`RecordHeader` has two conditions on the value alone, at most 64 slots in a record and a word slot that holds a buffer's length after each buffer slot, and `RecordSlots` has the second.  An encoding that breaks the length condition makes `Represent.borrowed` and `Represent.owned` false for its values in every store, and one that breaks the slot bound makes `Represent.owned` and the precondition of a moved value false, while a borrowed value can still be represented.  An `Implements` statement over the type then holds for every module whenever the type is an argument, for a broken length condition, or a moved argument, for a broken slot bound.  A type that appears only as a result constrains nothing in either case, because only modules that always trap satisfy the statement, and those satisfy every `Implements` statement.  The `Represent` instances of a type with `Encode`, in [the `Implements` definitions](../LeanExe/Pipeline/Implements.lean), require the class `EncodeWellFormed`, which states both conditions for every record of every value.  `verified_recursive_type` proves the theorem `wellFormed` and, unless the type has one, the instance for every type that it declares, from the layout of the type's tree, the encodings of `List UInt64`, `Words`, and `KeyTree` prove it by hand, and the typed-tree audit fails for a recursive type of its example without the theorem.  With the instance, a reader of an `Implements` statement over the type can rule out that it holds vacuously because of these two layout conditions.  Values too large for 32-bit memory have no representation, such as a buffer of 2^32 bytes or an array of about 2^29 words, which limits single values and never every value of a type.

WGSL dispatch uses the shared [device model](#the-wgsl-library-and-the-browser-pages)
with strict binary32 arithmetic.  Its theorems prove successful modeled execution and race freedom
under their buffer, count, and invocation bounds.

### Outside the proofs

The theorems hold in Talos's semantics, which bounds no call depth and grows memory whenever the new page count is within the cap.  Wasmtime ends a deep recursion with a stack-overflow trap, so guarded code traps at depth 1,000, and the pure reflector limits the frame of every function whose code takes the call depth to 32 positions.  The tests run a frame of 32 positions, 26 of them live across the self-call, at depth 999 on Wasmtime 44 for aarch64.  [The WASI compiler](wasi.md#callable-and-command-modules) permits larger acyclic effectful helpers under its separate call-chain stack check.

`p.initial` proves that the modeled initial store meets the allocator invariant and the cap and holds the tables.  With a nonempty literal pool, it also proves the pool's static contents and heap region.  A later call must establish separation from its consumed argument blocks.  Real engine instantiation and host executables remain outside the proofs.  WASI compilation proves guest I/O sequencing under explicit host assumptions, as [the WASI proof premises](wasi.md#execution-proofs-and-their-premises) describe.  The floating-point theorems describe the WebAssembly deterministic profile, as the LeanExe compiler's do.  The numerical examples have further theorems about mathematical functions, rounding, and exceptional values, with the domains and bounds listed in [the algorithm index](../index.md) and each function's document.

## The dialect

[`Verified/Source.lean`](../Verified/Source.lean) defines the source language: the types `Ty`, the element types `Elem`, the expressions `Expr S Γ t`, typed by the callees' signatures `S` and the context `Γ`, and their meaning `denote`.  A program consists of ordinary Lean definitions, which the reflector translates into this language.  The reflector's error messages name the term or the type that it cannot translate.

### Programs and definitions

A program is the list of definitions in `verified_compile p := [f₁, …, fₙ]`.  A definition may call the definitions before it in the list and, when it is recursive, itself, so the only cycles are a definition's calls of itself.  When no source rule covers a term, the reflector unfolds a helper marked `@[inline]`, including an `abbrev`, and checks the equation for its expanded body.  A listed helper compiles as a function and takes precedence over unfolding.  A named constant that holds no array is reflected as its value.  The reflector reads a recursive definition through its unfolding equation `f.eq_def`, so it accepts structural and well-founded recursion, and it rejects a definition with universe parameters and a recursive definition that uses `sorry`.

### Types

| Type | Representation | Notes |
|---|---|---|
| `UInt64` | One i64 word | Arithmetic wraps modulo `2^64`. |
| `Bool` | One i64 word, 1 or 0 | |
| `Float` | One f64 word, its bit pattern | Lean's binary64, which equals Talos's `IEEE64` on bit patterns. |
| `Float32` | One f32 word, its bit pattern | Parameters, results, tuples, arrays, and loop state, with binary32 operations. |
| Pair of types without arrays | Words of the first component, then those of the second | Nested pairs are tuples. |
| Structure with a `Flat` instance whose tuple is its fields | Its fields' words | A nested structure is flattened in turn. |
| Enumeration with a `Flat` instance to a word | One word | Inductive type whose constructors have no fields. |
| Sum with scalar fields and a `Flat` instance | Word tag and words of the constructor fields | The tag occupies the tuple's first leaf.  Each constructor's fields occur once. |
| `Array α`, for `α` a word, `Bool`, float, tuple, flat structure, enumeration, or sum | Address of a length word followed by the elements' words | An element of `k` words occupies `k` consecutive words.  An array of tuples may only be a local value, since Lean has no `Represent` instance for it. |
| `LeanExe.Bytes` | Allocation root and UInt64 logical length | Packed bytes, with owned and borrowed parameters, results, pairs, copying, and release. |
| Pair that holds arrays, or structure whose `Flat` tuple holds arrays | Its components' words | A structure of this kind is a record with array fields. |
| Sum with a `Flat` instance whose tuple holds `Bytes`, arrays, or recursive types | Word tag and words of the tuple's components | The inactive components hold the instance's values: `Bytes.empty` and a null tree allocate nothing, and `#[]` allocates an empty array.  Parameters are borrowed. |
| `List UInt64` | Null for `[]`, otherwise a record holding the head word and tail pointer | Construction, matching, identity, duplication, tuples, calls, tail recursion, and folds with scalar state |
| Recursive type whose fields are `UInt64`, `Bool`, `Float`, `Float32`, arrays of these, `LeanExe.Bytes`, types with a `Flat` instance whose flattening holds these, or the type itself | Null for the first constructor without fields, and for any other constructor a record of its word and child fields in declaration order, then its array and buffer fields in declaration order, a buffer as its root followed by its length, after a tag word that holds the constructor's index when the type has more than one record constructor.  A `Bool` slot holds 1 or 0, a `Float` slot its bit pattern, and a `Float32` slot its bit pattern in the low 32 bits.  A field of a type with a `Flat` instance occupies one slot for each leaf of its flattening, in order. | Each record has between 1 and 64 slots, the tag included, at least one constructor has no child field, and at least one has a child field.  Construction, one-level matching, guarded and tail recursion, identity, duplication, tuples, calls, and loop state.  A type with a field that holds an enumeration or a sum cannot be a parameter of a recursive or tail-recursive definition. |

`Nat`, `Int`, `String`, `Option`, recursive types outside the listed layout, and arrays of arrays are outside the dialect.  Integers are `UInt64`, so that a program and its module compute the same values, wraparound included.  A read past the end of an array gives Lean's default element, whose flattening must have zero words.  An array stores each Float32 bit pattern in the low 32 bits of an eight-byte word.

`LeanExe.Bytes.empty` returns an empty buffer.  `bytes.size` returns its UInt64 length, and
`bytes.get index` returns a byte as a UInt64, or zero when the index is past the end.
`LeanExe.Bytes.build count f` takes a UInt64 count and stores the low eight bits of each UInt64
callback result.  A zero count skips allocation and the callback.  The code checks the count
before allocating the result and traps when the count is at least `2^32`.  Memory exhaustion may
also cause a trap under the allocation bound.

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
modules, such as those of an earlier compiler.  [The WASI manual](wasi.md) describes these bytes in stream actions and the separate I/O compilation command.

### Expressions

| Construct | Lean forms |
|---|---|
| Word arithmetic | `+`, `-`, `*`, `/`, `%`, `&&&`, `\|\|\|`, `^^^`, `<<<`, `>>>`, `min`, `max` |
| Word comparisons, unsigned | `==`, `!=`, `<`, `≤`, `>`, `≥`, `=`, `≠` |
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
| Packed bytes | `bytes![0, 255]`, `LeanExe.Bytes.empty`, `bytes.size`, `bytes.get index`, `LeanExe.Bytes.build count f`, with UInt64 counts, indices, and callback results |
| Tuples and structures | `(a, b)`, `.1`, `.2`, constructors, `{ s with … }`, field reads |
| Lists of words | `[]`, `x :: xs`, and `match xs with \| [] => empty \| x :: ys => node` |

Every construct has Lean's meaning.  Word division by zero gives 0, the remainder by zero is the dividend, and a shift uses its amount modulo 64.  Each insertion accepts indices from 0 through the array's length.  Beyond the length, `insertIdx!` returns `#[]`, and `insertIdxIfInBounds` and `LeanExe.insertAt` return the input array.  Updates and removals leave the array unchanged at indices greater than or equal to its length.  Boolean equality supports `==`, `!=`, decisions of `=` and `≠`, and `if` on either proposition.  `==` and `!=` on `Bool` require `LawfulBEq Bool`.

`min` and `max` use Lean's comparison and conditional at both float widths, preserving its NaN and signed-zero results.  Float comparisons `==` and `!=` use IEEE value equality.  The reflector rejects the bit-pattern propositions `=` and `≠` on floats.  Both `Float.ofBits` and `Float32.ofBits` canonicalize NaNs as Lean does.  Binary32 signed conversion interprets the low 32 bits of a `UInt64` as an `Int32`, and signed truncation returns the resulting `Int32` bit pattern zero-extended to `UInt64`.  Only the listed conversion forms accept the intermediate `UInt32` and `Int32` terms.  Conversions between `Float` and `Float32` remain outside the dialect.  Lean's opaque float functions, such as `Float.exp` and `Float.sin`, require definitions of their own, as the numerical examples provide.

### Array literals and conditions on propositions

The reflector reads an array literal with elements, `#[a₁, …, aₙ]`, as `((#[].push a₁).push …).push aₙ`, and the kernel checks the reading by unfolding `Array.push`.  The literal therefore allocates as those pushes do: an empty block, then the growth of an owned array at each push.  The allocation bound charges the first push with `growCost` and each later push with `paidGrowCost`, so a literal of two words costs 232 bytes.  The elements may be any expressions of the dialect, of any element type that an array holds, and a literal may stand wherever an array may, such as a loop's state or a result.

`if p ∧ q` and `if p ∨ q` on propositions test the decision of the proposition, by `ite_decide_eq`, and the reflector reads `decide (p ∧ q)` and `decide (p ∨ q)` as `decide p && decide q` and `decide p || decide q`, by `decide_and_eq` and `decide_or_eq` at the instance of the term.  Each part is a comparison, an equation of `Bool`s or enumerations, or another conjunction or disjunction, as in `(a < b ∧ b < c) ∨ (c < b ∧ b < a)`.  The code evaluates both parts of each connective, as it does for `&&` and `||`, so a part that calls a function or reads an array runs even when the other part decides the result, and a nested `if` keeps the second test lazy.  The rule holds in ordinary code, in the elements of builds, in loops, and in the conditions of tail loops, and the WGSL translation lowers the Boolean connectives.  [The forms example](../Verified/Examples/Forms.lean) compiles literals and both connectives in each of these places, among them two tail recursions on a conjunction and a disjunction.

The termination proof of a tail loop applies Lean's functional induction to the definition, whose cases state the conditions in Lean's simplified form, such as `¬(r ≤ 1 ∨ d ≤ 1)` as `1 < r ∧ 1 < d`.  The step equation keeps the source form, so the proof splits each remaining case on the step's conditions and closes the branches that contradict the case with `omega` on the words' natural numbers.  Negation `¬ p`, implication, and equivalence of propositions remain outside the dialect, as the restrictions table states.

### Loops and builds

`LeanExe.loop n init f` applies `f` to the indices `0` to `n - 1` in order, starting from the state `init`.  `LeanExe.repeatWhile fuel init cond step` applies `step` while `cond` holds, at most `fuel` times, and `LeanExe.build n f` is the array of `n` elements whose element `i` is `f i`.  The modules of [`LeanExe/Dialect/`](../LeanExe/Dialect) define the three, and the LeanExe compiler accepts them as well.  A state may have any type of the dialect, records with array fields included, and each part of a loop or a build is an expression of the dialect, which may hold further loops, builds, and calls.  `for`, `while`, and `do` notation are outside the dialect.  Recognized tail recursion compiles as a loop.

`xs.foldl step init` accepts every array element type and any accumulator type of the dialect.  The step may contain loops, builds, calls, and further folds, and an array accumulator may grow in place under the ownership rules.  The reflector requires the full-array bounds, `start = 0` and `stop = xs.size`.  Its source operation has Lean's full fold meaning.  Compiled lengths and indices use `UInt64`, and the heap representation bounds the array size below `UInt64.size`, which the compiler proof uses to equate the word-counted loop with the fold.  Folding over a record needs no default value or `Inhabited` instance for that record.

`List.foldl` accepts `List UInt64` and a scalar accumulator: words, Booleans, floats of either width, and their tuples, flat structures, enumerations, or sums.  The loop follows each cell's tail pointer and ends at null.  The step may contain calls, allocation, nested folds, and reads from captured values.  Captures remain borrowed during the fold, and ownership releases a constructed list or an owned capture after its last use.  A structural traversal computes allocation bounds and frames conditions.  A fold that calls guarded code retains that code's depth limit.  [The list example](../Verified/Examples/Lists.lean) and its [execution cases](../Verified/Examples/ListsCases.lean) cover these forms.

### Ownership

An array variable is borrowed or owned.  The reflector chooses each array parameter's mode with `Expr.paramChoice` in [`Verified/Reflect/Modes.lean`](../Verified/Reflect/Modes.lean): a parameter is owned when the body consumes it at its last use, as the array of an update, an extension, an insertion, or a removal, as an argument at an owned parameter, or as the result, and borrowed otherwise.  An owned parameter has type `Moved (Array α)` in the theorem, and the caller gives the array up.  The theorem holds for every choice of modes, so the choice affects only the code's cost.  When an update, an extension, an insertion, or a removal is the last use of an owned array, the code changes the array in its own block, and it copies any other array first.  An extension that finds no room moves the array to a block of at least twice its capacity, so the number of blocks that a loop of pushes allocates grows with the logarithm of its count.  The code releases each owned array after its last use, unless the array moves into the result or into an owned parameter.  A record parameter is always borrowed, so a callee that updates one of its arrays copies that array.

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
beside `T`, such as `Library.Trees.WordTree.verifiedKeyTree`.  They are `toTree`, the conversion to
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
that the type's encoding, which the LeanExe compiler's programs also import, does not import the
verified compiler.

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

A sum's `Flat` instance maps it to a scalar tuple with a distinct constant word tag for each constructor and each constructor field in one position.  The standard layout places the tag first, then every constructor's fields, with zeros in inactive fields.  Fields may themselves be scalar tuples, structures, or enumerations.  An accepted sum has no type parameters or indices.  Matching uses the tag to choose an alternative and its field positions to supply the alternative's arguments.  The kernel checks the translation by constructor cases.  Wildcard alternatives may bind the original value, and an expression used as a discriminant is evaluated once.  [The sum example](../Verified/Examples/Sums.lean) compiles the existing shape program, arrays of shapes, and a sum with Float32 and enumeration fields.

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

Such a sum is represented as its tuple, as a record with array fields is, and the instance's values for inactive fields are part of that representation: a construction of `.text body` allocates the empty array of the instance, while `Bytes.empty` and a null tree allocate nothing.  A variable of the sum is not split into components, since no function rebuilds the sum from its tuple.  A match destructures the variable once and tests the tag, and each branch releases the owned components that it does not use.  An owned value whose alternative names the matched value, as in `| other => other`, is copied before the match takes it apart, while an alternative that rebuilds its constructor, as in `| .text b => .text b`, moves the fields and allocates the constructor's empty arrays again.  A parameter of such a sum is borrowed, so a function that returns or consumes a field copies it.  The destructuring stores each nested pair of the tuple in fresh locals, the whole tuple first and then each remaining part, so a match on `Item`, whose tuple has seven words, takes 22 positions, and a function whose code takes the call depth may exceed its 32 positions.  A field may not itself be a record with arrays or a sum with heap fields, and arrays cannot hold such sums.

### Structure patterns

A `match` on a structure with a `Flat` instance may have several alternatives whose patterns fix fields to constructors of enumerations and bind the other fields, as `Calc.undo` of [the calculator example](../Examples/Calc/README.md) does with `| { value, steps, last := .add } => …`.  Each pattern binds the whole value, or applies the structure's constructor with each field a variable or a constructor of an enumeration that has a `Flat` instance to words, and the alternatives end with a wildcard or cover every combination of constructors.  The reflector reads the match as a chain of `if`s in the order of the alternatives.  Each test compares the words of the fields that one pattern fixes with `==` and joins them with `&&`, and the last alternative, or an alternative that fixes no field, takes no test and ends the chain.  A variable of a pattern becomes the projection of the matched value, and a pattern that binds the value receives the value.  A matched value that is neither a variable nor a structure built from variables is bound with `let` first, so the code evaluates it once.

The reflector proves that the chain equals the match by cases on the structure and on each fixed field, with variables for the value and for each alternative's body, and the kernel checks the proof by reducing both sides at each combination of the fixed fields' constructors.  The proof has one case for each combination, and the code reads each fixed field once for each test that names it.  [The pattern example](../Verified/Examples/Patterns.lean) compiles patterns that fix one field or two, fix different fields in different alternatives, fix every field, bind the value, or cover every constructor without a wildcard.  Its matches stand on parameters, on a structure built in place, on a call, in a loop's body, and on a record that holds an array.  A pattern that fixes a field to a literal, a `Bool`, or a nested pattern stops the reflector, as the restrictions table states.  Lean's `UInt64` is a structure without a `Flat` instance, so a `match` on a `UInt64` with literal patterns does not reach the rule and stops with `unsupported term`, as the pattern example checks.  A `match` with one alternative binds the fields, as the section on records states.

### Calls and recursion

A call passes its arguments' words and receives its result's words, a pair or a record as several WebAssembly results.  The command compiles recognized tail recursion as a Wasm loop: a step returns a result or continues with new parameter values.  It recognizes self-calls in tail position under bindings, conditionals, list matches, and single-alternative destructuring matches.  Continuation arguments cannot contain a self-call.  Parameter modes stay fixed across iterations, and mode inference propagates ownership from continuation arguments.  The reflector derives a decreasing rank from Lean's generated induction theorem.  The rank occurs in proofs and bound calculations.  Executable parameters and indices retain their dialect types.

Other recursion uses a call-depth parameter, and `set_option verified.tailLoops false` selects that path for every recursive definition in the command.  Guarded functions and their callers trap at `unreachable` when the depth reaches 1,000 and pass depth plus one to each depth-taking callee.  A tail loop takes the depth only when its body calls guarded code, and continuing iterations preserve it.  An exported entry starts a depth-taking function at depth 0.  Such a function may use at most 32 positions, including its depth, parameters, and locals.  Wasmtime keeps 8 bytes per value live across a call and 16 bytes per frame, so 1,000 frames of 32 positions take at most 272,000 bytes of its 512 KiB default stack.  The reflector supplies each recursive definition as its source meaning, with a fixed-point proof and, for a tail loop, a termination proof.  Recursive parameter types require an inverse of their flattening on every source value.  Enumerations, sums, and recursive types with a field that holds an enumeration or a sum are excluded from recursive parameter types, because invalid tags and inactive field values prevent that inverse.

### Tables and wrappers

A table is a Lean constant of type `Array UInt64`, which the module writes in a data segment.  A function reads a table as a borrowed array parameter, and a wrapper is a listed definition of the form `f x := g T₁ … Tₖ x` that applies a listed function `g` to tables before its own parameters.  The module exports the wrapper as an entry that pushes the tables' addresses and calls `g`.  The wrapper's theorem, `ImplementsTables`, requires a store that holds each table at its address, apart from the blocks that the arguments move, and `p.initial` proves that the store in which the module starts holds them.  Wrappers serve host entry, while internal definitions pass tables as parameters.  In [the Fourier implementation](../Library/Numerics/Fourier/Program.lean), `transformWith` passes Trig's tables to `twiddleWith`, which passes them to `Trig.cosWith` and `Trig.sinWith`.

### Restrictions

| Message | Cause | Rewrite |
|---|---|---|
| `unsupported term …` | Term that no rule covers: an unlisted helper without `@[inline]`, `for`, or an opaque float function | List the callee before its callers, mark a helper `@[inline]`, use the combinators, or define the float function. |
| ``a pattern fixes the field … to …, which is not a constructor of an enumeration with a `Flat` instance to words`` | Structure pattern that fixes a field to a literal, a `Bool`, or a nested pattern, such as `{ flag := true, value }`.  Patterns that fix fields to enumeration constructors compile, as [structure patterns](#structure-patterns) describes. | Test the field with `if`, or match the nested structure in a nested `match`. |
| `unsupported term match w with …` | `match` with several alternatives on a `UInt64`, such as `match w with \| 0 => … \| _ => …`.  Lean's `UInt64` is a structure without a `Flat` instance, so the rule of [structure patterns](#structure-patterns) does not apply. | Test the word with `if`. |
| `unsupported condition …`, `unsupported decision …` | `if` or `decide` on a proposition other than a comparison, an equation, and conjunctions and disjunctions of these, such as `¬ p` or `p → q` | Test `!decide p`, or state the comparison that `¬ p` negates. |
| `Array.foldl requires start = 0`, `Array.foldl requires stop = xs.size` | Fold over part of an array | Use a word-counted `LeanExe.loop` for that range. |
| ``the type … is not UInt64, Bool, Float, Float32, Bytes, a structure with a `Flat` instance, an array, or a pair`` | Parameter, result, or binding of a type outside the dialect, such as `Nat` | Use the dialect's types, and give a structure or an enumeration a `Flat` instance. |
| `= and ≠ on … compare bit patterns; use == and !=` | `=` or `≠` on `Float` or `Float32` | Use `==` or `!=`. |
| ``an index must be `i.toNat` for a word `i` ``, ``a position must be `i.toNat` for a word `i` `` | Read or update at a position that is not a word's `toNat` | Index with `i.toNat` for `i : UInt64`. |
| `Lean has no Represent instance for …, so no theorem can be stated for it` | Parameter or result whose type has no instance, such as an array of tuples | Keep such an array local, or use an array of structures with a `Flat` instance. |
| `an array holds elements, not …` | Array of arrays, or of records with array fields | Store the inner arrays in one array at computed positions. |
| ``the `Flat` instance of … is not a tuple of its fields``, ``… repeats a field``, ``… does not hold all its fields`` | `Flat` instance other than the tuple of the structure's fields | Map the structure to the tuple of its fields, each once. |
| `unsupported comparison on …` | Comparison outside the supported word, float, enumeration, and Boolean equality forms | Compare supported scalar components. |
| `unsupported negation …` | `-x` on words | Write `0 - x`. |
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

A program's file imports `Verified.Reflect.Command` and the definitions, and runs one command.  Native definitions live in separate `Program` modules, so each compiler can compile the same functions, as [`Library/Random/Lcg/Verified.lean`](../Library/Random/Lcg/Verified.lean) shows for the [LCG generator](../Library/Random/Lcg/README.md).  The command lists the definitions in calling order, a callee before its callers.  A program over a user-defined recursive type also imports the module that runs `verified_recursive_type` for the type, as [Ownership](#ownership) describes.

```lean
import Verified.Reflect.Command
import Library.Random.Lcg.Jump

namespace Library.Random.Lcg.Verified

open _root_.Library.Random.Lcg

verified_compile compiled := [affine, step, advance, jumpPass, jump]
```

The command adds the program, the module, and every theorem in one step, and the kernel checks each.  The theorems use only the axioms `propext`, `Classical.choice`, and `Quot.sound`, as `#print axioms` shows for `Prog.correct`, `Prog.correctWith`, and each example's `compiled.bytes` and named theorems.  The declarations and the exports take the last component of a definition's name, so two listed definitions whose names end in the same component collide.

`set_option trace.Verified.reflect true` reports the reflection and proof-generation stages for each function and the encoding check for each function index.  Reflection entries include the remaining heartbeat budget in the units of `maxHeartbeats`.

### `verified_compile_wasi`

`import Verified.Wasi` provides a separate frontend for `LeanExe.Wasi.Action` definitions.  Its callable form is `verified_compile_wasi p := [pureHelper, actionHelper, action]`.  Adding `(main := main)` selects a closed `Action UInt64`, exports `_start`, and passes main's returned status to `proc_exit`.  The native API uses ordinary `do` notation, UInt64 lengths and counts, packed bytes, bounded loops, and acyclic effectful helpers.  Pure helpers use this manual's dialect and recursion rules.

Generated callable `.implements` and command `.start` theorems execute the exported wrappers with their hidden depth and table arguments.  They relate each sufficiently fueled target execution to a native source execution with the same ordered effects, world, and result, or to a source prefix on a permitted guest resource trap.  Conditional `.total` theorems require allocation room, `Resource.CallPrefixBound` for the typed program, and `host.NoTrapsAlong` the native action.  Host traps and rejected exits remain terminal outcomes of the general refinement theorem.  [The WASI manual](wasi.md) defines the generated declarations, ownership and scratch premises, modeled initial store, and host policies.  [The development journal](../devnotes.md#2026-10-23-implementing-the-wasi-agenda) records implementation and test results.

### Generated declarations

These declarations belong to the pure `verified_compile` command.  [The WASI declaration table](wasi.md#declarations) describes `verified_compile_wasi`.

| Declaration | Content |
|---|---|
| `p.program`, `p.funs`, `p.meaning` | Source program, meanings of its functions, and proof of `Prog.Meaning p.program p.funs`. |
| `p.tables`, `p.wrappers`, `p.module` | Tables, wrappers, and module `compileWith p.program p.tables p.wrappers`. |
| `p.literalPool` | Deduplicated nonempty byte literals, starting after the constant word-array tables.  The module uses this pool explicitly. |
| `p.initial` | The store in which the module starts meets the allocator invariant, caps the memory at 65,535 pages, and holds each table at its address.  A nonempty pool adds its static contents and heap region as a fourth conjunct.  An empty pool keeps the three-part result. |
| `p.bytes` | `∃ bytes, encode p.module = .ok bytes ∧ decode bytes = .ok p.module ∧` the conjunction of the theorems `p.f.implements`. |
| `p.sections`, `p.bodies`, `p.data`, `p.encoding` | Literal byte lists for the sections, function bodies, and data, and their assembly into the module's bytes. |
| `p.func_ok_k`, `p.rest_ok`, `p.data_ok`, `p.codes_ok`, `p.funcs_count`, `p.funcs_length` | Kernel-checked encoding claims for each function, the other sections, and the sizes. |
| `p.encoded` | `encode p.module = .ok ⟨p.encoding.toArray⟩`, with the bound on each function's locals that `decode_encode` requires. |
| `p.inSubset` | `LeanExe.Native.InSubset p.module`: the module is in the subset of WebAssembly that the translator to C accepts.  A module outside it gets a warning that names the first part outside, and no theorem. |
| `p.native_part_k`, `p.native_parts`, `p.translation_infos` | Checks from which `p.inSubset` and `p.translation_funcs` follow, one theorem for each function: function `k`'s `functionViolation` is `none`, and its `callInfo`, the functions that its C function calls, is entry `k` of the literal `p.translation_infos`. |
| `p.translation`, `p.translation_funcs`, `p.translation_eq` | For a module that translates with `nativeCap` pages: its translation to C, the list of the functions that the translation contains, and `translate nativeCap p.module = some p.translation`.  A module that does not translate gets a warning. |
| `p.f.native` | For a function that the translation contains: under every global environment that holds the translation's globals, memory, and functions, the C function computes `f` as `p.f.implements` states (`NativeImpl`, `NativeTablesImpl`, or `NativeStaticImpl`).  After a return, `p.f.native` concludes, as `p.f.implements` does, the postcondition, unchanged memory caps, and the region clause: every nonempty region of the heap apart from the moved blocks keeps its bytes, remains a region of the final heap, and lies outside the result.  With `set_option verified_compile.alignedNative true`, for a program without byte literals, the command also states the translation without the alignment test, `p.translationAligned`, its equation `p.translationAligned_eq`, and `p.f.nativeAligned`, which is `NativeAlignedImpl p.f.implements` or `NativeTablesAlignedImpl p.f.implements`: from an input that meets `AlignedInput`, the C function computes `f` as `p.f.native` states, with an aligned final heap and a result whose blocks meet `AlignedOutput`.  The SHA-256, SHA-3, CRC, and insertion-sort modules of the library and the verified Euler and binary32 GPT-2 modules set the option. |
| `p.f.aligned` | For each definition of a program without byte literals: from an input whose heap, consumed objects, and read regions are aligned, every run of the entry from some fuel on makes only aligned 64-bit accesses inside memory, and the final heap and the result's blocks are aligned.  `p.f.nativeAligned` follows from it and `p.f.implements`. |
| `p.f.func`, `p.f.denote_eq` | Source function and its body equation.  A tail body's equation describes its return-or-continue step.  A wrapper has no source function, and its equation relates it to its callee at the tables and parameters. |
| `p.f.implements` | With an empty literal pool, `ImplementsA aborts p.module k f` with Lean's instances, or `ImplementsTables` for a wrapper.  With a nonempty pool, `ImplementsStatic p.literalPool aborts p.module k f tables Pre Post`, including the static input premise. |
| `p.f.uniform`, `p.f.pure` | For eligible scalar functions in a program with an empty literal pool: raw execution is independent of the store, and `ImplementsPureA aborts` computes the Lean result while preserving the whole store. |
| `p.f.argsAgree`, `p.f.resultAgree` | Lean's instances represent the arguments and the result as the source's instances represent their flattenings. |
| `p.f.bound`, `p.f.bound_eq` | Allocation bound in bytes on the argument tuple, and its equation in the parameters.  For a function whose code takes the call depth, the bound takes the number of frames first. |
| `p.f.cost`, `p.f.cost_eq` | For a function with a paid parameter: the bound without the credits of the paid arguments, and its equation. |
| `p.f.trapFree` | With an empty literal pool, `ImplementsA false`, or `ImplementsTables false` for a wrapper whose callee takes no call depth.  It requires room when `aborts` is true and the frames condition for guarded calls.  With a nonempty pool, `ImplementsStatic` with `aborts = false` adds static input, allocation, and guarded-call premises.  Such wrappers receive `trapFree` through `Wrapper.bound`, without a named wrapper `bound` declaration. |
| `p.f.fits`, `p.f.fits_eq` | For a function whose code takes the call depth: the frames condition, and its equation. |
| `p.f.meaning`, `p.f.meaning_eq`, `p.f.fixed` | For a recursive definition: its meaning on source environments, the equation of its self-call, and the fixed-point equation. |
| `p.f.body`, `p.f.step`, `p.f.step_eq`, `p.f.wellFounded`, `p.f.decreases` | For a tail loop: its typed body, native return-or-continue step, their agreement, the well-founded continuing relation, and the source rank's decrease. |
| `p.flat_injective.E` | For each enumeration that the program compares, with `E` its full name: its flattening is injective, which the comparisons of its words use. |
| `p.flat_eta.R`, `p.flat_field.R.f` | For each record with array fields that the reflector splits, with `R` its full name: the eta law of its flattening, and the equation of field `f` with its component of the flattening. |

Functions 0 and 1 of the module are the runtime's `alloc` and `release`, and function `2 + k` is the `k`-th listed definition that is not a wrapper, counted from 0.  In a program of `n` such definitions, the entry of the `j`-th definition whose code takes the call depth is function `2 + n + j`, and the wrappers follow the entries.  The module exports each definition under its name, at its entry when its code takes the call depth.

A call theorem for one export starts from `p.f.implements` or `p.f.trapFree`.  [The call module](../Verified/Call.lean) states the call as `Verified.Call p.module p.tables k f Pre Post`: from a store that `Verified.Ready p.module p.tables` states ready, with borrowed or scalar arguments and `Pre`, function `k` returns `f x` without a trap and leaves a ready store.  The call also keeps every borrowed array borrowed and every region of the heap intact, and it meets `Post`.  `Verified.CallSpec p.module p.tables k f B` is that statement with room for `B x` bytes before the call and a rise of `top` by at most `B x`.  `Verified.ImplementsTables.call` proves `Call` from the entry's theorem, `Verified.Call.spec` proves `CallSpec p.module p.tables k g p.f.bound` from `p.f.trapFree` for a specification `g` that equals `f` on represented arguments, for words, word arrays, and tuples of them, as `Examples.Increment.compute_callSpec` does.  `Verified.Ready.initial rfl p.initial` proves that the store in which the module starts is ready.

### Module composition

The typed API combines separately reflected programs with `Prog.append`:

```lean
def program := source.program.append library.program
def funs := source.funs.append library.funs
theorem meaning : program.Meaning funs := source.meaning.append library.meaning
def module := Verified.compile program
```

The library's functions keep their indices.  Each source function and each call between source
functions moves by the library's function count.  `FVar.appendLeft` refers to a relocated source
function, and `FVar.appendRight` refers to a retained library function.  A new typed function can
call both.  The generic append theorem carries the existing meaning proofs through ordinary,
guarded-recursive, and tail-recursive functions.  The tail rank changes only in the proof.
Function export names must be unique.  Tables and wrappers remain arguments of `compileWith`.

`Prog.calls_append` reuses the library's execution, allocation, and frames theorems in the
combined module.  A shared pool must cover both programs and compile both function lists.
[Append coverage](../Verified/ProgramLiterals.lean), `Prog.covered_append`, gives the two coverage
premises.  `Prog.correctStatic` applies to the combined meaning proof.  With no nonempty
literals, `Prog.correct` supplies the empty-pool specialization.  The scalar proof generator
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
bit conversions can carry infinities and NaNs.  The shared WGSL translation normalizes arithmetic
NaNs to `0x7fc00000`.

After `verified_compile compiled := [scale]`, the typed API constructs the kernel as follows:

```lean
import Verified.WGSL.Compile

def gpu := (Verified.WGSL.compile (e := .float32) compiled.scale.func.body).get (by decide +kernel)
def kernel : LeanExe.WGSL.Module := gpu.module
```

Compilation returns `none` when translation or the local-layout check fails.  Each successful
result carries their proofs.  `gpu.dispatch_eq` states that dispatch returns the source array,
encoded as words, and that the dispatch is race-free.  Its conditions include input arrays and
an output count below 2²⁹, the count's agreement with its parameter or array, an output buffer
with the length header and room for every element, and enough invocations to cover the output.
The theorem uses the existing device model with strict binary32 arithmetic.
[The kernel examples](../Verified/Examples/Wgsl.lean) compile ordinary Lean
definitions with both backends.  [Their native-value proofs](../Verified/Examples/WgslProof.lean)
combine the generic dispatch theorem with the generated `denote_eq` equations.

[Binary32 GPT](../Demos/Gpt32/Verified.lean) compiles the thirteen unchanged kernel functions
of the existing application.  [Its dispatch proofs](../Demos/Gpt32/VerifiedDispatch.lean)
reuse `Compiled.dispatch_value`, which transports source correctness through a native
denotation equation.  [Its host theorem](../Demos/Gpt32/VerifiedHost.lean) instantiates the
existing typed generation proof with the new kernel map.  It states the native step's scores
and race freedom under the same device model and shape, token, and weight bounds.  [The WGSL
tests](#wgsl-tests) compare these kernels and those of the examples with native Lean.

### The WGSL library and the browser pages

[`LeanExe/WGSL/`](../LeanExe/WGSL) defines the WGSL subset of the kernels, a printer, a parser that `Module.parse_print` proves to invert the printer, and the device model, a semantics in which binary32 operations compute Talos's `IEEE32` results and a dispatch runs its invocations in order.  `Verified.WGSL.compile`, which [WGSL kernels](#wgsl-kernels) describes, translates into this subset.  [`tools/EmitWgsl.lean`](../tools/EmitWgsl.lean) prints a kernel after checking that the parser reads the text back as the kernel, and [`tools/build-webgpu-host.sh`](../tools/build-webgpu-host.sh), after [`tools/download-wgpu-native.sh`](../tools/download-wgpu-native.sh), builds `build/tools/leanexe-webgpu-host`.

`uv run tests/web/serve.py` serves two pages on http://127.0.0.1:8000/.  The kernel page runs the WGSL kernel cases on the browser's WebGPU and compares every word with native Lean's, and the GPT-2 page runs GPT-2 124M in binary32 with its kernels on WebGPU, in `gpt32.wasm`, or on both with their scores compared.  The pages load the verified compiler's kernels and cases, which `tests/wgsl/run.sh` writes to `build/wgsl` without an option, and its modules `build/verified/gpt32.wasm` and `build/verified/gpt.wasm`.  With `--leanexe`, the server loads the LeanExe compiler's kernels and cases from `build/wgsl-leanexe` and its modules `build/gpt32/gpt32.wasm` and `build/gpt/gpt.wasm`.  The GPT-2 page needs the weights that `uv run tests/gpt32/generate.py --export` writes, and [the description of the pages](../tests/web/README.md) covers the setup, the controls, and what is proved about the pages.

### Emitting and running

```sh
export PATH="$HOME/.elan/bin:$HOME/.cargo/bin:$PATH"
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
build/tools/leanexe-wasmtime-host call build/verified/clob.wasm insertLevel \
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

Options before the mode configure WASI.  `--wasi` links WASI preview 1, and `run MODULE.wasm` enables WASI and calls `_start`.  `--stdin-file`, `--stdout-file`, and `--stderr-file` give the guest's streams, which the guest otherwise inherits from the host.  `--control-file` receives the host's own output, the control records, which otherwise go to the host's stdout.  [The WASI manual](wasi.md#wasmtime-host) states which combinations each mode requires.  In WASI mode, the control output of a failed run ends with `wasi-exit N`, `trap`, or `error`, and in `run` mode the host writes records only to a control file.  Without `--wasi`, the host writes no outcome records, and its status and stderr report a failure.

| Record | Meaning | Host status |
|---|---|---|
| Result line, `results r0 r1 …`, `u64 V X`, `memory P L HEX`, `memory-size N`, `saved N` | Output of a call or a script command. | 0 |
| `stats A F` | Allocation and free counters after `call-stats` or the `stats` command. | 0 |
| `return` | `_start` returned in `run` mode. | 0 |
| `wasi-exit N` | Call of `proc_exit` by the guest with a status `N` that Wasmtime accepts. | `N` modulo 256 |
| `trap` | Trap in the export that the mode or a script `call` command calls. | 2 |
| `error` | Any other failure after the control output opens: a Wasmtime error, a rejected exit status, a trap in `alloc`, `reset`, or module initialization, a malformed result, or a host failure. | 1 |

## Proving

### Representations

`Represent α` says how a value appears to a compiled function: its WebAssembly values, the heap data they point to when borrowed and when owned, the blocks its owned objects occupy, the regions a call reads, and the pointers a call consumes.  `Scalar` covers values without heap data: `UInt64`, `Float`, `Float32`, `Unit` for a function without parameters, pairs, and any type with a `Flat α β` instance, which represents `α` as the scalar `β`.  `Bool` has the instance `cond b 1 0` built in, and a user enumeration, structure, or sum needs its own `Flat` instance, such as `Flat Calc (UInt64 × UInt64 × Op)` in [the enumeration example](../Verified/Examples/Enums.lean).  The instances are part of what the theorem states.

Arrays have instances for `Array UInt64`, `Array Float`, `Array Float32`, and `Array α` for a flat `α`, which is stored as `flatWords xs`.  `LeanExe.Bytes` has the instance of [the byte representation](../LeanExe/Pipeline/Bytes.lean), a pair of represented types is represented by its components, and a structure whose `Flat` tuple holds arrays is represented as that tuple through [the flat records](../LeanExe/Pipeline/FlatRecords.lean).  `Moved α` represents a consumed argument for these arrays, for `LeanExe.Bytes`, and for types with `Encode`, and a function's argument tuple gives an owned parameter the type `Moved`.

A type with `Encode` and `EncodeWellFormed` instances is represented by the records that `encode` gives, a `Node` tree of words, children, arrays, and buffers, and `List UInt64` has both instances built in.  A user recursive type needs an `Encode` instance, from which `verified_recursive_type` derives `EncodeWellFormed` and the declarations that compile programs over the type, as [Ownership](#ownership) describes.  `EncodeSlotted` states that every record of an encoded value has a slot, which gives the slot regions of a borrowed value positive length, as the keep lemmas of [the VKB entry on region frames](../VKB/entries/region-frame/README.md) require, and `List UInt64`, `Words`, `KeyTree`, and `Verified.Tree shape` have instances.

### The `Implements` family

| Predicate | Statement |
|---|---|
| `Runs aborts env m k store args P` | Every run of entry `k` with enough fuel returns values satisfying `P` or, when `aborts`, traps at `unreachable`.  `ReturnsOrAborts` is `Runs true`. |
| `Implements m k f` | `ImplementsA true m k f` without a precondition or a postcondition, as `Implements.toA` states.  A run may trap. |
| `ImplementsPureA aborts m k f` | For scalar arguments and results: from any store, the call returns the values of `f x` and leaves the store unchanged, or traps when `aborts`.  `ImplementsPure` is the `true` case, `ImplementsPure.implements` derives `Implements`, and `ImplementsPureA.implementsA` derives `ImplementsA` with a postcondition that keeps the heap and the store.  `p.f.pure` states it. |
| `ImplementsA aborts m k f Pre Post` | Statement of [the `implements` theorem](#the-implements-and-trapfree-theorems), with the abort flag, a precondition `Pre x heap store`, and a postcondition `Post x heap store heap' final`.  `ImplementsA.implements_of` derives `Implements` from `ImplementsA true` when `Pre` always holds. |
| `ImplementsTables aborts m k f tables Pre Post` | `ImplementsA` with the further premise that each table of `tables`, an address and its words, is borrowed and lies apart from the moved blocks.  A wrapper's `p.f.implements` and `p.f.trapFree` state it. |
| `ImplementsStatic pool aborts m k f tables Pre Post` | `ImplementsTables` with the further premise `pool.Input heap store params x` on the byte-literal pool.  The functions of a program with nonempty byte literals state it. |
| `Satisfies m k P Q` | For inputs satisfying `P`, the call traps or returns an owned `y` with `Q x y`.  `Implements.transfer` derives it from `Implements` and `∀ x, P x → Q x (f x)`. |

A theorem about a function of several parameters takes them as one tuple in declaration order, as `lcg_advance` states `ImplementsA false compiled.module 4 (fun x : UInt64 × UInt64 => advance x.1 x.2)`, and the entry index is the function's index in the module, which [the generated declarations](#generated-declarations) give.  The arguments are reversed in `Runs` because Talos lists them with the top of the stack first.  A call of `gcd a b` therefore takes `[.i64 b, .i64 a]` in `Library.Numerics.Arithmetic.Gcd.gcd_call`.

### Using the generated theorems

The generated theorems state facts about Lean functions, so a theorem about a program combines with them in ordinary Lean.  `p.bytes` gives the bytes and their decoding, and `p.f.implements` gives a function's theorem.  `lcg_advance` in [`Lcg.lean`](../Library/Random/Lcg/Verified.lean) combines the module's bytes and theorem with the period theorem of [`Library/Random/Lcg/Period.lean`](../Library/Random/Lcg/Period.lean):

```lean
theorem lcg_advance : ∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok compiled.module ∧
    LeanExe.Pipeline.ImplementsA false compiled.module 4
      (fun x : UInt64 × UInt64 => advance x.1 x.2) (fun _ _ _ => True) (fun _ _ _ _ _ => True) ∧
    ∀ x y : UInt64, ∃! n : UInt64, advance n x = y := by
  obtain ⟨bytes, success, decoded, _⟩ := compiled.bytes
  exact ⟨bytes, success, decoded, compiled.advance.implements, advance_existsUnique⟩
```

A theorem for one function gives a theorem for an equal function by rewriting: `lcg_jump` rewrites `compiled.jump.implements` with `jump_eq`, which states that the jump-ahead program computes `advance`.  `ImplementsA.mono` strengthens a precondition or weakens a postcondition, and `drone_trapFree` in [`Drone.lean`](../Demos/Drone/Verified.lean) uses it to replace the planner's bound by the constant 2,251,064.  The drone's theorems `drone_compute` and `drone_safe` combine the bytes with the planner's optimality and safety theorems in the same way.

### Bounds and total execution

`p.f.bound x` counts the bytes by which the allocator's `top` can rise during the call: 48 bytes of header plus the payload for each copy, each built array, and each block of `push`, `++`, and `insertAt`, with no reuse of freed blocks.  `p.f.bound_eq` states the bound as a Lean term that follows the definition: the loop counts, states, and call arguments of the program, the block sizes `blockCost`, `growCost`, `paidGrowCost`, and `creditCost` of [`Verified/BoundFacts.lean`](../Verified/BoundFacts.lean), `loopCost` and `sumBelow` of [`Verified/Bound.lean`](../Verified/Bound.lean) for loops and builds, `min` of the unpaid and paid bounds for a loop whose state is a paid pair, and `p.g.bound` at the arguments of a call, or, for a callee `g` with a paid parameter, `p.g.cost` and `creditCost` of each argument that the call charges.  A function that allocates nothing gets `p.f.bound x = 0`, and a record's arrays appear as its fields, such as `b.prices.size`.  `BoundFacts.lean` gives the closed forms, such as `blockCost_eq`, sums of `sumBelow`, `loopCost_const` for passes of equal cost, and `loopCost_le`, which bounds a loop's cost by an invariant of its index and state.  `pushSquare_bound` in [`Tables.lean`](../Verified/Examples/Tables.lean) shows the method:

```lean
theorem pushSquare_bound (xs : Array UInt64) (k : UInt64) :
    compiled.pushSquare.bound (⟨xs⟩, k) = 16 * (xs.size + 1) + 80 := by
  rw [compiled.pushSquare.bound_eq, compiled.pushWith.bound_eq, compiled.pushWith.cost_eq,
    creditCost, paidGrowCost_eq]
```

The bound charges an extension of an owned array by amortization.  An owned array of `n` words in a block of `c` bytes holds the potential `4 · 8 (n + 1) ∸ 2c`, and every owned array parameter of a function whose body extends an array, by `push`, `++`, `insertAt`, or a call with a paid parameter, is paid: the caller charges its credit, `creditCost`, 16 bytes per word and length word, and each extension of the paid array is charged `paidGrowCost`, a header and 32 bytes per added word.  The potential covers the bytes of the moves to larger blocks, so a loop of `n` pushes of one word onto a paid state is charged `80 n` bytes plus the credit.  For a function with a paid parameter, `p.f.cost` is the bound without the credits, and `p.f.bound` adds them.  [The internals](../Verified/README.md) give the rules that decide which values are paid.

The bound ignores the reuse of freed blocks and charges every extension of a dying owned array as a new block, so a precondition that fails says nothing about the program.  The bound also depends on the modes that `Expr.paramChoice` chooses.  The precondition `heap.Within store p.module (p.f.bound x)` states that `top` plus the bound is at most `65536` times the memory's cap, at most 4,294,901,760 bytes, and no theorem bounds the memory's size in pages.

`foldCost xs init step charge` in [the fold lemmas](../Verified/Reflect/FoldLemmas.lean) sums each fold step's allocation charge at its element, index, and accumulator.  The generated bound adds the initial expression's charge, a copy of a borrowed initial state when needed, and its potential credit.  A fold whose steps allocate nothing has charge 0.  The bound calculation uses natural arithmetic over the array's word-sized count.  It adds no executable `Nat` counter.

### Bounds of recursive functions

For a tail loop, the bound equation sums native per-step charges with `Verified.Tail.costAt` over the proof-derived rank plus one.  The charges come from the ordinary expression-bound builder with a continuing call charged at zero.  A loop whose steps allocate nothing has bound 0 without evaluating its rank.  A loop that calls guarded code also has a frames equation expressed by `Verified.Tail.fitsAt`: each iteration checks its callees at the same available depth.  [The tail example](../Verified/Examples/Tail.lean) proves a zero allocation bound and includes a guarded callee.

For guarded recursion, `p.f.bound k x` and `p.f.fits k x` take the number of frames `k` first, and `p.f.trapFree` holds under `p.f.fits 1000 x = true ∧ heap.Within store p.module (p.f.bound 1000 x)`.  `p.f.fits_eq` and `p.f.bound_eq` state `p.f.fits (k + 1) x` and `p.f.bound (k + 1) x` for every `k`, with `p.g.fits k` and `p.g.bound k` at each depth-taking call, self-calls included.  For a function with a paid parameter, `p.f.cost_eq` states `p.f.cost (k + 1) x` in this way, with `p.g.cost k` and `creditCost` at a call of such a `g` with a paid parameter, and `p.f.bound_eq` states `p.f.bound k x` as the credits plus `p.f.cost k x`.  `p.f.fits 0 x = false` holds by `rfl`, so a property of `p.f.fits 1000 x` follows by induction on `k`.  In [`Recursion.lean`](../Verified/Examples/Recursion.lean), `chain_fits` shows in this way that `compiled.chain.fits k n` holds exactly when `n < k`, and `chain_trapFree` that the module computes `chain n` without a trap for every `n` below 1,000.  `fill_fits`, `fill_cost`, and `fill_trapFree` do the same for a recursion that extends a paid array parameter and moves it into the next call.

### Axiom checks

A theorem may depend only on `propext`, `Classical.choice`, and `Quot.sound`.  Modules such as [the GCD compilation](../Library/Numerics/Arithmetic/Gcd/Compiled.lean) end with `#print axioms` for their theorems, and [`tools/full-check`](../tools/full-check) builds at log level info and fails on a report from a file of this repository that names any other axiom.  A check of other theorems is a Lean file outside the repository that imports their module and prints their axioms, run through [`tools/leanrun`](#toolsleanrun-and-the-shared-lock).  Any further axiom, such as `sorryAx` from an incomplete proof or the axiom that `native_decide` adds, is a failure.

```lean
import Library.Numerics.Arithmetic.Gcd.Compiled
#print axioms Library.Numerics.Arithmetic.Gcd.gcd_call
```

```text
'Library.Numerics.Arithmetic.Gcd.gcd_call' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Testing

### Module cases

[`tests/verified/run.sh`](../tests/verified/run.sh) writes each example's module to `build/verified/`, validates it with `wasm-tools`, and compares every case of [`Verified/Examples/Cases.lean`](../Verified/Examples/Cases.lean) between the Wasmtime host and native Lean.  `Cases.lean` prints one line per case, `module|export|result kind|host arguments|expected result`, computed by native Lean, with an optional sixth field, the number of blocks that must stay allocated after the call, and a seventh, a bound on the number of allocations, the host's included.  The expected result `trap` requires a trap at `unreachable`.  Native Lean writes a panic message for each read, update, or `insertIdx!` past the end, and the script counts these messages and fails on any other output to standard error.  The full invocation needs `lake build`, whose default targets include the module cases of the Euler check, `lake build Verified Library`, and the Wasmtime host `build/tools/leanexe-wasmtime-host`.  The driver adds `~/.cargo/bin` to its search path for `wasm-tools`.

`tests/verified/run.sh --cases frontend` builds and emits the selected module, validates it, builds the case generator and its imports, and compares its checked cases, including allocation counters.  Its insertion cases cover empty arrays, indices at and beyond the end, the largest word, a computed index, fresh and aliased inputs, and float and record elements.  The full invocation also runs the numerical byte/file proofs and native accuracy checks.  Each module has an entry in [the module registry](../tests/verified/modules.txt) and a checked corpus.  [The library case map](../tests/verified/library-cases.txt) reuses the compiler fixtures' cases for the shared library compilations.

`tests/verified/run.sh --cases fold` checks word and float folds, record elements without an `Inhabited` instance, owned array and pair accumulators, a borrowed input that is also the initial accumulator, nested folds, and calls in fold bodies.  Allocation counters check retained blocks and growth in place.  A recursive callee runs at depth 999, and the next frame at depth 1,000 must trap.

`tests/verified/run.sh --cases tail` checks default loop compilation through 4,096 iterations, scalar pairs and exceptional floats, record arrays, owned-array growth, swapping and replacement, an aliased seed, calls between tail functions, and a guarded callee.  It checks retained blocks and allocation counts.  The Recursion and Fold examples set `verified.tailLoops` to false to retain their guarded-depth tests.

`tests/verified/run.sh --cases tailconditions` checks Boolean coercions, word inequality, a proof-named conditional, destructured scalar tuples, and borrowed pair and record states through 4,096 iterations.  The borrowed-state cases require one retained input block and no additional allocation.

`tests/verified/run.sh --cases scalarcomposition` checks generated store-preserving scalar
functions: division, conditional calls, tail recursion through 4,096 iterations, float call
chains, and binary32 bit conversion and nearest-even rounding.  Every case checks zero
allocations and retained blocks.

`tests/verified/run.sh --cases relocation` reuses that scalar corpus after moving its library
behind another compiled program.  It also checks the retained library function and a new
caller that invokes functions from both libraries.

`tests/verified/run.sh --cases lists` checks construction, duplication, nested calls, matching,
head and tail access, reconstruction, and head updates on lists through 4,096 cells.  It checks
retained blocks and allocation counts, including reconstruction with no allocation beyond the
host's input cells.

`tests/verified/run.sh --cases listrecursion` checks guarded summation and recursive increment.
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

`tests/verified/run.sh --cases gpt` tests binary64 GPT with the existing corpus in [`tests/gpt/Cases.lean`](../tests/gpt/Cases.lean) and the release and cache-growth checks of [`tests/gpt/sessions.sh`](../tests/gpt/sessions.sh).  `tests/verified/run.sh --cases euler` uses [the existing Euler corpus](../Demos/Euler/Cases.lean) through `tests/modules/run.sh --module euler PATH`.  The full invocation includes both application checks.  `tests/verified/run.sh --cases slew` compares the slew planner with native Lean on plans and `atan2` calls that [a generator in Lean](../tests/TestSupport/Slew/Cases.lean) builds from SplitMix64.  [`tests/slew/edges.sh`](../tests/slew/edges.sh) compares the module's `edgeOk` export with native Lean on single-cone edges in one host session, and the same run checks the planner's theorems with [the axiom audit](../tests/slew/Axioms.lean) and its file theorems against the written module.

The cases cover words near 0, `2^32`, `2^63`, and `2^64`, zero divisors, shift amounts of 64 or more, loop counts of 0, 1, and up to 65,537, empty arrays, reads and updates past the end, and floats that are zeros of both signs, infinities, NaN, and the smallest subnormal.  Native Lean returns the canonical NaN for every NaN result, and the host enables Cranelift's NaN canonicalization, so the cases compare float results bit for bit.  The release counts show that a call leaves allocated exactly the result's arrays and the host's arrays at borrowed parameters.  The allocation counts show the updates in place and the growth by doubling: a loop of `n` pushes allocates at most `2 + log₂ (n + 1)` blocks, and an insertion sort of `n` elements at most `3 + log₂ (n + 1)` with the host's array.  One case asks for an array of `2^29` words and must trap.  A recursion case runs `deep`, whose frame has 32 positions, 26 of them live across the self-call, to depth 999, where its deepest frame calls `top1` and `top2`, two functions without the call depth that hold many values live.  The drone's cases include the terrains of [`tests/drone/corpus.txt`](../tests/drone/corpus.txt).

### Accuracy checks

Before the module cases, the driver builds the byte-theorem modules of [the file-theorem registry](../tests/verified/numerics.txt) and checks each file module against the file it emitted.  The registry holds 130 of the 131 modules of the module registry, all but `byHand` of `Modes`, which has no `p.module`.  Each file module proves that its file holds the encoding and decodes to the module of its byte theorem, with one command, `file_theorems NAME p "PATH" from B₁, …, Bₙ`, which states `NAME_file` and `NAME_file_decode` for `p.module` and prints their axioms.  The proof of `NAME_file_decode` takes its bytes from the byte theorem `B₁` and contains every `Bᵢ`, so its axiom report covers them all.  The six registry modules built without the reflector have no byte theorem, so their file modules leave `from` out, and the command proves the decoding with `Wasm.Encoding.decode_encode`.  The driver requires both file theorems to report only `propext`, `Classical.choice`, and `Quot.sound`.  The native accuracy checks then compare implementations with integer references over the argument sets stated in each function's document, including the worst inputs of [`WorstCases.lean`](../tests/TestSupport/Numerics/WorstCases.lean).  They also check fused multiply-add, limb arithmetic, and the parser and printer fixtures in `data/strconv/`.

The checks of `Trig`, `Exp`, and `Log` also compare the stored tables with integer references.  `FourierAccuracy.lean` checks impulse and single-frequency transforms, the round trip, Parseval's identity, the power spectrum, and agreement with an exact transform within its stated tolerance.  Each function's document gives its argument sets, measured distances, and proved accuracy bound.

### WGSL tests

`tests/wgsl/run.sh` emits the verified compiler's kernels of [the binary32 example](../Examples/Binary32/Compiled.lean), under the names `scale`, `axpyArray`, `matVec`, and `condMix`, and of [the binary32 GPT-2 compilation](../Demos/Gpt32/Verified.lean) with `tools/EmitWgsl.lean`, which checks each text with the parser.  It computes the cases of [`tests/wgsl/Cases.lean`](../tests/wgsl/Cases.lean) and `Demos/Gpt32/VerifiedGpuCasesMain.lean` with native Lean and runs every case on the SwiftShader and llvmpipe Vulkan drivers with `leanexe-webgpu-host`, comparing each output word.  `tests/wgsl/run.sh --verified` runs the kernels of [the kernel examples](../Verified/Examples/Wgsl.lean) and the binary32 example's kernels under their own names on the cases of [`WgslCasesMain.lean`](../Verified/Examples/WgslCasesMain.lean).  `tests/verified/run.sh --cases wgsl` and `tests/verified/run.sh --cases gpt32` check the Wasm results and allocations of the same functions.  `tests/wgsl/run.sh --leanexe` runs the LeanExe compiler's kernels of the binary32 example and of GPT-2 on the cases of `tests/wgsl/Cases.lean` and keeps them in `build/wgsl-leanexe`, apart from the verified kernels of the same names.  With `--emit-only` the driver writes the kernels and the cases and stops, and with `--drivers-only` it runs ones already written, so that a machine without Lean can run the drivers.

`tests/gpt32/native.sh --verified` emits the verified `gpt32.wasm` and runs small random GPT-2 models through the Lean driver of [`tests/gpt32/VerifiedNative.lean`](../tests/gpt32/VerifiedNative.lean), with the verified kernels, on that module and on both drivers.  It compares every step's scores with native Lean's `step32` bit for bit.  The driver uses the three random-model configurations of [the native cases](../Demos/Gpt32/NativeCases.lean).

### Talos conformance

[The Talos conformance driver](../tests/talos/run.sh) tests Talos, the semantics of the WebAssembly theorems, against the official WebAssembly testsuite at the revision that CodeLib's submodule `vendor/testsuite` records.  It builds the testsuite runner of the pinned CodeLib revision and runs it over the suite, and it fails if the runner records a failed command, an interpreter error, or exhausted fuel.  It then requires the runner's report, one line per command with its outcome, to equal `testsuite_report.txt` at CodeLib's root, the report that Talos's continuous integration checks.  The runner converts each script with `wasm-tools json-from-wast`, so the driver requires the pinned `wasm-tools` 1.251.0.  Lake's checkout of CodeLib leaves the submodule uninitialized, so a first run needs `git -C .lake/packages/CodeLib submodule update --init vendor/testsuite`.

### The full check

The full library includes the numerical proofs and can take several hours.  The lgamma root-range proofs need `--memory-high 10G`, which sets a 12 GiB memory maximum.  The [compilation example](#compiling-and-running) builds only its selected module and imports at the default limits.

[`tools/full-check`](../tools/full-check) runs the full check and writes [`STATUS.md`](../STATUS.md), the record of what holds at the checked commit.  It builds every module of `LeanExe`, `Examples`, `Demos`, `Verified`, `Library`, and `TestSupport` with the test executables, at log level info so that it can count the build's axiom reports, and then runs `tests/verified/run.sh`, `tests/drone/run.sh` and `tests/modules/chunks.py` on the drone and order-book modules that the verified driver writes, the native drivers, `tests/wasi/run.sh`, the bare-metal drivers under TCG, the VKB check, `rocq/check.sh`, `tests/wgsl/run.sh` with and without `--verified`, `tests/gpt32/native.sh --verified`, and [the Talos conformance driver](../tests/talos/run.sh).  A failed build leaves every later step but `rocq/check.sh` and the Talos driver unrun, and the failure of any other step is recorded before the next step runs.  The GPU steps emit their kernels and cases on every machine and run them only where the SwiftShader and llvmpipe Vulkan drivers and `leanexe-webgpu-host` are present, `rocq/check.sh` runs only with `coqc` and a CompCert tree whose proofs are built, and the Talos driver only with `wasm-tools` and CodeLib's `vendor/testsuite` submodule initialized.  The script passes `LEANRUN_THREADS`, `LEANRUN_MEMORY_HIGH`, 10G unless set, `CCOMP`, `CLIGHTGEN`, and `CCOMP_STDLIB` to the drivers, and `COMPCERT_TREE` names the tree for the Rocq step, by default the directory of `CCOMP`.  On a host with about 12 GiB of memory, a cold numerical proof cache first needs the [separate one-worker builds](#memory-heavy-numerical-proofs).  With `LEANRUN_THREADS=8`, `LEANRUN_MEMORY_HIGH=40G`, and `JOBS=8` on AArch64, after a build whose modules were current, the run that `STATUS.md` records took 2 hours and 55 minutes, 58 of them in `tests/verified/run.sh` and 69 in `tests/baremetal/verified.sh`.

After a change to the verified compiler or its examples, `tools/leanrun --threads 2 --memory-high 10G --timeout 12h lake build Verified Library` must finish with no `sorry` warning, and `tests/verified/run.sh`, run with `LEANRUN_THREADS=3` and `LEANRUN_MEMORY_HIGH=10G`, must pass with no failed case.  A new pure compiler fixture needs an import in [`Verified.lean`](../Verified.lean), an entry in [the module registry](../tests/verified/modules.txt), and checked cases.  Reusable algorithm compilations belong in [`Library.lean`](../Library.lean), verified application compilations belong in [`Demos/Verified.lean`](../Demos/Verified.lean), and verified compilations of the LeanExe compiler's examples belong in [`Examples/Verified.lean`](../Examples/Verified.lean), both of which `Verified` imports.  An application port reuses its existing corpus.  Other pure examples add cases to `Verified/Examples/Cases.lean`.  WASI changes also use [the maintained WASI driver](../tests/wasi/run.sh), with its proof and axiom targets, frontend examples, stream fixtures, and host tests.  [The LeanExe compiler manual's full check](leanexe-manual.md#the-full-check) covers the rest of the repository, and [the journal](../devnotes.md) records the counts of each run.

## Examples

[The algorithm index](../index.md) lists the elementary and special functions, software fused multiply-add, limb arithmetic, decimal parsers and printers, and their numerical and byte theorems.  Each numerical function has a document beside its implementation with the proof modules, exceptional values, and limits.

The [compiler fixtures](../Verified/Examples) compile their own definitions or import native programs from `Examples` and `Library`.  A fixture can use `verified_compile` or construct a typed source program directly, as [the tuple example](../Verified/Examples/Tuples.lean) does.  Its byte theorem states that the emitted bytes decode to the module that computes those definitions.

Reusable implementations and their compilations live in [the library](../Library/README.md), and application ports live in [the demos](../Demos/README.md).  The LCG, Park–Miller, and xorshift64 families under `Library/Random/` hold native definitions in `Program.lean`, compilation in `Verified.lean`, and period and other mathematical results in separate proof modules.  [The shared orbit theory](../Library/Random/Orbit/README.md) proves facts about their iterates.

| Example | Contents |
|---|---|
| [`Poly`](../Verified/Examples/Poly.lean) | `a * b + c * c - 7`. |
| [`Mix`](../Verified/Examples/Mix.lean) | Division, remainder, the bitwise operations, and the shifts. |
| [`Lets`](../Verified/Examples/Lets.lean) | Four `let` bindings, the last of them inside an operand of `+`, with a division in its body. |
| [`Select`](../Verified/Examples/Select.lean) | `Bool` bindings, `if` on a `Bool` and on `<`, `>`, and `≠`, a `Bool` parameter, and a `Bool` result. |
| [`Pairs`](../Verified/Examples/Pairs.lean) | Pairs as parameters and results, `.1`, `.2`, and `match` on a pair, a pair inside a pair, calls that pass and return pairs, and patterns that take nested pairs apart on the left and on the right, skip a component, keep a pair whole, take apart a pair built in place, and take apart a triple that holds arrays. |
| [Packed byte values](../Verified/Examples/Bytes.lean) | Identity, duplication, selection, cleanup, swapped results, empty buffers, UInt64 lengths, byte indexing, and construction with captured buffers and nested builders.  [The WASI driver](../tests/wasi/run.sh) checks empty inputs, out-of-bounds reads, allocation/free counts, and oversized construction. |
| [Byte literals](../Verified/Examples/Literals.lean) | Static-pool deduplication, fresh owned copies, empty and conditional literals, ordinary and recursive helpers, and literals inside loop, build, fold, and tree-match bodies. |
| [Array literals and conditions](../Verified/Examples/Forms.lean) | Literals of words, floats, and `Bool`s, a literal as a loop's state, and conjunctions and disjunctions of comparisons in conditions, decisions, the elements of a build, and the conditions of two tail recursions, which [the section on these forms](#array-literals-and-conditions-on-propositions) describes. |
| [Structure patterns](../Verified/Examples/Patterns.lean) | Matches on structures whose patterns fix one field or two to enumeration constructors, fix different fields in different alternatives, fix every field, bind the value, or cover every constructor, on parameters, a structure built in place, a call, a loop's state, and a record that holds an array, which [the section on structure patterns](#structure-patterns) describes, and a pattern that fixes a `Bool` field and a match on word literals, whose rejection messages the example checks. |
| [WASI stdin and stdout](../Verified/Examples/WasiStdio.lean) | `copySome` and closed main of the WASI manual, compiled in callable and command forms.  One read and one write expose errno handling and short-transfer limits. |
| [WASI reflection](../Verified/Wasi/ReflectCommandCases.lean) | Public source-to-export declarations with hidden tables, literals, owned and borrowed bytes, records, computed call arguments, and command main. |
| [`Calls`](../Verified/Examples/Calls.lean) | Four definitions in which `sumSq` calls `sq` and `pick` calls the other three, with a call as an argument of a call and a `Bool`-valued call as the test of an `if`. |
| [Frontend forms](../Verified/Examples/Frontend.lean) | Nested `@[inline]` helpers and `abbrev`s, helper calls in loops and array expressions, listed inline callees, direct array methods, `insertIdx!` with its empty result past the end, empty arrays of words, floats, and records, including a record without an `Inhabited` instance, and Boolean equality, decisions, and conditions with record results, record-array results, and operand calls that consume arrays. |
| [Array folds](../Verified/Examples/Fold.lean) | Words, floats, record elements without an `Inhabited` instance, owned array and pair accumulators, a borrowed initial-state alias, nested folds, calls inside a fold, and the frames condition of a recursive call.  `words_bound` proves the word fold's allocation bound is zero. |
| [Lists of words](../Verified/Examples/Lists.lean) | Construction, identity, duplication, nested calls, matching, head and tail access, reconstruction, and head updates.  Allocation counts check last-use header reuse. |
| [Guarded list recursion](../Verified/Examples/ListRecursion.lean) | Summation, recursive increment with header reuse, and the depth boundary. |
| [List loops](../Verified/Examples/ListLoops.lean) | Construction and extension of list state in word-counted loops. |
| [List tail recursion](../Verified/Examples/ListTail.lean) | Borrowed summation and consumed reversal with header reuse, including chains beyond the guarded call-depth limit. |
| [User-defined recursive values](../Verified/Examples/RecursiveTypes.lean) | Construction, matching, identity, duplication, subtree release, guarded size and increment with header reuse, loop state, tail summation and reversal, and owned right-spine traversal over the existing `Words` and `KeyTree` types, whose conversions and encoding proofs [the `Words` derivation](../Examples/Words/Reflected.lean) and [the `KeyTree` derivation](../Library/Trees/WordTree/Reflected.lean) supply. |
| [Tagged recursive values](../Verified/Examples/TaggedTypes.lean) | Type `Term` with a null constructor and four tagged record constructors: construction, duplication with a copy, matching, guarded evaluation and size, header reuse, subtree release, and tail recursion. |
| [Tail loops](../Verified/Examples/Tail.lean) | Word accumulation, scalar pairs, record arrays, owned growth, swapped and replaced array parameters, aliases, calls between tail functions, and a guarded callee. |
| [Tail conditions and borrowed states](../Verified/Examples/TailConditions.lean) | Boolean and inequality conditions, a proof-named conditional, tuple destructuring, and borrowed pair and record parameters. |
| [Binary64 GPT-2](../Demos/Gpt/Verified.lean) | The unchanged functions of [the GPT example](../Demos/Gpt/README.md), including full-sequence inference, cached steps, and sampling.  The compiler derives each function's execution, allocation-bound, and trap-free theorems and the module's bytes theorem. |
| [Binary32 GPT-2](../Demos/Gpt32/README.md#verified-compiler) | The unchanged kernel functions, with generated Wasm execution and byte theorems, proved WGSL lowering, native dispatch theorems, and the existing host-generation proof instantiated with the new kernels. |
| [Euler solvers](../Demos/Euler/Verified.lean) | Functions of [the Euler example](../Demos/Euler/README.md), with buffered solvers that keep three grids in their loops under the names `solve` and `reconstructedSolve`, and that `solve_eq` and `reconstructedSolve_eq` equate with the example's solvers.  `euler_solve_call` states both calls from the store in which the module starts under a cap of at most 1,563 pages for every grid.  `Demos.Euler.euler_solve_total`, with its 1,407-page bound, applies to the LeanExe compiler's module. |
| [`Loops`](../Verified/Examples/Loops.lean) | Loops over a word, over a pair, and over a pair with a `Bool`, a loop inside a loop, a loop whose body branches, and a loop whose body calls an earlier definition. |
| [`Arrays`](../Verified/Examples/Arrays.lean) | Sums, a dot product, a count, and a search over arrays in loops, reads at computed positions, a pair of arrays passed to calls, and an array chosen by an `if` and bound with `let`. |
| [`Owned`](../Verified/Examples/Owned.lean) | Array results, copies of parameters, owned call results that a reader, a call, a branch, or an unused binding releases, a moved result, a loop whose state is an owned array, a pair of owned arrays taken apart, and arrays built with `LeanExe.build`, one whose element builds and releases an array of its own and one whose element reads an owned array that the code releases after the build. |
| [`Updates`](../Verified/Examples/Updates.lean) | Updates of a parameter, of a built array, of a loop's state, two updates in a row, and an update of an array that stays live. |
| [`Grow`](../Verified/Examples/Grow.lean) | `push` and `++` on parameters, built arrays, and loop states, onto an array that stays live, an array appended to itself, and an owned right operand. |
| [`Modes`](../Verified/Examples/Modes.lean) | Parameters that a function returns, updates, or moves into an owned parameter, also from a loop's state and before a later argument reads the array, and parameters that stay borrowed because the body uses them again.  Its `byHand`, written without the reflector, has an owned parameter that the body never reads and one that it reads last. |
| [`Floats`](../Verified/Examples/Floats.lean) | Piecewise function, scaled hypotenuse, float comparisons as conditions and as `Bool` values, `min`, `max`, negation, loop over a pair of floats, function with a word, a float, an array, and a pair as parameters and a pair result with a float, call of float functions, conversions between words and floats, power of two built from its exponent field, and literal NaN patterns. |
| [Binary32 operations](../Verified/Examples/Floats32.lean) | Arithmetic, comparisons, conditional branches, square root, signs, nearest, unsigned and signed word conversions, bit-pattern conversions, mixed f32/f64 parameters and results, arrays, updates, folds, builds, and tail loops.  Guarded recursion includes a proved 32-position mixed-format frame. |
| [Sums with fields](../Verified/Examples/Sums.lean) | Existing shape program, matches and wildcard bindings, constructors, calls, arrays, updates, folds, loop state, and mixed Float32 and enumeration fields. |
| [Sums with heap fields](../Verified/Examples/HeapSums.lean) | Sum with `Bytes`, array, tree, word, and float fields and sum with a list field: construction from owned arguments, borrowed and owned matches, wildcards that name the matched value, results, pairs, loop state, and guarded call inside a match. |
| [Trees with buffer fields](../Verified/Examples/BufferTrees.lean) | Tree whose records hold a byte buffer beside a word and two children: construction from owned and borrowed buffers and from the empty buffer, owned matches that move the buffers out and release those that die, borrowed reads of a buffer's bytes and size, and copies of a borrowed tree that copy each record's buffer. |
| [Trees with array fields](../Verified/Examples/ArrayTrees.lean) | Tree whose records hold an array of words beside a word and two children: construction from owned and borrowed arrays, owned matches that move the arrays out and release those that die, borrowed reads of the arrays' elements, record reuse, and copies of a borrowed tree that copy each record's array. |
| [Trees with typed fields](../Verified/Examples/TypedTrees.lean) | Tree with `Bool`, binary64, binary32, and word fields, tree whose records hold a structure with a nested structure, tree with an enumeration field, and tree with a sum field: construction, copies, record reuse, borrowed reads, matches on the sum, recursion, loops, and functions that take or return the fields. |
| [`Records`](../Verified/Examples/Records.lean) | Structures with a nested structure and a `Bool` field, built, updated with `{ s with … }`, read field by field, taken apart with `match`, chosen with `if`, passed to calls, and used as a loop's state, with theorems stated for the structures. |
| [`Tuples`](../Verified/Examples/Tuples.lean) | Arrays of tuples of a float and a word and of a nested tuple, built, read along a path, updated in place, extended, and appended, written without the reflector, with an `example` per function stating by `rfl` that it means a Lean function. |
| [`Grids`](../Verified/Examples/Grids.lean) | Arrays of the structures of `Records.lean`, built, read element by element and field by field, also past the end, updated in place in a loop, extended with a new structure, appended, counted, reduced to a total and a `Bool`, and returned in a pair with a total, and a local array of pairs. |
| [`Repeat`](../Verified/Examples/Repeat.lean) | `LeanExe.repeatWhile` over words, a float, pairs that hold arrays, and a structure, stopping early under fuels up to `2 ^ 64 - 1`, with a condition that reads an owned array of the state and a step that updates it in place, and loops over literal data inside a pair result, under a `match`, behind a call with literal arguments, and in a closed term. |
| [`Enums`](../Verified/Examples/Enums.lean) | Four enumerations, flattened by `ctorIdx`, by a `match`, by a constant for the one with a single constructor, and by a `match` to the words 0 and 200, as parameters, results, a structure field, a loop state's field, and array elements, with `match` that has a wildcard binding the value, `match` on an array element, `==`, `!=`, `decide`, and `if` on enumerations, and an update in place. |
| [`Recursion`](../Verified/Examples/Recursion.lean) | Recursion once and twice per call over words, floats, a pair, a structure, an array of structures, and an owned array that each call extends and moves into the next, a function that calls two recursive ones, a recursion that returns at depth 999 and traps at depth 1,000, a recursion that calls another, and `spread`, which calls them inside a loop, a build, a `repeatWhile` condition, a destructured pair, an update, the argument of a function without the call depth, and conditions on a `Bool`, a float, and `≠`, with the theorems `chain_fits`, `chain_trapFree`, `fill_fits`, `fill_cost`, and `fill_trapFree`. |
| [`Fields`](../Verified/Examples/Fields.lean) | Records with array fields, built, read field by field and element by element, also past the end, updated with `{ r with … }` on a borrowed parameter and, in place, in a loop's state, passed to a call, taken apart with `match`, chosen with `if`, returned in a pair, and held in another record, with a `Flat` instance written as a pattern, a loop that extends a field's array, and bound equations that name the fields. |
| [`Trig`](../Library/Numerics/Float64/Trig/Program.lean) | `sin` and `cos` ported from fdlibm, with its reduction by multiples of `π/2` below `2 ^ 20 · π/2`, a Payne–Hanek reduction in word arithmetic above, after Go's `math.trigReduce`, which reads the bits of `2/π` and `π/2` from tables so that no call allocates, `sinWith` and `cosWith` with the tables as parameters and `sin` and `cos` as wrappers, with theorems that allow no trap, and fdlibm's minimax kernels, written with the constants' bit patterns. |
| [`Fourier`](../Library/Numerics/Fourier/Program.lean) | Discrete Fourier transform of a signal of interleaved complex floats by the `n²` products of the definition, its inverse, and power spectrum of real samples, with factors from `Trig.cosWith` and `Trig.sinWith`, compiled in the same program, with Trig's tables passed by the wrappers `dft`, `inverse`, `powerSpectrum`, and `twiddle`. |
| [`Exp`](../Library/Numerics/Float64/Exp/Program.lean) | `exp` ported from Arm's optimized-routines, with its table of 256 words in a data segment, `expWith` with the table as a parameter and `exp` as its wrapper, and the paths for results that overflow or underflow. |
| [`Tanh`](../Library/Numerics/Float64/Tanh/Program.lean) | `expm1` and `tanh` ported from fdlibm, with fdlibm's signed reduction count represented as a sign and a magnitude. |
| [`Log`](../Library/Numerics/Float64/Log/Program.lean) | `log` ported from Arm's optimized-routines, with two tables of 256 words in data segments and `log` as the wrapper that passes them. |
| [`Tables`](../Verified/Examples/Tables.lean) | Two tables read by wrappers, in range and past the end, and an owned array updated and extended from a table, with the theorem `pushSquare_bound` for a wrapper whose callee has a paid parameter. |
| [`Insert`](../Verified/Examples/Insert.lean) | `LeanExe.insertAt` and `LeanExe.eraseAt` on parameters, built arrays, an array that stays live, a loop's state in an insertion sort and in a removal loop, a local array of pairs, and arrays of structures, also past the end. |
| [`Clob`](../Demos/Clob/Verified.lean) | Bid side of an order book, as two arrays of prices and sizes, with insertions and removals of levels in place, a market buy, cancellations, and command streams, and the theorems that a stream run in two chunks gives the book of one run and that `runOut` leaves the book of `runCommands`. |
| [`Drone`](../Demos/Drone/Verified.lean) | Drone planner of [`Demos/Drone`](../Demos/Drone/README.md), compiled unchanged, with its named constants reflected as their values, and the theorems `drone_compute` and `drone_safe`, from the planner's `compute_correct` and `compute_safe`, that the module's results are optimal and safe flights, and `drone_trapFree`, from `compute_bound` on `compiled.compute.bound_eq`, that the module computes `compute` without a trap whenever `top` can rise by 2,251,064 bytes within the memory's cap. |
| [`Slew`](../Demos/Slew/Verified.lean) | Slew planner of [`Demos/Slew`](../Demos/Slew/README.md), which plans rest-to-rest eigenaxis rotations of a spacecraft under cone constraints through a graph of waypoint attitudes, compiled with the library's `atan` and `atan2` into one module, with the generated `implements`, `trapFree`, and bytes theorems, and [`slew_trapFree`](../Demos/Slew/Bound.lean), from `plan_bound` on `compiled.plan.bound_eq`, that the module computes `plan` without a trap whenever `top` can rise by 68,020,488 bytes within the memory's cap. |
| [`Elements`](../Verified/Examples/Elements.lean) | Sum, dot product, and maximum over arrays of floats, grid built from converted indices, `axpy` that updates an owned array of floats in place, extension, flags of negative elements, count and selection by flags, update and push of an owned array of `Bool`s, and sieve of Eratosthenes. |
| [`Lcg`](../Library/Random/Lcg/Verified.lean), [`ParkMiller`](../Library/Random/ParkMiller/Verified.lean), [`Xorshift`](../Library/Random/Xorshift/Verified.lean) | Generators of [`Library/Random/Lcg`](../Library/Random/Lcg/README.md), [`Library/Random/ParkMiller`](../Library/Random/ParkMiller/README.md), and [`Library/Random/Xorshift`](../Library/Random/Xorshift/README.md), compiled unchanged, with the theorems `lcg_advance`, `parkMiller_advance`, and `xorshift_advance`, which combine each module's bytes with the generator's theorems about `advance`, and `lcg_jump` and `xorshift_jump`, which state that the modules' jump-ahead functions compute `advance`, the second when `top` can rise by 36,920 bytes, by `jump_bound`. |
| [`Gcd`](../Library/Numerics/Arithmetic/Gcd/Compiled.lean), [`PrimeFactors`](../Library/Numerics/Arithmetic/PrimeFactors/Compiled.lean), [`Mean`](../Library/Numerics/Statistics/Mean/Compiled.lean), [`SumSquares`](../Library/Numerics/Statistics/SumSquares/Compiled.lean), [`SplitMix64`](../Library/Random/SplitMix64/Compiled.lean) | Library programs of the LeanExe compiler, compiled unchanged, with `gcd_call` and `primeFactors_call`, which compose the generated store-preserving theorems with `gcd_eq` and `compute_eq`, and `prng_module`, which combines the module's bytes with the store-preserving theorems of `splitMix` and `unitFloat`. |
| [`Lookup`](../Examples/Lookup/Compiled.lean), [`TreeLookup`](../Examples/TreeLookup/Compiled.lean), [`Increment`](../Examples/Increment/Compiled.lean), [`Below100`](../Examples/Below100/Compiled.lean), [`RemoveZero`](../Examples/RemoveZero/Compiled.lean), [`Binary32`](../Examples/Binary32/Compiled.lean) | Examples of the LeanExe compiler, compiled unchanged, with `lookup_call`, `treeLookup_call`, `increment_call`, `below100_call`, and `removeZero_call`, which compose the generated trap-free theorems with the examples' specification theorems through `Examples.arrayCall` of [the shared call theorem](../Examples/ArrayCall.lean), and the WGSL kernels of `scale32`, `axpyArray32`, `matVec32`, and `condMix32` with dispatch theorems under the premises of the LeanExe compiler's kernels. |
| [`Scale`](../Examples/Scale/Compiled.lean), [`SumArray`](../Examples/SumArray/Compiled.lean), [`SumCount`](../Examples/SumCount/Compiled.lean), [`PairSum`](../Examples/PairSum/Compiled.lean), [`ScaledHypot`](../Examples/ScaledHypot/Compiled.lean), [`Piecewise`](../Examples/Piecewise/Compiled.lean), [`Axpy`](../Examples/Axpy/Compiled.lean), [`Bucket`](../Examples/Bucket/Compiled.lean), [`Bools`](../Examples/Bools/Compiled.lean), [`Lists`](../Examples/Lists/Compiled.lean), [`Updates`](../Examples/Updates/Compiled.lean), [`Grids`](../Examples/Grids/Compiled.lean), [`Calc`](../Examples/Calc/Compiled.lean) | Examples of the LeanExe compiler, compiled unchanged, whose LeanExe theorems state only that the module computes the Lean function, which the generated theorems also state.  `Bools`, `Grids`, and `Calc` take the `Flat` instances of their `Flat.lean`, and the registry names the modules of `Lists`, `Updates`, and `Grids` `exampleLists`, `exampleUpdates`, and `exampleGrids`.  The reflector reads the structure patterns of `Calc.undo`, which fix the field `last`, as tests of its word. |

## From an English request

[The verified-request skill](../.claude/skills/verified-request/SKILL.md) directs an agent from a request in English to a program of this compiler and a call theorem that the module's export returns, without a trap, the value of a specification reviewed against the request.  Its first stage produces the specification `expected`, its samples, and a review by a fresh agent that sees only the request, the specification, and the samples.  The agent then writes the program, `compute_eq` in a module that imports only the program, the specification, and lemmas about the dialect, and the call theorem `compute_callSpec`, which composes `compute_eq` with the generated `trapFree` theorem through `Verified.ImplementsTables.call` and `Verified.Call.spec` of [the call theorem](../Verified/Call.lean).  The skill covers parameters of `UInt64`, `Array UInt64`, or tuples of these, and results of `UInt64` or `Array UInt64`, which `Verified.CallSpec` covers through `Represent`.

[`tools/verified-request-check`](../tools/verified-request-check) accepts or rejects the result.  `--spec NAME` prints each sample with the specification's output, `--freeze NAME` records the hashes of the reviewed `Spec.lean` and `Samples.lean`, and `--run NAME` emits `compiled.module` with [the module emitter](../tools/Emit.lean) and runs the samples in Wasmtime without proofs.  Both `--run` and the check first refuse a run whose Lean files declare a global or scoped instance, notation, macro, syntax, or elaborator, or code that runs at import, since the check elaborates its statement with the run's modules imported, and each refusal names the file and line.  Without a flag, it checks the hashes of the reviewed specification and samples, writes the statement `Verified.CallSpec compiled.module compiled.tables K expected compiled.compute.bound` for the export's index `K`, and requires `compute_callSpec` to prove it with no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`.  It proves in the kernel that the export is function `K`, emits `build/verified-request/NAME/NAME.wasm`, and runs the samples in Wasmtime against `expected`.  When `ccomp` and `clightgen` are found, it also builds the module's translation to C with `native-verified build`, as [the native driver](../tests/native/verified.sh) does, and runs the samples in the native program.

## Development practice

### `tools/leanrun` and the shared lock

Every `lean` and `lake` command runs through [`tools/leanrun`](../tools/leanrun), as [the repository instructions](../AGENTS.md) require.  The runner limits memory and CPU time through a systemd user scope, sets `LEAN_NUM_THREADS`, and holds a lock in the directory that `LEANRUN_LOCKDIR` names, by default one for each user of the machine, so that one runner command runs at a time and other sessions wait for the lock.  `--timeout` sets the command's limit and `--lock-timeout` the seconds to wait for the lock, 900 by default.

`--threads N`, 1 by default, sets `LEAN_NUM_THREADS=N`.  Lake takes its number of parallel build jobs from `LEAN_NUM_THREADS`, and each Lean process it starts uses the same value for its own tasks, so parallel jobs share the scope's memory limit.  `--cpus N` sets a CPU quota of `N` CPUs, and `--cpus auto` uses every online CPU.  Without `--cpus` the quota equals the thread count, and without `--threads` the thread count equals the `--cpus` count.  `LEANRUN_THREADS` and `LEANRUN_CPUS` supply these settings to repository drivers without wrapping them in another runner.

`--log FILE` writes standard output and standard error to a file and preserves the command's exit status.  Passing the path as an argument keeps `tools/leanrun` as the first command token, so saved runner permissions cover later targets and logs.  The default memory limits are 4 GiB high and 6 GiB maximum, and `--memory-high SIZE`, in whole gibibytes such as `10G`, selects the high limit and a maximum 2 GiB above it.

```sh
export PATH="$HOME/.elan/bin:$PATH"
tools/leanrun --timeout 30m --lock-timeout 1200 lake env lean FILE
```

After a target reaches its timeout without a diagnostic, [the repository instructions](../AGENTS.md) require dividing it, or adding a reusable lemma that reduces its elaboration, before running it again.  `LEANRUN_LOCAL=1` runs without the cgroup limits and only with the user's explicit authorization.  [`tools/leanrun-dev`](../tools/leanrun-dev) runs Lean on the remote machine that `LEANRUN_DEV_HOST` names, with the modes `sync`, `check`, or a command.

`lake env lean FILE` loads the existing build of each import without rebuilding it, so a check of a file whose imports changed must follow `lake build` of those imports.  `lake build` of a target rebuilds the imports whose sources changed.  [The journal](../devnotes.md#2026-10-05-organization-of-the-branch) records a check that passed against the stale builds of modules whose sources had been renamed, until it imported the old and the new module together.

### Memory-heavy numerical proofs

Some gamma and lgamma range checks need several gibibytes each.  On a host with about 12 GiB of memory, a cold numerical proof cache uses the following one-worker builds before the two-worker aggregate of [the full check](#the-full-check).  Each target has a separate invocation, which bounds the working set to one heavy proof and its imports, and the aggregate reuses the accepted results.

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

The 12-hour limit accommodates cold imports.  The measured leaf checks used 30-minute limits after their common imports had been built.  [The journal](../devnotes.md#2026-10-24-integration-checks) records their results.

### Repository rules and iterative development

[The repository instructions](../AGENTS.md) set the procedures that bind agents in this repository: the runner and its limits, the approval boundaries for repository drivers, the gates and the review of a proof iteration, and the proposal of VKB entries after a proof task.  [The style guide](../CLAUDE.md) sets the style of prose, comments, and commit messages.  Python tools declare their dependencies as PEP 723 metadata and run with `uv run`.

[The design document](design.md) gives the design, the decisions with their reasons, what is proved and tested, and the open work.  One of its decisions for both compilers makes development iterative: each iteration takes one program from Lean source to bytes, a proved `Implements`, a Wasmtime comparison with native Lean, an axiom audit, and a commit, adding only what that program needs.  [The journal](../devnotes.md) records each step in dated prose: the analysis, the options, the decision, what was built, and the measurements.

### Documentation links

Every Markdown document and prose README has a path of links from [LeanExe](../README.md).  Link text names the destination's subject, and the surrounding sentence explains the reason for the reference.  Current repository references use relative paths.  A historical reference carries the revision to which its claims apply in its link's URL, and no commit hash of this repository appears in the text.  Links to documentation lead to a file or a directory with a README, and links to source directories support code browsing.

A `References` or `Internal References` section lists the sources whose content a document uses, and an internal document appears there only when the text does not link it at the point of use.  Each item is a citation or a link titled with the destination's title and, for a section, its heading, and items contain no sentences.  One paragraph after the list may discuss the references when the body does not state that information: what was read or checked, peer-review status, the license of ported code, or a difference between a source and the implementation.  A directory README explains how its files work together, the assumptions they share, or how to build, test, or use them.

[The documentation checker](../tools/check-doc-links.mjs) checks local targets, heading anchors, and reachability from the root README.  It reads Git's tracked and unignored untracked files, so that drafts can be checked before staging, and [the documentation tests](../tests/README.md#documentation-tests) exercise its parsing and traversal on temporary files.  [The style guide](../CLAUDE.md#review-process) requires at least two passes of its review over a document: openings and puffery, filler words, passive constructions and weak verbs, jargon, redundancy and vague references, and grammar.
