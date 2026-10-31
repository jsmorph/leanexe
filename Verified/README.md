# Verified Compiler Internals

The verified compiler consists of a typed source language, a Lean function that compiles it, and
a universal correctness proof.  `verified_compile` reflects ordinary Lean definitions into that
language and derives their execution theorems.
[The verified compiler manual](../docs/verified-manual.md) describes the dialect, the declarations
that the command adds, the bounds, the tests, and the examples for a program's author.  The library
shares the trusted base and the statement of correctness with `LeanExe`: Talos's semantics, the
encoder and decoder with `decode_encode`, `Implements` and its relatives in
[`LeanExe/Pipeline/`](../LeanExe/Pipeline), and the runtime.  The statements add definitions of
their own: `Heap.Within` in [the runtime rules](RuntimeFacts.lean), the allocation bound of
[`Bound.lean`](Bound.lean), `ImplementsTables` for wrappers, and `initialHeap` and `tableAddr` for
the initial store.  Native algorithm definitions live in
[the library](../Library/README.md), compiler fixtures in `Verified/Examples`, and application
compilations in [the demos](../Demos/README.md).  Separate compilation and mathematical proof
modules import the compiler or proof rules they use.  The proofs use only the axioms `propext`, `Classical.choice`, and
`Quot.sound`.

## Source language and code

A program is a list of functions in which each function may call the functions after it in the list
and, when it is recursive, itself, so the only cycles are a function's calls of itself.  The list
holds the definitions of a `verified_compile` command in reverse order, so that a definition calls
the definitions before it in the command.  A function's body is a typed expression.

### Types and expressions

The element types, `Elem`, are 64-bit words, `Bool`s, binary64 and binary32 floats, and tuples of
element types.  `Ty.elem e` embeds an element type, `Ty.array e` holds an array of elements, and
`Ty.pair` combines any two value types.  `Ty.bytes` denotes `LeanExe.Bytes`.
`Ty.tree shape` holds a recursive value with the fixed
layout `shape`, and `Ty.treeHeader shape r` holds the detached header of a record of constructor
`r` during matching and reuse.  The reflector represents `List UInt64` and supported user-defined recursive types through
this tree model.  An expression of type `t` over a context `Γ` that may call functions with
signatures `S` has type `Expr S Γ t`, so every expression is well typed, reads only variables in
scope, and calls only functions that exist.  The constructs are those of [the manual's
dialect](../docs/verified-manual.md#the-dialect), each with Lean's meaning, with tuples built by
`Expr.mk` and read by `Expr.proj`, which follows a path of first and second steps from a tuple
variable.  A binary64 operation has the meaning of Lean's `Float`, which
[`F64Bits.lean`](../LeanExe/ProofKit/F64Bits.lean) proves equal on bit patterns to Talos's `IEEE64`
functions, the semantics of WebAssembly's f64 instructions in the deterministic profile, in which
every NaN result is the canonical NaN.  The source expresses `LeanExe.loop` and
`LeanExe.repeatWhile` with one loop that tests a condition on the state before each pass and leaves
when it fails: `LeanExe.loop` is the loop whose condition is `true`, and `LeanExe.repeatWhile` the
one whose body ignores the index.  A variable is numbered by its distance from the front of the
context: a binding's value is variable 0 of its body, parameter `i` is variable `i` of the
function's body, a loop's condition has the state as variable 0, its body has the state as variable
0 and the index as variable 1, and a build's element has the index as variable 0.  The size, the
read, the update, and the extensions take array variables, and a call's argument that holds arrays
is a place, a variable or a pair of places, and a variable at an owned parameter.

### Values and ownership

A value is carried as words, as `Implements` passes it: a word as itself, a `Bool` as 1 or 0, a
float as its bit pattern in an f64 or f32 word, a tuple or a pair as its first component's words
followed by its second's, and an array as the address of its length word and its elements' words
in memory.  An element of `k` words occupies `k` consecutive eight-byte words, with a `Bool` as
1 or 0 and a float as its bit pattern.  A Float32 pattern occupies the low 32 bits of its word.
The length word counts words.  `Elem.words` gives these words, the identity for an array of
words, as Lean's instances for `Array UInt64`, `Array Float`, `Array Float32`, and arrays of `Flat`
types such as `Bool` store them.  Lean has no instance for an array of tuples, and `Elem.wordsInst`
stores one in the same way.  `Elem.typed_words` states that decoding an element's words into
typed values and extracting their bits recovers those words.  The word-store proof uses this
equation for both float formats and tuples.  A structure whose `Flat` tuple holds arrays is represented as that tuple, by
the instance `instRepresentOfFlat` of [`FlatRecords.lean`](../LeanExe/Pipeline/FlatRecords.lean),
and the reflector treats it as a pair whose components are the tuple's.  Such a record may be a
parameter, a result, a local value, or a loop state.  A parameter of a record with array fields is
borrowed, so a callee that updates one of its arrays copies the array.  A function with a pair result
returns several WebAssembly results.  Each value holds its arrays in a mode, borrowed or owned, which
`Expr.mode` computes from the modes of the variables.  A function's signature gives each array
parameter a mode.  The function reads a borrowed parameter and leaves it in place, and it consumes
an owned parameter's array, releasing it at entry when the body does not use it.  A call's result, a
function's result, and a built, updated, or extended array are owned, so a function copies a
borrowed value that it returns.  Each expression consumes the owned variables that die in it, those
live before it and not after: an owned variable moves into the value where it dies and is copied
where it stays live, a reader or a call releases an owned variable that dies there, and a branch, a
binding, and a loop release the owned variables that die without a use.  Recursive values also have
borrowed and owned modes, with copying, release, and reuse described [below](#recursive-records).
The code generator learns which variables each subexpression reads from the bitmask `Expr.useMask`
through `Expr.usesFast`, and `Expr.usesFast_eq` equates it with `Expr.uses`.  A pair has one mode, and a
loop's state is owned when its initial value or its body's value is owned, so a borrowed component
or state is copied.  An array copy allocates through the runtime's `alloc` and writes the length word and
the elements.

A byte value occupies two i64 words: its allocation root and logical length.  Borrowed bytes
protect the allocation's header and full capacity.  An owned copy allocates a packed payload
without an array-length word.  Copying empty bytes returns `(0, 0)` without allocating.  A valid
incoming empty buffer may have a nonzero root, which cleanup releases.  The
[byte examples](Examples/Bytes.lean) cover parameters, results, duplication, branches, cleanup,
empty values, UInt64 lengths, and indexed reads.  An out-of-bounds read returns zero.  Length and
index operations release an owned input at its last use.  `Expr.bytesBuild` allocates a packed
result and stores each callback's low eight bits.  Its proof carries live captures, callback
allocation bounds, and separation through the loop.  Zero count skips allocation and callbacks,
and counts of at least `2^32` trap before allocating the result.  The [WASI compiler](../docs/wasi.md)
uses these buffers for stdin, stdout, and stderr.

`bytes![65, 0, 255]` reflects to `Expr.bytesLiteral`.  The macro accepts numerals from 0 through
255.  Each evaluation of a nonempty literal copies its static source bytes into a fresh owned
allocation.  An empty literal returns `(0, 0)` without allocating.  [Literal expression correctness](AlignedBytes.lean)
uses the shared byte allocator and copier, preserving the packed-buffer representation and its
48-byte header.  The allocation bound charges `Bytes.allocationCost bytes.length` at each
evaluation, including each loop iteration or callback invocation.  [The literal examples](Examples/Literals.lean)
cover ordinary, guarded, and tail helpers, nested byte indices, and build, fold, and tree-match
bodies.

### Scalar code and control flow

A function's locals are its parameters, an i64 local for each further position, and
f64 and f32 locals for every position.  Each word occupies the local for its type.  A function
copies floating-point parameters to their typed locals at entry.  Arithmetic reflection selects
binary32 or binary64 from the operand type.  Negation subtracts the operand from negative zero in
its format, matching Lean's result on every input, including canonical NaN.
`Float.ofBits` compiles to `f64.reinterpret_i64` followed by the addition of −0, which gives the
canonical NaN for a NaN pattern and leaves every other float unchanged.  A float constant's code
holds its canonical bit pattern, which the compiler computes with integer operations, so the bytes
that `tools/Emit.lean` writes by evaluating the compiler natively do not depend on Lean's native
float code.  Each binding's value is stored in positions of its own, and a call pushes its
arguments' words in order and calls the function, which the module places before its callers.  An
argument at an owned parameter moves its variable into the call when the variable is owned, dies at
the call, and no other argument with arrays reads it, and is copied otherwise.  Every argument's
variables stay live until the call, so a later argument may read a moved array, and the call then
releases the owned variables that die there and that it does not consume.  An `if` stores the words
of its value in locals in each branch and loads them after it, because the encoder writes block
types of at most one result.  A loop keeps its count, its index, and its state in locals, compares
the index with the count at the top of a WebAssembly `loop` inside a `block`, and branches out of
the block when the index reaches the count.

### Array code

A build keeps its count, the array's address, and the index in locals.  It traps at `unreachable`
when the count's words would be `2^29` or more, since the
array would not fit in 32-bit memory, allocates the array and writes its length word, and stores
each element after the element's code runs.  The outer variables that only the element reads stay
live through the loop and are released after it.

An update runs its position's and value's code
first and then takes the array in an owned position: an owned array that dies there is updated in
its own block, and any other array is copied first.  An extension takes the array with room for the
result: an owned array that dies there grows in its own block when the block has room and otherwise
moves to a block of at least twice its capacity, which releases the old block, and any other array
is copied once into a block with room.  `push` then writes the new element, and `++` copies the
other array's elements after the first's and releases the other array when it is owned and dies
there.

An insertion takes the array with room for one more element in the same way, moves the words
from the position to the end up by one element, from the last word down, and writes the new element
at the position.  A removal takes the array as an update does, moves the words after the element
down by one element, from the first word up, and writes the shorter length.  Each move stays inside
one block, and its order reads every word before it overwrites it.  The primitive `Expr.insertAt`
returns the input value past the end after its ownership and capacity handling.  `Expr.insertIdx`
checks the length first and selects an empty build past the end, preserving `Array.insertIdx!`.

A read keeps the position in a local, compares it with the array's size, the length word divided
by the element's word count, and keeps the result as a flag.
It then loads each of the element's words under the flag, 0 past the end.  A binary64 read uses
`f64.reinterpret_i64`; a binary32 read wraps the word to i32 and uses `f32.reinterpret_i32`.
An update, a push, and a build store the element's words in locals and write each.  Binary64 stores
use `i64.reinterpret_f64`; binary32 stores use `i32.reinterpret_f32` and zero-extension to i64.
The code uses `min k 2^29` as the word count `k` of an element: an element of `2^29` words or more is in no array that
memory holds, and the bound keeps the count positive and below `2^64`.  WebAssembly traps on a zero
divisor, so the compiled division and remainder save their operands in scratch locals, test the
divisor, and return Lean's result for zero.

[`Source.lean`](Source.lean) defines the syntax and
`Func.denote`, [`Compile.lean`](Compile.lean) the compiler, [`State.lean`](State.lean) the
representation of values in the heap and the facts about variables, [`Heap.lean`](Heap.lean) the
specifications of the allocation, copy, and release code, [`Bound.lean`](Bound.lean) the allocation
bound, [`Potential.lean`](Potential.lean) the potential of owned arrays, and [`After.lean`](After.lean)
the facts that the proof shares.  [The expression specification](ExprSpec.lean) defines `CodeSpec`
and proves the shared call, budget, and operand-sequencing rules.  [The binary32 rules](AlignedFloat32.lean)
prove arithmetic, comparisons, unary operations, and word conversions.  [The expression rules](ExprCorrect.lean) prove expression and
ordinary-function compilation, and [the program theorem](Correct.lean) combines the function
rules.  The compiled module has the layout of `LeanExe`'s modules, with the runtime's `alloc`
and `release` at functions
0 and 1.

### Folds and checked insertion

`Expr.fold` has the full `Array.foldl` meaning, with its element, accumulator, and `UInt64`
index as variables 0, 1, and 2 of its body.  The reflector accepts whole-array folds and
leaves the index unused.  [The fold proofs](ArrayFold.lean) equate the source operation
with `Expr.foldExpand`, a word-counted loop that reads each element before its body.
`Ty.Rep.array_size_lt` derives the required size bound for every represented element type
from the flattened array's heap bound and positive element width.  `Cases.spec_fold`
composes the existing size, read, binding, and loop rules.  The expansion has the same
code, liveness, mode, allocation bound, frames condition, and local width as the fold.
[The reflection lemmas](Reflect/FoldLemmas.lean) express its allocation and frames
conditions with `foldCost` and `foldFits` on the user's array and accumulator types.
`Expr.foldLoop` and [variable renaming](Rename.lean) also give a loop construction for a
body that takes only the element and accumulator.

`Expr.insertIdx` composes a logical length comparison, the existing insertion, and an empty
build to implement `Array.insertIdx!`, including its `#[]` result beyond the end.  The typed
predicate `Expr.leSize` compares a word index with the array's full logical length.  Its
compiled comparison uses the word-sized length, justified by `Ty.Rep.array_size_lt`.
[The insertion equations](InsertIdx.lean) relate this comparison to the existing comparison
rule, and `Cases.spec_leSize` reuses that rule's ownership, release, and allocation proof.

## Recursive records

The [tree model](Tree.lean) has a null value and records with a fixed layout of at most 64 slots.
Each field is a child with the same layout or a word field, `TreeField.word e`, that holds an
element `e` of one word: a `UInt64`, a `Bool`, or a float of either width.  `TreeShape.kinds r`
lists the fields of record constructor `r`, and `TreeShape.fields r` maps them to the child bits
that `Node`, the release and copy loops, and their proofs read.  `Tree.node` takes its words as a
family typed by `TreeShape.elem`, which reduces to `Elem.word` when every field of the shape is a
`UInt64` word or a child (`TreeShape.allWords`), so the words of a list and of such a type have type
`UInt64`.  A load converts a slot's word with `ofWordCode` into a local of the element's slot type,
and a store converts with `toWordCode`.  Both are empty for a `UInt64` and a `Bool`, so a field of
either type needs no conversion instructions.  The model proves the conversion laws for `List
UInt64` and uses the shared runtime's record encoding.

The [copy theorem](AlignedTreeCopy.lean), `wp_copyTree`, covers every borrowed value with that layout.
It proves termination, ownership and pairwise separation of the copied records, preservation of
every initial heap region and the memory caps, and an allocation bound of `N * (48 + 8 * w)`
bytes for `N` records of `w` fields.  It permits a trap at `unreachable` only when that bound
does not fit within the memory cap.  The emitted loop uses six scratch locals.  It keeps parent
links, source pointers, and slot indices in new headers, restoring each completed header before
returning to its parent.  Its decreasing traversal measure and allocation count belong to the proof.

[Header detachment](TreeDetach.lean) and [attachment](TreeAttach.lean) preserve child ownership
across the mask changes needed for record reuse.  The [release rules](TreeRelease.lean) apply the shared release
runtime to a whole owned tree or a detached header and prove that `top` stays unchanged.
[Detached-header copying](AlignedTreeHeaderCopy.lean) allocates one record, sets its kind and width,
and retains the allocator's zero child mask.  Its arbitrary payload words represent no children.
The bound charges `48 + 8 * w` bytes for a header of `w` fields.
[Field stores](TreeFieldsStore.lean) write local values to consecutive payload slots, and
[field loads](TreeFieldsLoad.lean) recover them in distinct locals while preserving the frame.
[Payload writes](TreeFieldsState.lean) preserve the allocator invariant, capacity, and header words.
[Field locations](TreeFieldLocs.lean) and [field values](TreeFieldValues.lean) relate the grouped
word and child locals to their physical order and establish ownership of the stored slots.

[Field evaluation](FieldsExpr.lean) proves the ordered evaluation and local storage of fields,
including owned coercions, pairwise block separation, preservation of live variables, and the
combined allocation bound.  [Owned value lists](OwnedValues.lean) and
[field ownership composition](FieldsAfter.lean) preserve completed fields as later fields execute.
[Field advancement](FieldsAdvance.lean) preserves those results through a further heap step.
[Variable correctness](AlignedCorollaries.lean) proves reading, moving, and copying a variable.
[Context composition](ContextAppend.lean) combines represented variable contexts and removes a
prefix of bound variables.  [Binding composition](BindPrefix.lean) composes a value's execution
with a body that binds any number of fields.  [Field positions](TreeFieldPositions.lean) relate
each packed word or child field to its assigned local.
The binding rule also accepts an initial heap step whose consumed value has been decomposed
into fields.  The field-load rule preserves the operand stack.
[Tail binding composition](TailBindPrefix.lean) removes a field prefix after a return or
continuation, preserving the remaining parameter or result ownership and the state frame.
`TailCodeSpecAt` fixes the input environment, and `TailCodeSpec` quantifies over that environment.
[Release before tail execution](AlignedTail.lean) drops unused variables and composes the
remaining body's allocation bound.
[Expression coercion](OwnedExpr.lean) preserves an expression's execution facts as its result
mode changes.  [Release and coercion](AlignedTreeMatch.lean) adds release of unused variables and
accounts for the allocation allowance of the remaining expression.
[Context equalities](ContextHEq.lean) preserve the environment and execution facts when
equivalent context expressions have different associations.  [Child-region enumeration](TreeMatchBlocks.lean)
relates a record's packed child slots to the grouped child bindings' blocks and read regions.
The [owned-expression rule](OwnedExpr.lean) combines expression correctness with result coercion.
[Field grouping](FieldsArgs.lean) relates the constructor's finite word and child families to
the typed argument list.  [Record assembly](TreeAssembleCode.lean) composes payload stores and
header writes, preserving child ownership and proving the completed record's exact block list.
[Local-state rules](LocalFrame.lean), [heap steps](HeapStep.lean), and [runtime rules](RuntimeFacts.lean)
give these proofs interfaces independent of the source language.

The source types `Ty.tree` and `Ty.treeHeader` record the layout.  The [constructor
rule](AlignedTreeBuild.lean) composes field evaluation, parent allocation or reuse, and record
assembly.  The [matching rule](AlignedTreeCase.lean) handles null and nonempty values, loads the
fields, detaches an owned header, releases unused bindings, and composes the branch's ownership and
allocation bound.  Both rules enter `Expr.code_spec` and the whole-program correctness theorems.
Borrowed aliases retain their regions, and moving or copying a recursive value uses its exact record
blocks at the current store.  The reflector supports `List UInt64` construction, matching, identity,
duplication, tuples, and calls.  [Representation agreement](TreeAgree.lean) proves that borrowed and
consumed lists use the typed tree's encoding.  The [list example](Examples/Lists.lean) derives
execution theorems for ordinary Lean definitions.  The [match equations](Reflect/TreeLemmas.lean)
preserve both branch meanings and their allocation and frames conditions.  [Matcher
normalization](Reflect/NativeList.lean) derives the equation from Lean's elaborated match to its two
list cases, which the kernel checks with the generated theorem.  The [tail-match
rule](AlignedTailTree.lean) enters `TailBody.code_spec` and the whole-loop theorem.  Its branches
preserve the enclosing loop's return and continue labels.  The [recursive-tail
reflector](Reflect/TailBody.lean) shares the expression reflector's field context, and [its
equations](Reflect/TailListLemmas.lean) connect the native step to the typed match.  For a
user-defined recursive type, the command `verified_recursive_type`, run once after the type's
`Encode` instance, derives the conversion to the typed tree, the agreement of the instance with it,
and the match lemmas, and, when no field holds an enumeration or a sum, the conversion back and both
inverse laws.  `verified_compile` requires these declarations of every recursive type that a program
uses.  A record's fields may be words, `Bool`s, floats, children, and values of a type with a `Flat`
instance, one slot for each leaf of its flattening, with at most 64 slots, the tag included.  [The
derivation](Reflect/RecursiveTypes.lean) supports construction, matching, guarded and tail
recursion, identity, duplication, tuples, calls, and loop state, and it excludes a type with a field
that holds an enumeration or a sum from recursive parameters.  [Native matcher
normalization](Reflect/NativeTree.lean) abstracts the alternatives before proving their constructor
cases.  [Generated branch equations](Reflect/RecursiveMatch.lean) preserve denotation, allocation
bounds, and frames conditions.  The [native-type example](Examples/RecursiveTypes.lean) checks the
existing `Words` and `KeyTree` layouts, including subtree release and header reuse.  Native tail
matching uses the same field context and branch equations as expression matching.

The typed `Expr.listFold` traverses a list with a scalar accumulator and borrowed captures.
Its state contains the list pointer, accumulator, and captures.  Null returns the accumulator,
and a record supplies the head and next pointer for a step.  A structural tree measure proves
termination.  The [tail-code generator](Compile.lean) accepts the step's expression code, so
folds and tail functions share their control instructions.  The
[expression rule](AlignedListFold.lean) composes argument evaluation, the
[loop rule](AlignedListFold.lean), and release of owned outer values after the fold.
[Resource equations](ListFoldResource.lean) sum the step's allocation charges and frames
conditions along the traversal.  [Fold agreement](TreeFold.lean) proves the full Lean
`List.foldl` meaning under the accumulator encoding.  The reflector selects the step's free
variables as borrowed captures and proves its meaning, allocation charge, and frames condition
with the [native-fold equations](Reflect/ListFoldLemmas.lean).  Captured values need only a
forward encoding.  The [native list example](Examples/Lists.lean) covers encoded sums, tuple and
Boolean state, both float widths, nested folds, allocating steps, constructed inputs, and guarded
calls in a step.

The [copy cases](Examples/TreeCopyCases.lean) cover lists, branching trees, null children, arbitrary
words, and chains through 4,096 records.  They also check detached headers with 1 and 64 fields
and header allocation from memory reused after releasing a list.
`tests/verified/run.sh --cases treecopy` compares the
[copy test module](Examples/TreeCopy.lean) with native Lean and checks allocation and live-block counts.
The [typed constructor and matching module](Examples/TreeCore.lean) derives its correctness from
the universal compiler theorem.  Its [cases](Examples/TreeCases.lean) exercise owned and borrowed
construction, field access, rebuilding, duplication, word updates, and typed folds, including
retained aliases and last-use header reuse.  The fold cases cover wrapping arithmetic, captured
array reads, per-step allocation, and release of owned inputs.  `tests/verified/run.sh --cases treecore`
runs those cases.
The [list-tail cases](Examples/ListTailCases.lean) check borrowed summation and consumed reversal
through 4,096 cells, beyond the guarded call-depth limit.  Reversal reuses each matched header.
`tests/verified/run.sh --cases listtail` checks their results, allocations, and retained blocks.

## Recursion

A guarded recursive function's meaning is a solution `M` of its body's equation, `M env = body.denote
(Funs.cons M funs) env`, and `Prog.Meaning prog funs` states that `funs` are such meanings for every
function of the program, `Func.denote` for the others.  `Prog.funs` gives the meanings of a program
without recursion, and the reflector gives a recursive definition's meaning as the definition
itself.  The code of a guarded recursive function, and of every function that calls one, takes the call
depth as a first parameter, traps at `unreachable` when the depth reaches `depthLimit`, 1,000, and
passes the depth plus one to the functions of this kind that it calls.  After the program's
functions the module holds an entry for each such function, exported under its name, which calls it
with depth 0.  Talos's semantics bounds no call depth, and Wasmtime ends a deep recursion with a
stack-overflow trap, so the guard keeps every run that the theorem describes within a fixed number
of nested calls.  Wasmtime 44 on aarch64 keeps 8 bytes for each value live across a call and 16
bytes per frame, so the reflector rejects such a function with more than 32 positions: 1,000 frames
of 32 positions take at most 272,000 bytes of the 512 KiB default stack, and the rest holds the
functions without the depth parameter at the top of the chain.  The tests run `deep`, whose frame
has 32 positions, 26 of them live across the self-call, to depth 999, where its deepest frame calls
two functions without the depth parameter.

[The tail-run lemmas](TailRun.lean) model a step that continues with another state or returns a
value.  They prove uniqueness of the result and run length, agreement with a fixed-point
meaning, and existence of a finite run from a well-founded transition relation.  They define a natural-valued rank
and prove that the allocation sums and frames conditions stabilize past the finite run's
length.  [The indexed Wasm loop rule](TailLoop.lean) uses the least rank represented by its
invariant to prove that each continuing iteration decreases the rank.

[Typed tail bodies](Source.lean) have return, continue, conditional, and binding nodes.
[Their code template](Compile.lean) copies the initial parameters into mutable locals
and stores each continuation there.  [The bounds](Bound.lean) sum per-step charges
over the finite run.  Parameter modes stay fixed, with owned continuation arguments
propagated by [mode inference](Reflect/TailModes.lean).  [The body theorem](AlignedTailEntry.lean)
covers return, continuation, conditional, and binding code, including paid result potential.
[The whole-loop theorem](AlignedTailLoop.lean) composes the represented states, kept regions,
and remaining bounds.  [The function-entry theorem](AlignedTailEntry.lean) proves the Wasm
function's behavior from its initial arguments.  `Prog.consTail` includes the tail function,
and its `Prog.Meaning` proof supplies the fixed-point equation and decreasing rank.
`Prog.calls` uses the tail-function specification in the same induction as ordinary and
guarded functions.  [The typed-source example](Examples/TailCore.lean) grows an owned array
from a borrowed weight array.  Its twenty [checked execution cases](Examples/Cases.lean)
include 4,096 iterations and allocation counts.

[The tail-body reflector](Reflect/TailBody.lean) constructs a native return-or-continue
step and proves its agreement with the typed body and the recursive definition's fixed-point
equation.  [Termination reflection](Reflect/TailTermination.lean) derives a well-founded
continuing transition from Lean's generated induction theorem.  [State flattening](Reflect/TailState.lean)
proves both inverse laws for the tuple of native parameters and its source environment.
[The reflection examples](Examples/TailReflection.lean) check these proofs for word accumulation,
array growth with fixed weights, scalar pairs, and arrays of records.  [Definition assembly](Reflect/TailDefinition.lean)
adds the typed function, decreasing rank, and fixed meaning.  The fixed-point equations go
through `Sum.elim_inl`, `Sum.elim_inr`, and `Tail.fixed_restate`, and each meaning definition
has a height above its function's, so the kernel checks them without unfolding the recursive
definition.  For the prime-factor count, whose measure has a factor `2 ^ 64`, that unfolding does
not finish.  When Lean's induction theorem states a case's condition in another form than the step,
the termination proof splits the step on its conditions and closes contradictory branches with
`omega`.  The command selects this path
for recognized tail recursion by default.  `set_option verified.tailLoops false` retains
guarded recursion.  A tail function takes a depth parameter only when its body calls guarded
code.  Continuing iterations preserve that depth.

[Tail bound reflection](Reflect/TailBounds.lean) charges the continuing call at zero in the
existing expression builder and proves equality with the typed body's step charge.
[Source equality](Reflect/SourceEq.lean) proves finite argument-function equalities by
extensionality when function renaming and argument packing differ.  The public bound sums
native step charges with `Tail.costAt`, and its frames equation uses `Tail.fitsAt`.
Zero charges give bound 0 without evaluating the rank.  [The command example](Examples/Tail.lean)
includes owned growth, rotation, replacement, aliases, and calls between tail and guarded functions.
[The condition examples](Examples/TailConditions.lean) cover Boolean coercions, inequality,
proof-named conditionals, destructuring, and borrowed pair and record states.  The native step
uses the existing field-normalization pass, so the termination proof sees native record fields.

## Theorem statement, allocation bounds, and tables

[`ArgsCorrect.lean`](ArgsCorrect.lean) proves argument evaluation, release after a call, and
parameter-potential accounting independently of universal expression correctness.  The generic
tail-loop rules use these shared lemmas.  [`AlignedTailEntry.lean`](AlignedTailEntry.lean) combines those rules
with the expression theorem when it proves correctness for every typed tail body.

For a program with an empty byte-literal pool, the theorem for each function is `ImplementsA aborts`, the heap form of `Implements` in
[`LeanExe/Pipeline/Implements.lean`](../LeanExe/Pipeline/Implements.lean).  From any heap and store
with the allocator invariant, a memory cap of at most 65,535 pages, and arguments that represent
`x`, whose moved blocks lie apart from one another and from the memory that the call reads, the
function returns words that represent `f x` and own its arrays, keeps the allocator invariant and
the memory caps, keeps every region of the caller's heap that lies apart from the moved blocks, and
places the result's arrays apart from those regions.  `aborts` is part of each function's signature.
The flag is conservative: array results and updates, owned parameters, recursive construction and
matching, and calls that may trap enable it.  Allocation may trap when memory runs out, and guarded
calls may trap at the depth limit.  A function whose `aborts` is false returns without a trap.
The theorem for a function whose code takes the call depth holds at its entry, with a trap allowed,
and its internal function meets `ImplementsP`, below, at each depth from the arguments that follow
the depth word.

Each function also has an allocation bound, a Lean function of its arguments that
[`Bound.lean`](Bound.lean) defines from the code: the bytes by which the allocator's `top` can rise
during the call.  `Expr.allocs` follows `Expr.code` with the same modes and live sets and counts
each copy, each built array, and each block of `push`, `++`, and `insertAt`, at 48 bytes of header
plus the payload, and it ignores the reuse of freed blocks.  An owned array of `n` words in a block
of `c` bytes has the potential `4 · 8 (n + 1) ∸ 2c`, which [`Potential.lean`](Potential.lean)
defines.  The result of an extension of an owned array that dies is paid, as are a variable that
`let` binds to a paid value and an `if` whose branches are both paid.  A paid array's extension by
`k` words is charged a header and `32 k` bytes, which with the array's potential cover the bytes of
a move to a block of twice the capacity and the new block's potential.  An extension of an owned
array that dies and is not paid is charged a block of twice the bytes of its new length and `16 k`
bytes, which leave the result's potential.  A loop's state is paid when the loop's mode is owned,
the body holds a `push`, `++`, `insertAt`, or a call of a function with a paid parameter, and the
body's value is paid when the state is, as `Expr.statePaid` checks.  An initial value that is not
paid is then charged `16 (u + 1)` bytes per array of `u` words, the most potential its block can
hold.  A loop of `n` pushes of one word onto its state is therefore charged `80 n` bytes and the
credit.  An owned array parameter is paid when the body extends an array, and a call's result is
paid when the callee's result holds an array and its body's value is paid with its parameters'
flags.  `Prog.flags` collects these flags for a program.  A recursive function's parameter flags
count its calls of itself as extending nothing, and its result flag assumes that its calls of itself
return paid values and holds when its body's value is then paid.  A call charges the credit of each
argument at a paid parameter, except an argument that is a paid owned variable that the call moves,
whose potential the caller holds.  An owned pair is paid when each component is paid or holds no
array, and the components of a destructured paid pair are paid.  In the result of the body of a
loop whose state grows, an `if` reached through `let`s, destructurings, and branches is paid when
either branch is, as `Expr.bodyPaid` checks, and `Expr.buys` charges the credit of the value of the
branch taken when that branch is unpaid and the other is paid.  A loop whose state is a paid pair
is charged the smaller of its bounds with an unpaid and with a paid state, `loopAllocWith false`
and `loopAllocWith true`.  The paid bound charges the credit of an unpaid initial state once and
the credits that `Expr.buys` counts, and the minimum keeps the bound at or below the bound with an
unpaid state.  The value of a loop whose state is a pair is not paid, and neither are the results
of `build`, `set`, and `eraseAt`.  A function's bound is its body's plus the copy of a borrowed
result.  `ImplementsB aborts m e
f bound` is the theorem with the bound: the call traps only when `aborts` holds and `heap.Within
store m (bound x)` fails, and it raises `top` by at most `bound x`.  `Heap.Within`, defined in
the [runtime facts](RuntimeFacts.lean), states that `top + bound x` is at most `65536` times the memory's cap in
pages, which `ImplementsA` requires to be at most 65,535, so the bound must fit in 4,294,901,760
bytes.  `ImplementsB.trapFree` turns it into `ImplementsA false`, with the precondition that the
bound fits and the postcondition that `top` rises by at most the bound, and
`ImplementsB.implementsA` into `ImplementsA aborts` without the bound.

A function whose code takes the call depth has a bound and a frames condition for each number `k` of
frames available, `framesAt d = 1000 - d` at depth `d`.  `Expr.fits` follows `Expr.allocs` with `&&`
in place of `+` and states whether every call that the run makes of such a function finds its
frames.  `Func.boundAt` and `Func.fitsAt` give such a function the bound 0 and the condition `false`
at 0 frames, where its guard traps, and at `k + 1` frames its bound and its body's frames condition
with its callees at `k`.  `RecFunc.boundAt` and `RecFunc.fitsAt` do the same for a recursive
function, which is among its own callees.  `Prog.boundsAt` and `Prog.fitsAt` collect them for a
program.  A function whose code takes no call depth has the same bound at every `k`, and its calls
always find their frames.  `ImplementsP` states the theorem of a function, at depth `d` for one
whose code takes the call depth: the call traps only when the frames condition fails or, when
`aborts` holds, `top` cannot rise within the cap by the potential of the arguments at paid
parameters plus the bound.  When the condition holds, `top` after the call, plus the potential of a
paid result, is at most `top` before it plus that sum.  `FunSpec.implementsB` gives `ImplementsB`
with the credits of the paid arguments plus the bound, since an owned array's potential is at most
its credit.

A program may hold constant tables of words.  A table is a Lean constant of type `Array UInt64`, and
the module writes the tables with data segments from the heap base, 4096, each as a length word and
its words.  A function reads a table as a
borrowed array parameter, so the theorems for borrowed arrays cover it.  A wrapper is a definition
`f x := g T₁ … Tₖ x` that applies a listed function `g` to tables before its own parameters.  The
module exports it as an entry that pushes the tables' addresses and calls `g`, and its theorem is
`ImplementsTables` for an empty byte-literal pool, `ImplementsA` with two further premises: each table is a borrowed array at its
address, and the blocks that the arguments move lie apart from it.  The instantiation theorem
`compileWith_initialStore` in [`Instantiate.lean`](Instantiate.lean) shows that the store in which
the module starts, as Talos's `Module.initialStore` builds it, meets the allocator invariant with
the bump pointer after the tables and an empty free list, caps the memory at 65,535 pages, and holds
each table at its address, so the theorems apply to the first call.  The reflector states it for
each such program as `p.initial`.  A wrapper is no function of the program, so other functions pass
tables as parameters.  [The call module](Call.lean) names that condition on a store `Ready` and
states with `Call` that an entry, called from a ready store, leaves a ready store, so that a call
theorem covers every call of a sequence that starts in the initial store.

[Literal collection](Literals.lean) traverses every function body, including guarded and tail
bodies and expression callbacks.  `Prog.literalPool` removes duplicate nonempty byte lists and
stores their concatenation in one raw data segment after the word-array tables.  The static
bytes have no allocation header.  The allocator starts at the eight-byte-aligned end of the
pool.  Each literal evaluation copies from this pool into its own owned allocation.
[Empty-pool equality](LiteralCodeEq.lean) states the module for an empty pool: the table segments
are its only data, its memory size and heap start depend only on the tables, and its functions use
the empty pool.  The default `compileWith` pool
starts at `tablesEnd tables`.

The compiler carries the same pool through expression code, ordinary and tail function
templates, and every program suffix.  This compile-time context adds no function parameter.
`Expr.Covered` and `Prog.Covered` require the source literals to occur in the pool.  The universal
expression and program theorems take this coverage premise.  Expression rules take
[static environment safety](Bytes/StaticEnv.lean), `LiteralPool.Safe`, which combines valid pool
contents with separation from live owned variables.  `Safe.after` transports both facts through
the existing `After` result.  Binding and tree-field rules extend safety to newly bound values,
and callback proofs derive it from their accumulated heap steps.

Function specifications use [the static input predicate](Bytes/StaticInput.lean),
`pool.Input heap store words value`.  It requires `pool.Static heap store` and, for every pool
region, `Apart store (Represent.moves store words value) region`.  [The static memory predicate](Bytes/LiteralFrame.lean)
states the pool's exact contents, memory bounds, and heap region when it is nonempty.
`CodeSpec`, `ImplementsP`, `FunSpec`, and `Calls` share this pool.  [Program correctness with a static pool](Correct.lean),
`Prog.correctStaticWith`, proves the program specifications under coverage.  The public
[static call specification](StaticImplements.lean), `ImplementsStatic`, adds `pool.Input` as a
separate premise using the machine argument words, alongside the ordinary precondition and
borrowed-table premises.  It retains the owned-result, frame, and memory-cap conclusions.
[The static program rules](ProgramStatic.lean) derive the exported `implements` and `trapFree`
theorems and transfer them to Lean's representations.

[Static initialization](Instantiate.lean), `compileWith_initialStaticStore`, requires
`pool.base = tablesEnd tables` and `pool.top ≤ 65535 * 65536`.  Its result establishes the
allocator invariant for `initialStaticHeap pool`, the memory cap, the borrowed tables, and
`pool.Static`.  For a nonempty pool the reflector exposes these four conjuncts as `p.initial`.
Separation from the arguments moved by a later call remains a call premise.  For a program with
no nonempty literals, `Prog.correctWith` and `compileWith_initialStore` take an explicit
`prog.literals = []` proof and preserve the previous generated `ImplementsA`, `ImplementsTables`,
and three-part `p.initial` APIs.

## Module composition

[Prefix composition](ModuleComposition.lean) carries a program's correctness into any module
that keeps its functions at their original indices and provides the shared runtime.
`Prog.calls_prefix` requires the program's function list to be a prefix after the two runtime
functions.  `Prog.calls_extension` applies that rule to a larger compiled program, including its
tables and wrappers.  The original program's meaning proof, allocation bounds, and frames
conditions apply in the larger module.

Composition of programs with literals uses one pool for both function lists.  The pool must cover the
original program and its extension.  [Append coverage](ProgramLiterals.lean),
`Prog.covered_append`, proves that covering the appended program is equivalent to covering both
parts.  `Prog.calls_prefix` and `Prog.calls_extension` take coverage proofs explicitly.  For a
literal-free program, `prog.literals = []` reduces coverage to `List.nil_subset`.

The [library example](Examples/CompositionBase.lean) compiles word addition and float scaling.
The [larger module](Examples/Composition.lean) reuses that program, adds typed callers, and
derives the library functions' execution theorems from prefix composition.  Its
[cases](Examples/CompositionCases.lean) check results and zero allocation through
`tests/verified/run.sh --cases composition`.

[Scalar calibration](ScalarCalibration.lean) derives `ImplementsPureA` from the compiler's
meaning theorem and store-independent execution.  [Sequence rules](ScalarTransport.lean),
[primitive rules](ScalarAtoms.lean), [call rules](ScalarCalls.lean), and
[block and loop rules](ScalarControl.lean) compose the execution proof.  The
[scalar library proofs](Examples/CompositionPure.lean) establish that addition and scaling
return their Lean results and preserve the whole store, starting from any store in a module
with the library prefix.  [Proof generation](Reflect/ScalarProof.lean) adds `p.f.uniform` and
`p.f.pure` for scalar functions whose instructions and callees have these store-preservation
rules.  It scans each instruction sequence and joins its proofs with balanced applications of
the append rules.  The [automatic example](Examples/ScalarComposition.lean) covers branches, division,
tail loops, both float widths, and call chains.

[Program append](ProgramAppend.lean) combines two typed programs and their meaning proofs.
`source.append target` keeps the target's functions first and relocates the source's calls by
the target's function count.  [Function relocation](FunRelocation.lean) and
[tail relocation](TailRelocation.lean) preserve signatures, argument placement, meanings, and
the tail rank.  [The module rules](ProgramAppendCorrect.lean) prove both call-index equations
and preservation of the target prefix.  The [relocation example](Examples/Relocation.lean)
reuses two separately reflected libraries and adds a caller of both.  Its native theorems and
whole-store theorems apply at the combined module's indices, and its
[cases](Examples/RelocationCases.lean) reuse the scalar corpus after relocation.

## WASI Preview 1

`import Verified.Wasi` provides `verified_compile_wasi`.  The command reflects definitions of
`LeanExe.Wasi.Action` into [typed commands](Wasi/Source.lean), with pure expressions as operands.
The [native API](../LeanExe/Wasi/Action.lean) provides stdin reads, stdout and stderr writes,
exit, and bounded loops.  Each primitive read or write makes at most one WASI import call.
The host may use several operating-system calls for one import.  Source code handles errnos
and short transfers.  Effect helpers form an acyclic graph and share the guarded-call depth with
pure callees.  [The WASI manual](../docs/wasi.md) states the API and generated declarations.

| Proof stage | Declaration or predicate | Result |
|---|---|---|
| [Pure transport](Wasi/PureTransportSpecs.lean) | `Calls` | Relocated pure code computes the same values and preserves the host world in a module with the three WASI imports. |
| [Universal command proof](Wasi/CostCommandCorrect.lean) | `Command.cost_code_spec` | Every command constructor preserves ownership and caller regions outside scratch, with source execution or a permitted resource prefix.  Normal results retain their allocation charge, fit predicate, and heap-top bound. |
| [Universal program proof](Wasi/Correct.lean) | `EffectProg.correctWith` | Pure correctness, effect calls, function entries, and command rules compose for the compiled effect program. |
| [Native callable entry](Wasi/NativeEntry.lean) | `compiled_native_entry_run` | The actual exported wrapper executes the original Lean action after injecting depth zero and hidden table addresses. |
| [Native command entry](Wasi/NativeCommand.lean) | `compiled_native_start_run` | `_start` executes the selected closed action, then requests its returned status as an exit. |
| [Modeled initialization](Wasi/ProgramInitial.lean) | `compileWith_initialStore` | The assembled module establishes the allocator invariant, memory cap, borrowed tables, and static literal pool. |

The [resource model](Wasi/ResourcePrefix.lean) charges allocation and checks pure-call fits along
source execution prefixes, including a read's full requested capacity before its reply.  A
generated `total` theorem requires `Heap.Within` and `Resource.CallPrefixBound`, together with
`Host.NoTrapsAlong` for the native action.  The host condition concerns reached operations,
including acceptance of reached exits.  Callable totality gives a return or accepted exit.
[Command totality](Wasi/CommandTotal.lean) gives an accepted exit.  Without those premises,
refinement retains terminal host failures and resource prefixes with their committed effects.

The [host specification](Wasi/HostSpec.lean) reserves scratch `[0, 16)`.  Input read regions and
retained caller regions must lie apart from it.  Returned bytes have owned allocation roots,
and their logical lengths may be smaller than the retained capacity after a short read.
The [source correspondence](../LeanExe/Wasi/RelatedExec.lean) and
[prefix correspondence](../LeanExe/Wasi/RelatedPrefix.lean) preserve ordered events and worlds
through native flattening.

The [public command](Wasi/ReflectCommand.lean) supplies finite profile/readiness proofs and
constructs a scalar module-typing proof through the [validity proof generator](../LeanExe/Encoding/ValidityProof.lean).
Each accepted module receives `Spec.Validity.Module`, checked encoding and decoding, and native
entry refinement in its `bytes` theorem.  These proofs use Talos and the specified host relations.
Real engine instantiation, host conformance, file emission, and host progress remain external
assumptions.  The [execution tests](../tests/wasi/run.sh) run Wasmtime, scripted hosts, and emitted modules.
The [development journal](../devnotes.md#2026-10-23-implementing-the-wasi-agenda) records proof and execution runs.

## WGSL kernels

[The WGSL compiler](WGSL/Compile.lean) translates an outer typed array build to the source
language of [`LeanExe/WGSL/Source.lean`](../LeanExe/WGSL/Source.lean) and its WGSL subset.  [Typed representations](WGSL/Context.lean) relate source values to scalar
expressions and borrowed input buffers.  [Lowering](WGSL/Lower.lean) recursively constructs
[code with a denotation proof](WGSL/Code.lean), using shared rules for bindings, branches, and
counted loops.  Parameters, loop state, and output elements use words, Booleans, or binary32
values.  Unsupported expressions return `none`.

[Kernel construction](WGSL/Kernel.lean) checks the local layout and WGSL translation and retains
their proofs.  [Dispatch correctness](WGSL/Dispatch.lean) combines the lowered element theorem
with the existing generic dispatch theorem.  Every accepted source build computes its source
array and has a race-free dispatch under that theorem's buffer, count, coverage, and device
conditions.  [The manual's WGSL section](../docs/verified-manual.md#wgsl-kernels) states the
accepted subset and API.  [The examples](Examples/Wgsl.lean) and
[native-value proofs](Examples/WgslProof.lean) specialize the result to reflected Lean functions.

The shared WGSL translation normalizes binary arithmetic, square root, and nearest-even results
with [integer tests of their bit patterns](../LeanExe/WGSL/F32Canonical.lean).
[Result lemmas](../LeanExe/WGSL/F32Result.lean) prove that normalization preserves each operation's
strict-model result.  The original and verified compilers use this translation.

[Binary32 GPT](../Demos/Gpt32/Verified.lean) compiles the existing program's thirteen kernel functions
without changing them.  [The native dispatch proofs](../Demos/Gpt32/VerifiedDispatch.lean) combine
`Compiled.dispatch_value` with each generated denotation equation and the buffer bounds.
[The host instance](../Demos/Gpt32/VerifiedHost.lean) supplies those theorems to the existing typed item,
layer, and generation proofs.  Its kernel map also runs through the existing generation driver.
[The application guide](../Demos/Gpt32/README.md#verified-compiler) describes the tests and the
separate Wasm and device-model claims.

## The reflector

The reflector, `verified_compile p := [f, g, …]` in [`Reflect/Command.lean`](Reflect/Command.lean),
writes ordinary Lean definitions as a source program.  [Definition
reflection](Reflect/Definitions.lean) holds the expression translation, bound builders, and shared
recursive-parameter flattening.  Each source definition has a separate term-elaboration action and
its own Lean heartbeat allowance.  The command transfers closed reflection state between
definitions, then assembles the program, wrappers, meaning proof, byte proofs, and exported
theorems.  For each definition `f` it adds the source function `p.f.func`, the equation
`p.f.denote_eq` that it means `f`, and `p.f.implements`, which states that function `2 + k` of the
module `p.module`, or the entry `2 + n + j` of the `j`-th function whose code takes the call depth,
computes `f` on the tuple of its arguments, with the `Represent` instances that Lean synthesizes for
the tuple and the result.  It also adds the meanings `p.funs` and the proof `p.meaning` of
`Prog.Meaning p.program p.funs`.  `p.bytes` states that the module's bytes decode to the module,
which computes every listed definition.  The reflector is meta code and is not trusted: it builds
each equation from the lemmas of [`Reflect/Lemmas.lean`](Reflect/Lemmas.lean), one per Lean form,
and Lean's kernel checks it.  An `if` on a `Prop` comparison needs a lemma, because Lean elaborates
it with `UInt64`'s `Decidable` instance, which is not definitionally the source's test of a `Bool`.
A call of an earlier listed definition becomes a source call, proved from the callee's equation,
`LeanExe.loop` becomes a loop whose condition is `true` and whose body is the reflection of the loop
function's body, and `LeanExe.repeatWhile` becomes a loop with the reflections of its condition and
its step.  An unlisted `@[inline]` helper is unfolded when no source rule covers its application,
and its expanded body's equation gives the equation for the application.  Listed definitions retain
their source calls.  `setIfInBounds`, `insertIdxIfInBounds`, and `eraseIdxIfInBounds` use the
existing set, insertion, and removal expressions through definitional equalities.  `insertIdx!`
expands to the proved conditional form, after binding its array and index when either is an
expression.  `repeatWhile_eq_loop` states that `repeatWhile` is the loop over its fuel whose
function applies the step to a state that satisfies the condition and keeps any other.  The
reflector chooses the parameter modes with `Expr.paramChoice` in
[`Reflect/Modes.lean`](Reflect/Modes.lean): an array parameter is owned when the body consumes it
where it dies, as the array of an update or an extension, at a call that moves it into an owned
parameter, or as the result, directly or through a binding, a branch, a pair, or a loop's state, and
borrowed otherwise.  The choice is not trusted, since the theorem holds for every choice of modes.
The reflector binds with `let` an array that a size or a read reads, a call's argument with arrays
that is not a place, and an argument at an owned parameter that is not a variable.  It replaces a
`let` of a place by its body with the place for the variable, and splits every variable of a pair
type that holds arrays into variables for its components, so that a projection reads a component
without a copy of the pair.  A Lean pair without arrays becomes a tuple: `(a, b)` becomes `Expr.mk`,
a chain of `.1` and `.2` on a tuple variable becomes one `Expr.proj`, and a projection of another
tuple, or a `match` on it, binds the tuple with `let` first.  A structure with a `Flat` instance
whose tuple is its fields becomes the tuple of its fields' source values, its flattening `φ`, so
that a nested structure is flattened in turn.  The environment of each equation holds `φ x` for each
variable `x`, and each equation states that the source expression means `φ` of the Lean term, with
`φ` the identity for the other types.  A constructor or `{ s with … }` becomes the tuple of the
fields in the instance's order, a chain of field reads, `.1`, and `.2` on a structure variable
becomes one `Expr.proj`, and a `match` on a structure binds its fields.  `letE_flat_eq`,
`letPair_flat_eq`, `loop_flat_eq` and `repeatWhile_flat_eq` with `loop_map`, and `apply_ite` state
that `φ` commutes with bindings, pairs, loops, and `if`.  An array of structures is the array of its
elements' flattenings, `Array.map φ`, and `size_map_eq` through `build_map_eq` move the map through
a size, a read, an update, an extension, and a build.  A read past the end gives the flattening of
Lean's default structure, which the reflector checks by unfolding to be the default element, as it
is when the default takes each field's default, as `deriving Inhabited` gives.  The theorem for a
definition on structures follows from the theorem for its flattened function by
`ImplementsA.transferAgree`, from proofs of `Agree` that Lean's instances for the argument tuple and
the result represent each value as the source instances represent its flattening.  The reflector
builds these proofs by recursion over the source types, as `argsInst` and `Ty.leanInst` build the
source instances: `Agree.scalar` for a type without arrays, whose words are the words of its
flattening, `Agree.flatArray` and `Agree.flatMoved` for an array of structures, borrowed or owned,
whose elements Lean's instance stores as the words of their `Flat` tuples, `Agree.refl` for another
array, `Agree.flat` for a record with array fields, and `Agree.prod` for a pair that holds arrays,
each restated along the flattening of the equation's right side.  The kernel checks each step by
unfolding, and the reflector checks it first to name the type that fails.  The reflector builds the
equations and the theorems as terms so that the kernel never unfolds a definition, because it would
evaluate a loop over literal data pass by pass.  `p.f.denote_eq` relates `f` to its body through `f
= fun params => body`, which the kernel checks by unfolding `f` against the lambda.  A call and
`p.f.implements` reach a function's meaning through `Funs.get_there` and `Funs.get_here`, which take
`p.funs.get` to the function's meaning.  A recursive definition, one that Lean records as recursive,
is reflected from its unfolding equation `f.eq_def` with a callee for itself, and its meaning
`p.f.meaning` is `f` at the inverses of the flattenings of an environment's values.  Both laws of
the inverse hold, by `rfl` for structures and pairs and by `map_inverse` for arrays, and they give
the self-call's equation `p.f.meaning_eq` and the fixed-point equation `p.f.fixed`, which the kernel
checks without comparing `f` at two different arguments, since `f`'s value is a `WellFounded.fix`.
An enumeration or a sum in a parameter type, directly or in a field of a recursive type, has no
inverse on the words that encode no constructor, so the reflector rejects it in a recursive
definition, as it rejects a recursive definition that uses `sorry`.  Its parameter modes are the
choice of `Expr.paramChoice` for the body reflected with the modes before, from all borrowed, until
the choice repeats or after one round per parameter.  An `if h : c` whose branches do not use `h` is
reflected as `if c`.  The reflector evaluates a body's flags, modes, and positions with the kernel's
`whnf`, and the `bytes` theorem's bound on locals with `decide +kernel`: the elaborator's evaluation
recurses once per level of the body and exceeds its recursion limit on a deep one.  A `match` on a
value that is not a variable meets its alternative through an equation proved by `cases` on a
variable, the flattenings appear as lambdas, and equations compose with explicit middle terms.  A
definition without parameters is the exception: the kernel relates the constant to a body that is a
`match` by unfolding the matcher first, as for Lean's own equation lemmas, so it evaluates a
discriminant that computes over literals.  Only literals become constants: any other closed term is
compiled as written.  An enumeration, an inductive type whose constructors have no fields, with a
`Flat` instance to words, is the word of that instance, so it needs no source type of its own, and a
constructor becomes its word.  A `match` on an enumeration becomes a chain of `if`s on the word that
chooses each constructor's alternative, which `reduceMatcher?` reads off the match.  The equation of
the chain and the match is proved by `casesOn` on a variable for the value, with variables for the
alternatives, so the kernel evaluates the tests and field projections.  `==`, `!=`, `decide`, and
`if` on enumerations become the same comparisons of words, by `flat_beq`, `flat_bne`, `flat_decide`,
`flat_ite`, and `flat_ite_ne` from a theorem, added once per program and enumeration, that the
flattening is injective, which follows from a decoder by one case per constructor.  `==` needs
`LawfulBEq`, which `deriving DecidableEq` gives, and `decide (a ≠ b)` becomes `!decide (a = b)` by
`decide_not`.

Sums with scalar fields use the same match translation.  `SumLayout` checks each constructor's
constant tag and the tuple path of each field in its `Flat` instance.  `reflectDataMatch` builds
the conditional chain, projects the selected fields, and proves the chain's equation by constructor
cases.  A wildcard may bind the original value.  Constructor translation reduces the `Flat` tuple
while preserving its scalar terms for ordinary reflection.  The source expressions are tuples,
projections, and conditionals, and arrays use the existing element representation and ownership
rules.  [The sum example](Examples/Sums.lean) checks these forms with binary64 shapes and a sum
with binary32 and enumeration fields.

A `match` with several alternatives on a structure with a `Flat` instance, whose patterns fix
fields to constructors of enumerations and bind the others, as `{ value, steps, last := .add }`
does, becomes a chain of `if`s from `structMatchChain`.  `structAlts` reads each alternative's
pattern from the matcher's type with its motive abstract, and it accepts a variable for the value
and the structure's constructor with each field a variable or a constructor of an enumeration with
a `Flat` instance to words.  Any other field pattern, such as a literal, a `Bool`, or a nested
structure, stops the reflector with a message that names the field.  A match on a structure without
a `Flat` instance does not reach the rule, so a match on a `UInt64` with literal patterns, which
Lean records as a match on a structure, stops with `unsupported term`.  The chain tests, in the
order of the alternatives, the words of the fields that each pattern fixes, joined with `&&`, and
the last alternative, or one that fixes no field, takes no test.  The equation of the chain and the
match is proved by `casesOn` on a variable for the value and then on each fixed field, with
variables for the alternatives, so the kernel reduces both sides at each combination of
constructors without evaluating the value or an alternative's body.  A discriminant that is not a
place is bound with `let` first.  [The pattern example](Examples/Patterns.lean) checks these forms
on parameters, calls, loop states, and a record that holds an array.

A sum whose `Flat` tuple holds `Bytes`, arrays, or recursive types has the source type of that
tuple, a `Ty.pair`, and `instRepresentOfFlat` represents it as the tuple, so the compiler and its
proofs treat it as a pair.  The reflector does not split its variables, since no function rebuilds
the sum from the tuple: `reflectSplit` and the `let` rule leave a variable of such a sum whole, and
`pairView` gives its components for copy costs but no rebuild.  `reflectDataMatch` binds
`p := Flat.flat x` with `let` before the chain of tag tests, so the match destructures the variable
once with `letPair` and each branch reads its fields as variables, while a scalar sum keeps its
projections.  `requireRecursiveTypes` also checks the recursive types that only a sum's tuple
names.  [The heap sum example](Examples/HeapSums.lean) covers construction, borrowed and owned
matches, results, pairs, loop state, and lists, trees, bytes, and arrays as fields.

The reflector spreads a field of a type with a `Flat` instance over the leaves of its flattening,
one word field for each leaf, and `NativeField.flat` holds each leaf's element and path.  In a
branch the field is one Lean variable and each leaf a source variable keyed by the leaf's term, and
`keyedComponent?` reads the field, a component, or a leaf from those variables.
`verified_recursive_type` derives `fromTree` and the inverse laws only when every such field is a
structure whose `Flat` tuple holds each of its fields and whose leaves, through nested structures,
are words, `Bool`s, and floats, since a word that encodes no constructor of an enumeration or a sum
has no Lean value.  [The typed-field example](Examples/TypedTrees.lean) covers `Bool`, float, nested
structure, enumeration, and sum fields.

A variable that holds a pair or a record with arrays is split into the components of
its pair, and the body at the value rebuilt from them is the body at the variable by `pair_eta` or
by `p.flat_eta.R`, a theorem added once per program and record and proved by `rfl` with the body and
the variable free, so the kernel unfolds only the `Flat` instance.  Wherever the reflector reflects
a term in place of the one it was given, a `let` it substitutes, a match on a pair it takes apart,
or arguments it binds, it closes the gap with an equation of the two terms by `rfl`, which the
kernel checks by `let`, beta, and constructor reductions, before it applies a flattening.  Under a
flattening that is a `match`, comparing the flattened terms would evaluate them.  A match on a pair
built in place whose pattern binds its two components becomes `let` bindings of the components, and
a match on any other tuple takes apart a variable bound to the tuple, so that each part of the tuple
is computed once.  A pattern may take nested pairs apart, as `let (n, a, b) := f x` does: the
reflector reads the alternative's arguments by reducing the match on the variable expanded into its
pairs, which gives projections of the variable.  It proves the equation of the match and the
alternative at those projections by `rfl` with variables for the discriminant and the alternative,
since structure eta lets the match reduce on a variable.  A match on several values and `match h :
…` are not supported.  The reflector writes `min a b` and `max a b` on words and floats as `if a ≤
b`, which is Lean's definition and, on floats, differs from `f64.min` and `f64.max` on NaN and on
zeros of opposite sign, after binding with `let` an operand that is not a variable.  Each of these
rewritings leaves the meaning unchanged.  The reflector computes the bit pattern of a float literal,
of `Float.ofBits` or `UInt64.toFloat` of a word literal, and of a negated literal, and the kernel
checks by `decide` that the literal has it.  It rejects `=` and `≠` on floats, which compare bit
patterns, so that `0.0 ≠ -0.0`, and which no f64 instruction computes.

The reflector keeps the context expression in `Ctx.ctx` and extends it with one `consCtx` per
binding.  The nested contexts share their tails, so a new binding does not copy the contexts of
the earlier bindings.  Its bound and frames builders use the same contexts.

The command evaluates the module and encoder natively to obtain literal byte lists `p.sections`,
`p.bodies`, and `p.data`.  The kernel checks the encoding and locals bound of each function in
`p.func_ok_k`, the remaining sections in `p.rest_ok` and `p.data_ok`, and the code-section bounds
in `p.codes_ok`.  `p.encoded` assembles these proofs into the equation for `encode p.module`.
`p.bytes` follows by `decode_encode`.  Native evaluation supplies the literals, and the kernel
checks every claim about them.  It checks each function's encoding in a separate theorem.

For each source function of the program the reflector also adds `p.f.bound`, the function's allocation
bound in bytes on the tuple of its arguments, with `Moved (Array α)` for an owned array and `Unit`
for no parameters, and `p.f.trapFree`.  For a function without paid parameters whose code takes no
call depth, `p.f.bound` is the compiler's bound, `Func.bound` of the function among the functions
before it, which is `Prog.boundsAt` of the program at the function, composed with the flattening of
the tuple, and `#eval` computes it by interpreting `Expr.allocs` over the reflected program.  Its
`p.f.trapFree` states `ImplementsA false` when the byte-literal pool is empty: the call returns `f` of its arguments, without a trap and
for enough fuel, and raises `top` by at most `p.f.bound x`.  When `aborts` holds, its precondition
is `heap.Within store p.module (p.f.bound x)`.  A function with a paid parameter also gets
`p.f.cost`, the compiler's bound, and its `p.f.bound x` adds the credits of the paid arguments to
`p.f.cost x`, so that `p.f.trapFree` has the same form for every function.  A wrapper whose callee's
code takes no call depth gets the same two declarations, with `Wrapper.bound`, the callee's credits
and bound at the tables and the wrapper's arguments, as `ImplementsTables` with the same conditions
when the byte-literal pool is empty.  With a nonempty pool, generated execution theorems use
`ImplementsStatic` and require static input safety.  Their trap-free forms require the allocation
allowance and guarded-call condition.  A wrapper in such a program receives `trapFree` stated with
`Wrapper.bound`, without a named wrapper `bound` declaration.  Scalar `uniform` and `pure`
declarations are generated only for programs with an empty byte-literal pool.

For a function whose code takes the call depth, `p.f.bound k x` and `p.f.fits k x` take the frames
available first: they are `Func.boundAt` and `Func.fitsAt`, or `RecFunc.boundAt` and
`RecFunc.fitsAt`, of the function among the functions before it, with `p.f.cost k x` the entry and
`p.f.bound k x` the credits plus it for a function with a paid parameter.  With an empty byte-literal pool, its `p.f.trapFree` states
`ImplementsA false` at the function's entry, which calls it at depth 0 with 1,000 frames, under the
precondition `p.f.fits 1000 x = true ∧ heap.Within store p.module (p.f.bound 1000 x)`, and the call
raises `top` by at most `p.f.bound 1000 x`.  With an empty pool, a wrapper whose callee's code takes the call depth gets
no bound and no `trapFree`.

`p.f.bound_eq` states `p.f.bound x` as a Lean term in the function's parameters that mirrors the
definition: the user's loop counts, initial states, steps, conditions, and call arguments,
`blockCost`, `growCost`, `paidGrowCost`, and `creditCost` of [`BoundFacts.lean`](BoundFacts.lean)
for each block and credit that the modes, paid flags, and live sets call for, `loopCost` and
`sumBelow` for loops and builds, `min` of the unpaid and paid bounds for a loop whose state is a
paid pair, and `p.g.bound` at the arguments of a call, or the numeral that
`p.g.bound_eq` states, with `let` values substituted and summands `0` dropped, so that a function
that allocates nothing gets `p.f.bound x = 0`.  A call of a function `g` with a paid parameter shows
`p.g.cost` and `creditCost` of each argument that the call charges.  For a function with a paid
parameter, `p.f.cost_eq` states `p.f.cost x` in this way, and `p.f.bound_eq` states `p.f.bound x` as
`creditCost` of each paid argument's words plus `p.f.cost x`.  The arrays of a record that holds
arrays appear as its fields, such as `b.prices.size`.  A lemma `p.flat_field.R.f : ∀ v, (Flat.flat
v).path = v.f`, for `R` the record's full name, proved by `rfl`, rewrites each component of the
record's flattening by congruence, so that the kernel unfolds neither the term that holds the record
nor a term that unfolds to it.  Under a binder, a component of a variable, such as a loop's state,
becomes its field behind a type hint, and a record with parameters keeps the flattened form.  The
proof applies one lemma of [`Reflect/BoundLemmas.lean`](Reflect/BoundLemmas.lean) per source form.
Each lemma builds its conclusion from its arguments, so that two equations compose by transitivity
where their terms are identical.  The kernel compares two closed `Nat` sums that differ by
evaluating both, which for a closed loop means running it, so the proof's hints compare different
terms only where one holds a variable, or under heads that the kernel unfolds by their heights
before it compares arguments.  A wrapper's `bound_eq` states its bound as the callee's bound at the
tables and its arguments, or as the numeral that the callee's equation states.

For a definition whose code takes the call depth, `p.f.bound_eq` and `p.f.fits_eq` state `p.f.bound
(k + 1) x` and `p.f.fits (k + 1) x` for every `k`, with `p.g.bound k` and `p.g.fits k` at the
arguments of a call of such a function `g`, the definition itself included.  For a definition with a
paid parameter, `p.f.cost_eq` states `p.f.cost (k + 1) x` in this way, with `p.g.cost k` at the
calls of such a `g`, and `p.f.bound_eq` states `p.f.bound k x` as the credits plus `p.f.cost k x`
for every `k`.  `p.f.fits_eq` comes from the lemmas of
[`Reflect/FitsLemmas.lean`](Reflect/FitsLemmas.lean) in the same way, with `Expr.fits_of_depthCalls`
for a part that calls no such function, with the operands `true` of `&&` dropped, and with `true`
for an `allBelow` or a `loopFits` whose parts are `true`.

## Main theorems

| Theorem | Statement |
|---------|-----------|
| [Prog.correctStaticWith](Correct.lean) | Every covered program meets `FunSpec` with the same static pool at each depth, using the flags `Prog.flags`, allocation bounds `Prog.boundsAt`, and frames conditions `Prog.fitsAt`.  Calls require static input validity and separation from consumed argument blocks. |
| `Prog.correct` | For a program with `prog.literals = []`, the function's index in the compiled module meets `FunSpec` at every depth `d` with the flags `Prog.flags`, the bounds `Prog.boundsAt`, and the frames conditions `Prog.fitsAt` at `framesAt d` frames: the code computes the function's meaning in the sense of `ImplementsP`, from its arguments when it does not take the call depth, and then without a trap when its signature's `aborts` is false, and from the depth and its arguments otherwise.  `Prog.correct_funs` states it for a program without recursion and `Prog.funs`. |
| `Prog.correct_entry` | For a program with no nonempty byte literals, the exported entry of a function whose code takes the call depth computes the function's meaning in the sense of `ImplementsA true`.  `Prog.entry_trapFreeWith` states it as `ImplementsA false` when the function's frames condition holds at 1,000 frames and the credits of its paid arguments plus its bound fit, and `Prog.entry_trapFreeWith_unpaid` without the credits for a function without paid parameters. |
| `compileWith_initialStore` | For a program with no nonempty byte literals, the initial store meets the allocator invariant for `initialHeap`, whose bump pointer follows the tables, caps its memory at 65,535 pages, and holds each table as a borrowed array at its address, when the tables end below 65,535 pages.  `tables_written` shows that each table's range holds its length word and words, and `read64_of_bytes` reads each word back through `read64_write64`. |
| [compileWith_initialStaticStore](Instantiate.lean) | With the pool immediately after the tables and its aligned end within the page cap, initialization establishes `initialStaticHeap pool`, the cap, borrowed tables, and static pool contents. |
| `Prog.correct_wrapper` | For a program with no nonempty byte literals, a wrapper computes its callee's meaning at the tables and its own arguments in the sense of `ImplementsTables`, from `wrapper_correct`: the entry's words are the tables' addresses and its arguments, the tables are borrowed arguments of the callee, `Env.withTables_moves` shows that they move no block, and `Env.withTables_reads` that the arguments' reads include their regions.  The theorem `ImplementsTables.lean` states it with Lean's instances. |
| `Prog.calls` | By induction on the program.  Ordinary and tail functions use the specifications of the functions before them.  A guarded recursive function meets its specification at depth `d` by strong induction on `depthLimit - d`, since its self-calls happen at `d + 1` and the guard traps at the limit.  The tail-function rule uses its decreasing rank and whole-loop theorem. |
| `bodyFunction_runs` | A function's code, with or without the depth parameter, in a module whose functions at the call indices compute the functions it calls at the next depth, computes the body's meaning.  `Env.Rep.apart` turns the callee's `Separate` into the facts of `Holds` for the parameters at entry. |
| `Expr.code_spec` | With literal coverage and static environment safety, expression code computes its source value, consumes dying owned values, preserves live values and the local frame, and meets its allocation and call-depth bounds.  The proof is described below. |
| [spec_bytesLiteral](AlignedBytes.lean) | Each nonempty literal evaluation allocates a fresh owned byte buffer with the literal contents.  Empty literals allocate nothing.  The theorem requires coverage and static environment safety. |
| `ImplementsA.lean` | This theorem of [`Correct.lean`](Correct.lean), with `ImplementsA.transferAgree` there and `Ty.leanInst` and `argsInst` of [`State.lean`](State.lean): a function's theorem for the verified compiler's representation gives the theorem with the instances that Lean synthesizes for its argument tuple and result, in which an owned array parameter has type `Moved (Array α)`.  The instances for arrays and their `Moved` forms are those of [`Implements.lean`](../LeanExe/Pipeline/Implements.lean) for `Array UInt64`, `Array Float`, `Array Float32`, and arrays of `Flat` types, which include `Bool`.  `Ty.leanInst`, `Ty.argInst`, and `argsInst` rebuild those instances by recursion over the types and modes, so no signature needs a proof of its own. |

### Expression proof

`Expr.code_spec` assumes coverage of the expression's literals, static environment safety, and
represented live variables whose owned blocks are separate from the other variables' heap data.
It proves that the code computes the source value in its stated mode,
consumes the owned variables that die in the expression, and preserves the live variables.
Parameters and locals below the code's reserved range keep their values.  The result's owned
blocks lie apart from the values that remain live.

The allocation argument tracks `top` and the potential of paid values.  When `Expr.fits` holds,
`top` after execution plus the result's potential is at most the sum of the initial `top`, the
dying paid variables' potential, and `Expr.allocs`.  A trap requires a failed frames condition or,
for code that may allocate, insufficient room for that allowance.  `TrapOK.part` gives each
subexpression its share of the allowance.  `After.seq`, `After.bind`, `After.bind2`, and
`After.release` compose the execution and heap facts.

The loop rule uses `wp_loop_cons`.  Its invariant states that the index is at most the count, the
state locals represent the state after that many passes, live variables retain their values, and
the remaining allocation allowance covers the state potential and remaining passes.  The
condition borrows the state.  `After.test` and `After.test_regions` preserve it, and
`loopState_stop` identifies the result when the condition is false.  A paid initial state brings
its potential.  An unpaid initial state receives credit covering its potential, by
`Ty.pot_le_credit`.  Each pass
transfers the paid state's potential to the next state, and `After.release` preserves it at exit.

For a build, `wp_allocArray` supplies an owned array of the result length.  The invariant describes
the initialized prefix, and `After.writeElement` extends it by one element.  An update uses
`spec_ownedVar` to move an owned array at its last use or copy another array, then writes the new
element.  Extension uses `spec_room` for growth in place, a move to a larger block, or a copy.
`After.replace`, the potential lemmas, `wp_allocCopy`, and `wp_copyInto` establish those cases.
`After.rewrite` preserves the array representation through the writes.

Insertion uses `spec_room`, and removal uses `spec_ownedVar`.  `wp_shiftUp` and `wp_copyDown`
preserve every word until it has been read.  `After.rewriteRange` gives the array after shifting
and changing its length.  `Elem.words_insertIdx` and `Elem.words_eraseIdx` identify the resulting
words with Lean's arrays.  Recursive construction and matching use the field, ownership, and
header rules described in [Recursive records](#recursive-records).

For a call, `args_spec` proves separation between consumed arguments, borrowed data, and the
caller's live values.  A depth-taking callee receives the next depth, and `FunSpec.runs` supplies
its execution theorem.  `Expr.paramPot` accounts for paid arguments: a moved paid variable brings
its potential, and another argument receives the credit charged by `Expr.allocs`.  A paid result
retains the potential stated by the callee's `ImplementsP` theorem.

## Related work

[The journal](../devnotes.md) records the analysis that led to this library and its plan.  The
LeanExe compiler, which the repository no longer holds, proved the same kind of fact for one IR
program at a time with its expression rule `Expr.program_spec`.
[`Scale`](../Examples/Scale/README.md) and [`Axpy`](../Examples/Axpy/README.md) were its closest
programs.

## References

- X. Leroy, "Formal Verification of a Realistic Compiler," *Communications of the ACM*
  52(7):107–115, 2009.
- E. Mullen, S. Pernsteiner, J. R. Wilcox, Z. Tatlock, and D. Grossman, "Œuf: Minimizing the Coq
  Extraction TCB," *Proceedings of CPP 2018*.
- WebAssembly Core Specification,
  [Numerics](https://webassembly.github.io/spec/core/exec/numerics.html).
