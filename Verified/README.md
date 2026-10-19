# Verified Compiler Internals

This document describes how the verified compiler works: its source language, the code that it
produces, the statement and structure of its theorem, and the reflector behind `verified_compile`.
[The verified compiler manual](../docs/verified-manual.md) describes the dialect, the declarations
that the command adds, the bounds, the tests, and the examples for a program's author.  The library
shares the trusted base and the statement of correctness with `LeanExe`: Talos's semantics, the
encoder and decoder with `decode_encode`, `Implements` and its relatives in
[`LeanExe/Pipeline/`](../LeanExe/Pipeline/), and the runtime.  The statements add definitions of
their own: `Heap.Within` in [`Heap.lean`](Heap.lean), the allocation bound of
[`Bound.lean`](Bound.lean), `ImplementsTables` for wrappers, and `initialHeap` and `tableAddr` for
the initial store.  The compiler and its proof have their own definitions of the IR parts they need
and import no part of the LeanExe compiler, and nothing in `LeanExe` or `Examples` imports the
library.  The drone and xorshift examples import programs of `Examples/` that depend on the LeanExe
compiler and its IR lemmas.  The proofs use only the axioms `propext`, `Classical.choice`, and
`Quot.sound`.

## Source language and code

A program is a list of functions in which each function may call the functions after it in the list
and, when it is recursive, itself, so the only cycles are a function's calls of itself.  The list
holds the definitions of a `verified_compile` command in reverse order, so that a definition calls
the definitions before it in the command.  A function's parameters and result are 64-bit words,
`Bool`s, floats, tuples of these, arrays of any of these, and pairs that hold arrays, and its body
is a typed expression.  The element types, `Elem`, are words, `Bool`s, floats, and tuples of element
types, and `Ty.elem` embeds them in the types: `Ty.elem e` is the type of an element, `Ty.array e`
the type of an array of elements, and `Ty.pair` the type of a pair, so an array never holds an
array.  An expression of type `t` over a context `Γ` of types that may call functions with the
signatures `S` has type `Expr S Γ t`, so every expression is well typed, reads only variables in
scope, and calls only functions that exist.  The constructs are those of [the manual's
dialect](../docs/verified-manual.md#the-dialect), each with Lean's meaning, with tuples built by
`Expr.mk` and read by `Expr.proj`, which follows a path of first and second steps from a tuple
variable.  A float operation has the meaning of Lean's `Float`, which
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

A value is carried as words, as `Implements` passes it: a word as itself, a `Bool` as 1 or 0, a
float as its bit pattern in an f64 word, a tuple or a pair as its first component's words followed
by its second's, and an array as the address of its length word and its elements' words in memory.
An element of `k` words occupies `k` consecutive words, a `Bool` as 1 or 0 and a float as its bit
pattern, and the length word counts words.  `Elem.words` gives these words, the identity for an
array of words, as Lean's instances for `Array UInt64`, `Array Float`, and arrays of `Flat` types
such as `Bool` store them; Lean has no instance for an array of tuples, and `Elem.wordsInst` stores
one in the same way.  A structure whose `Flat` tuple holds arrays is represented as that tuple, by
the instance `instRepresentOfFlat` of [`FlatRecords.lean`](../LeanExe/Pipeline/FlatRecords.lean),
and the reflector treats it as a pair whose components are the tuple's.  Such a record may be a
parameter, a result, a local value, or a loop state.  A record parameter is always borrowed, so a
callee that updates one of its arrays copies the array.  A function with a pair result returns
several WebAssembly results.  Each value holds its arrays in a mode, borrowed or owned, which
`Expr.mode` computes from the modes of the variables.  A function's signature gives each array
parameter a mode.  The function reads a borrowed parameter and leaves it in place, and it consumes
an owned parameter's array, releasing it at entry when the body does not use it.  A call's result, a
function's result, and a built, updated, or extended array are owned, so a function copies a
borrowed value that it returns.  Each expression consumes the owned variables that die in it, those
live before it and not after: an owned variable moves into the value where it dies and is copied
where it stays live, a reader or a call releases an owned variable that dies there, and a branch, a
binding, and a loop release the owned variables that die without a use.  The code generator learns
which variables each subexpression reads from the bitmask `Expr.useMask` through `Expr.usesFast`, and
`Expr.usesFast_eq` equates it with `Expr.uses`.  A pair has one mode, and a
loop's state is owned when its initial value or its body's value is owned, so a borrowed component
or state is copied.  A copy allocates through the runtime's `alloc` and writes the length word and
the elements.  A function's locals are its parameters, an i64 local for each further position, and
an f64 local for every position.  A word of type f64 occupies its position's f64 local and any other
word its i64 local, and a function copies its f64 parameter words to their positions' f64 locals at
entry.  Negation compiles to the subtraction of the operand from −0, which is Lean's negation on
every input, since `f64.neg` turns the canonical NaN into a NaN with the sign bit set.
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
the block when the index reaches the count.  A build keeps its count, the array's address, and the
index in locals, traps at `unreachable` when the count's words would be `2^29` or more, since the
array would not fit in 32-bit memory, allocates the array and writes its length word, and stores
each element after the element's code runs.  The outer variables that only the element reads stay
live through the loop and are released after it.  An update runs its position's and value's code
first and then takes the array in an owned position: an owned array that dies there is updated in
its own block, and any other array is copied first.  An extension takes the array with room for the
result: an owned array that dies there grows in its own block when the block has room and otherwise
moves to a block of at least twice its capacity, which releases the old block, and any other array
is copied once into a block with room.  `push` then writes the new element, and `++` copies the
other array's elements after the first's and releases the other array when it is owned and dies
there.  An insertion takes the array with room for one more element in the same way, moves the words
from the position to the end up by one element, from the last word down, and writes the new element
at the position.  A removal takes the array as an update does, moves the words after the element
down by one element, from the first word up, and writes the shorter length.  Each move stays inside
one block, and its order reads every word before it overwrites it.  An insertion past the end writes
the old length back, after the code has copied or moved the array with room, and traps where the
longer array would not fit in memory.  A read keeps the position in a local, compares it with the
array's size, the length word divided by the element's word count, and keeps the result as a flag.
It then loads each of the element's words under the flag, 0 past the end, and converts each float
word to an f64 with `f64.reinterpret_i64`.  An update, a push, and a build store the element's words
in locals and write each, converting a float word with `i64.reinterpret_f64`.  The code uses `min k
2^29` as the word count `k` of an element: an element of `2^29` words or more is in no array that
memory holds, and the bound keeps the count positive and below `2^64`.  WebAssembly traps on a zero
divisor, so the compiled division and remainder save their operands in scratch locals, test the
divisor, and return Lean's result for zero.  [`Source.lean`](Source.lean) defines the syntax and
`Func.denote`, [`Compile.lean`](Compile.lean) the compiler, [`State.lean`](State.lean) the
representation of values in the heap and the facts about variables, [`Heap.lean`](Heap.lean) the
specifications of the allocation, copy, and release code, [`Bound.lean`](Bound.lean) the allocation
bound, [`Potential.lean`](Potential.lean) the potential of owned arrays, and [`After.lean`](After.lean)
the facts that the proof shares.  [The expression rules](ExprCorrect.lean) prove expression and
ordinary-function compilation, and [the program theorem](Correct.lean) combines the function
rules.  The compiled module has the layout of `LeanExe`'s modules, with the runtime's `alloc`
and `release` at functions
0 and 1.

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
propagated by [mode inference](Reflect/TailModes.lean).  [The body theorem](TailCode.lean)
covers return, continuation, conditional, and binding code, including paid result potential.
[The whole-loop theorem](TailWhile.lean) composes the represented states, kept regions,
and remaining bounds.  [The function-entry theorem](TailEntry.lean) proves the Wasm
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
adds the typed function, decreasing rank, and fixed meaning.  The command selects this path
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

## The theorem

The theorem for each function is `ImplementsA aborts`, the heap form of `Implements` in
[`LeanExe/Pipeline/Implements.lean`](../LeanExe/Pipeline/Implements.lean).  From any heap and store
with the allocator invariant, a memory cap of at most 65,535 pages, and arguments that represent
`x`, whose moved blocks lie apart from one another and from the memory that the call reads, the
function returns words that represent `f x` and own its arrays, keeps the allocator invariant and
the memory caps, keeps every region of the caller's heap that lies apart from the moved blocks, and
places the result's arrays apart from those regions.  `aborts` is part of each function's signature.
It is true when the result holds arrays, a parameter is owned, the body builds, updates, extends,
inserts into, or removes from an array, or the body calls a function whose `aborts` is true, whose
result holds arrays, or which owns a parameter, since only then can the function allocate, and an
allocation traps at `unreachable` when memory runs out.  A call of a function whose code takes the
call depth makes `aborts` true as well.  A function whose `aborts` is false returns without a trap.
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
whose potential the caller holds.  Pairs and the results of `build`, `set`, and `eraseAt` are not
paid.  A function's bound is its body's plus the copy of a borrowed result.  `ImplementsB aborts m e
f bound` is the theorem with the bound: the call traps only when `aborts` holds and `heap.Within
store m (bound x)` fails, and it raises `top` by at most `bound x`.  `Heap.Within`, defined in
[`Heap.lean`](Heap.lean), states that `top + bound x` is at most `65536` times the memory's cap in
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
its words, and starts the allocator's bump pointer after them.  A function reads a table as a
borrowed array parameter, so the theorems for borrowed arrays cover it.  A wrapper is a definition
`f x := g T₁ … Tₖ x` that applies a listed function `g` to tables before its own parameters.  The
module exports it as an entry that pushes the tables' addresses and calls `g`, and its theorem is
`ImplementsTables`, `ImplementsA` with two further premises: each table is a borrowed array at its
address, and the blocks that the arguments move lie apart from it.  The instantiation theorem
`compileWith_initialStore` in [`Instantiate.lean`](Instantiate.lean) shows that the store in which
the module starts, as Talos's `Module.initialStore` builds it, meets the allocator invariant with
the bump pointer after the tables and an empty free list, caps the memory at 65,535 pages, and holds
each table at its address, so the theorems apply to the first call.  The reflector states it for
each program as `p.initial`.  A wrapper is no function of the program, so other functions pass
tables as parameters.

## The reflector

The reflector, `verified_compile p := [f, g, …]` in [`Reflect/Command.lean`](Reflect/Command.lean),
writes ordinary Lean definitions as a source program.  [Definition reflection](Reflect/Definitions.lean)
holds the expression translation, bound builders, and shared recursive-parameter flattening.
The command assembles the program, wrappers, byte proofs, and exported theorems.
For each definition `f` it adds the source
function `p.f.func`, the equation `p.f.denote_eq` that it means `f`, and `p.f.implements`, which
states that function `2 + k` of the module `p.module`, or the entry `2 + n + j` of the `j`-th
function whose code takes the call depth, computes `f` on the tuple of its arguments, with the
`Represent` instances that Lean synthesizes for the tuple and the result.  It also adds the meanings
`p.funs` and the proof `p.meaning` of `Prog.Meaning p.program p.funs`.  `p.bytes` states that the
module's bytes decode to the module, which computes every listed definition.  The reflector is meta
code and is not trusted: it builds each equation from the lemmas of
[`Reflect/Lemmas.lean`](Reflect/Lemmas.lean), one per Lean form, and Lean's kernel checks it.  An
`if` on a `Prop` comparison needs a lemma, because Lean elaborates it with `UInt64`'s `Decidable`
instance, which is not definitionally the source's test of a `Bool`.  A call of an earlier listed
definition becomes a source call, proved from the callee's equation, `LeanExe.loop` becomes a loop
whose condition is `true` and whose body is the reflection of the loop function's body, and
`LeanExe.repeatWhile` becomes a loop with the reflections of its condition and its step.
An unlisted `@[inline]` helper is unfolded when no source rule covers its application, and its
expanded body's equation gives the equation for the application.  Listed definitions retain
their source calls.  `setIfInBounds`, `insertIdxIfInBounds`, and `eraseIdxIfInBounds` use the
existing set, insertion, and removal expressions through definitional equalities.
`insertIdx!` expands to the proved conditional form, after binding its array and index when
either is an expression.
`repeatWhile_eq_loop` states that `repeatWhile` is the loop over its fuel whose function applies the
step to a state that satisfies the condition and keeps any other.  The reflector chooses the
parameter modes with `Expr.paramChoice` in [`Reflect/Modes.lean`](Reflect/Modes.lean): an array
parameter is owned when the body consumes it where it dies, as the array of an update or an
extension, at a call that moves it into an owned parameter, or as the result, directly or through a
binding, a branch, a pair, or a loop's state, and borrowed otherwise.  The choice is not trusted,
since the theorem holds for every choice of modes.  The reflector binds with `let` an array that a
size or a read reads, a call's argument with arrays that is not a place, and an argument at an owned
parameter that is not a variable.  It replaces a `let` of a place by its body with the place for the
variable, and splits every variable of a pair type that holds arrays into variables for its
components, so that a projection reads a component without a copy of the pair.  A Lean pair without
arrays becomes a tuple: `(a, b)` becomes `Expr.mk`, a chain of `.1` and `.2` on a tuple variable
becomes one `Expr.proj`, and a projection of another tuple, or a `match` on it, binds the tuple with
`let` first.  A structure with a `Flat` instance whose tuple is its fields becomes the tuple of its
fields' source values, its flattening `φ`, so that a nested structure is flattened in turn.  The
environment of each equation holds `φ x` for each variable `x`, and each equation states that the
source expression means `φ` of the Lean term, with `φ` the identity for the other types.  A
constructor or `{ s with … }` becomes the tuple of the fields in the instance's order, a chain of
field reads, `.1`, and `.2` on a structure variable becomes one `Expr.proj`, and a `match` on a
structure binds its fields.  `letE_flat_eq`, `letPair_flat_eq`, `loop_flat_eq` and
`repeatWhile_flat_eq` with `loop_map`, and `apply_ite` state that `φ` commutes with bindings, pairs,
loops, and `if`.  An array of structures is the array of its elements' flattenings, `Array.map φ`,
and `size_map_eq` through `build_map_eq` move the map through a size, a read, an update, an
extension, and a build.  A read past the end gives the flattening of Lean's default structure, which
the reflector checks by unfolding to be the default element, as it is when the default takes each
field's default, as `deriving Inhabited` gives.  The theorem for a definition on structures follows
from the theorem for its flattened function by `ImplementsA.transferAgree`, from proofs of `Agree`
that Lean's instances for the argument tuple and the result represent each value as the source
instances represent its flattening.  The reflector builds these proofs by recursion over the source
types, as `argsInst` and `Ty.leanInst` build the source instances: `Agree.scalar` for a type without
arrays, whose words are the words of its flattening, `Agree.flatArray` and `Agree.flatMoved` for an
array of structures, borrowed or owned, whose elements Lean's instance stores as the words of their
`Flat` tuples, `Agree.refl` for another array, `Agree.flat` for a record with array fields, and
`Agree.prod` for a pair that holds arrays, each restated along the flattening of the equation's
right side.  The kernel checks each step by unfolding, and the reflector checks it first to name the
type that fails.  The reflector builds the equations and the theorems as terms so that the kernel
never unfolds a definition, because it would evaluate a loop over literal data pass by pass.
`p.f.denote_eq` relates `f` to its body through `f = fun params => body`, which the kernel checks by
unfolding `f` against the lambda.  A call and `p.f.implements` reach a function's meaning through
`Funs.get_there` and `Funs.get_here`, which take `p.funs.get` to the function's meaning.  A
recursive definition, one that Lean records as recursive, is reflected from its unfolding equation
`f.eq_def` with a callee for itself, and its meaning `p.f.meaning` is `f` at the inverses of the
flattenings of an environment's values.  Both laws of the inverse hold, by `rfl` for structures and
pairs and by `map_inverse` for arrays, and they give the self-call's equation `p.f.meaning_eq` and
the fixed-point equation `p.f.fixed`, which the kernel checks without comparing `f` at two different
arguments, since `f`'s value is a `WellFounded.fix`.  An enumeration in a parameter type has no
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
alternatives, so the kernel evaluates only the tests.  `==`, `!=`, `decide`, and `if` on
enumerations become the same comparisons of words, by `flat_beq`, `flat_bne`, `flat_decide`,
`flat_ite`, and `flat_ite_ne` from a theorem, added once per program and enumeration, that the
flattening is injective, which follows from a decoder by one case per constructor.  `==` needs
`LawfulBEq`, which `deriving DecidableEq` gives, and `decide (a ≠ b)` becomes `!decide (a = b)` by
`decide_not`.  A variable that holds a pair or a record with arrays is split into the components of
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

For each function of the program the reflector also adds `p.f.bound`, the function's allocation
bound in bytes on the tuple of its arguments, with `Moved (Array α)` for an owned array and `Unit`
for no parameters, and `p.f.trapFree`.  For a function without paid parameters whose code takes no
call depth, `p.f.bound` is the compiler's bound, `Func.bound` of the function among the functions
before it, which is `Prog.boundsAt` of the program at the function, composed with the flattening of
the tuple, and `#eval` computes it by interpreting `Expr.allocs` over the reflected program.  Its
`p.f.trapFree` states `ImplementsA false`: the call returns `f` of its arguments, without a trap and
for enough fuel, and raises `top` by at most `p.f.bound x`.  When `aborts` holds, its precondition
is `heap.Within store p.module (p.f.bound x)`.  A function with a paid parameter also gets
`p.f.cost`, the compiler's bound, and its `p.f.bound x` adds the credits of the paid arguments to
`p.f.cost x`, so that `p.f.trapFree` has the same form for every function.  A wrapper whose callee's
code takes no call depth gets the same two declarations, with `Wrapper.bound`, the callee's credits
and bound at the tables and the wrapper's arguments, as `ImplementsTables` with the same conditions.

For a function whose code takes the call depth, `p.f.bound k x` and `p.f.fits k x` take the frames
available first: they are `Func.boundAt` and `Func.fitsAt`, or `RecFunc.boundAt` and
`RecFunc.fitsAt`, of the function among the functions before it, with `p.f.cost k x` the entry and
`p.f.bound k x` the credits plus it for a function with a paid parameter.  Its `p.f.trapFree` states
`ImplementsA false` at the function's entry, which calls it at depth 0 with 1,000 frames, under the
precondition `p.f.fits 1000 x = true ∧ heap.Within store p.module (p.f.bound 1000 x)`, and the call
raises `top` by at most `p.f.bound 1000 x`.  A wrapper whose callee's code takes the call depth gets
no bound and no `trapFree`.

`p.f.bound_eq` states `p.f.bound x` as a Lean term in the function's parameters that mirrors the
definition: the user's loop counts, initial states, steps, conditions, and call arguments,
`blockCost`, `growCost`, `paidGrowCost`, and `creditCost` of [`BoundFacts.lean`](BoundFacts.lean)
for each block and credit that the modes, paid flags, and live sets call for, `loopCost` and
`sumBelow` for loops and builds, and `p.g.bound` at the arguments of a call, or the numeral that
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
| `Prog.correct` | For every program, meanings `funs` of its functions, and function in it, the function's index in the compiled module meets `FunSpec` at every depth `d` with the flags `Prog.flags`, the bounds `Prog.boundsAt`, and the frames conditions `Prog.fitsAt` at `framesAt d` frames: the code computes the function's meaning in the sense of `ImplementsP`, from its arguments when it does not take the call depth, and then without a trap when its signature's `aborts` is false, and from the depth and its arguments otherwise.  `Prog.correct_funs` states it for a program without recursion and `Prog.funs`. |
| `Prog.correct_entry` | The exported entry of a function whose code takes the call depth computes the function's meaning in the sense of `ImplementsA true`.  `Prog.entry_trapFreeWith` states it as `ImplementsA false` when the function's frames condition holds at 1,000 frames and the credits of its paid arguments plus its bound fit, and `Prog.entry_trapFreeWith_unpaid` without the credits for a function without paid parameters. |
| `compileWith_initialStore` | The store in which the module of a program with tables starts meets the allocator invariant for `initialHeap`, whose bump pointer follows the tables, caps its memory at 65,535 pages, and holds each table as a borrowed array at its address, when the tables end below 65,535 pages.  `tables_written` shows by induction over the segments that each table's range holds its length word and words, and `read64_of_bytes` reads each word back through `read64_write64`, since `wordBytes` gives the bytes that `Mem.write64` stores. |
| `Prog.correct_wrapper` | A wrapper computes its callee's meaning at the tables and its own arguments in the sense of `ImplementsTables`, from `wrapper_correct`: the entry's words are the tables' addresses and its arguments, the tables are borrowed arguments of the callee, `Env.withTables_moves` shows that they move no block, and `Env.withTables_reads` that the arguments' reads include their regions.  The theorem `ImplementsTables.lean` states it with Lean's instances. |
| `Prog.calls` | By induction on the program.  Ordinary and tail functions use the specifications of the functions before them.  A guarded recursive function meets its specification at depth `d` by strong induction on `depthLimit - d`, since its self-calls happen at `d + 1` and the guard traps at the limit.  The tail-function rule uses its decreasing rank and whole-loop theorem. |
| `bodyFunction_runs` | A function's code, with or without the depth parameter, in a module whose functions at the call indices compute the functions it calls at the next depth, computes the body's meaning.  `Env.Rep.apart` turns the callee's `Separate` into the facts of `Holds` for the parameters at entry. |
| `Expr.code_spec` | From any heap and store with the allocator invariant, in which the variables live before an expression hold words that represent their values in their modes and the blocks of the owned ones lie apart from the other variables' arrays, the code of the expression ends with words that represent the expression's value in its mode.  The step of the heap and store consumes only the blocks of the owned variables that die in the expression, the variables live after it hold their values, an owned value's blocks are new, and the value lies apart from the variables live after it.  The code changes no parameter and no local below the locals it uses.  It traps only when `Expr.fits` fails, or, when it may allocate, when `top` cannot rise by the potential of the paid owned variables that die in the expression plus `Expr.allocs` within the cap, and when `Expr.fits` holds, `top` after the code, plus the potential of a paid value, is at most `top` before it plus that sum.  Each construct's lemma gives a part the allowance with `TrapOK.part`: when the whole's bound fits, the part's bound fits at its start, since `top` has risen by at most the bounds of the parts before it.  `wp_alloc` uses the allowance at each allocation.  One lemma per construct proves it, such as `spec_word` and `spec_eraseAt`; `After.seq`, `After.bind`, `After.bind2`, and `After.release` combine the facts of consecutive codes, of a binding and its body, and of a release.  The loop case uses `wp_loop_cons` with an invariant: the index `i` is at most the count, the state locals hold the state after `i` passes with the facts of `After` for the variables live in the loop, and `top` plus the state's potential, when the state is paid, plus the remaining passes' bound is at most the loop's allowance.  Each pass runs the condition with the state as a borrowed variable, in which no variable dies, so `After.test` keeps the invariant at the condition's heap and `After.test_regions` the state's regions, from which `Ty.pot_of_regions` gives its potential, and a false condition leaves with the state, which `loopState_stop` shows is the loop's value.  At entry the state's potential is that of a paid initial value, which the coercion of an owned value keeps, or at most the credit, by `Ty.pot_le_credit`.  The body counts the state's potential among its dying variables and, since the state is paid only when the body's value is, passes it to the next state.  At the exit `After.release` keeps the state's regions, so the loop's value has the last state's potential.  The build case's invariant is an owned array of the count's length whose elements below the index are built, with the facts of `After`; `wp_allocArray` gives the array, and `After.writeElement` stores each element in place.  The update case takes the array with `spec_ownedVar`, which moves an owned variable that dies and copies any other, and writes the element with `After.writeElement`.  The extension cases take the array with `spec_room`, which proves the growth in place, the move to a larger block with `After.replace`, and the copy, with the potential's arithmetic in `room_inplace_paid` through `room_move_unpaid`; `wp_allocCopy` and `wp_copyInto` give the allocation and the copy loop that the copy of a value also uses, and `After.rewrite` the writes inside an owned block.  The insertion case takes the array with `spec_room` and the removal case with `spec_ownedVar`.  `wp_shiftUp` and `wp_copyDown` prove the moves inside the block by loop invariants under which the words still to read are unchanged, and `After.rewriteRange` gives the array after the moves, the writes, and a shorter length.  `Elem.words_insertIdx` and `Elem.words_eraseIdx` show that the words are those of Lean's `insertIdx` and `eraseIdx`.  The call case pushes the next call depth when the callee takes it, which `FunSpec.runs` turns into the callee's run, and takes the arguments with `args_spec`, which proves that the owned arguments' blocks lie apart from one another and from the borrowed arguments' arrays, as the callee's `Separate` requires, and that the caller's live variables lie apart from the blocks that the call consumes.  `args_spec` also bounds the potential of the arguments at the callee's paid parameters by `Expr.paramPot`: a moved paid variable's own potential, which the caller's dying variables hold, or the credit that `Expr.allocs` charges.  A paid result keeps the potential that the callee's `ImplementsP` states. |
| `ImplementsA.lean` | This theorem of [`Correct.lean`](Correct.lean), with `ImplementsA.transferAgree` there and `Ty.leanInst` and `argsInst` of [`State.lean`](State.lean): a function's theorem for the verified compiler's representation gives the theorem with the instances that Lean synthesizes for its argument tuple and result, in which an owned array parameter has type `Moved (Array α)`.  The instances for arrays and their `Moved` forms are those of [`Implements.lean`](../LeanExe/Pipeline/Implements.lean) for `Array UInt64`, `Array Float`, and arrays of `Flat` types, which include `Bool`.  `Ty.leanInst`, `Ty.argInst`, and `argsInst` rebuild those instances by recursion over the types and modes, so no signature needs a proof of its own. |

## Related work

[The journal](../devnotes.md) records the analysis that led to this library and its plan.  The
`LeanExe` rule for expressions, `Expr.program_spec` in
[`LeanExe/IR/Expr.lean`](../LeanExe/IR/Expr.lean), proves the same kind of fact for one IR program
at a time.  [`Scale`](../Examples/Scale/README.md) and [`Axpy`](../Examples/Axpy/README.md) are the
closest programs of the LeanExe compiler.

## References

- X. Leroy, "Formal Verification of a Realistic Compiler," *Communications of the ACM*
  52(7):107–115, 2009.
- E. Mullen, S. Pernsteiner, J. R. Wilcox, Z. Tatlock, and D. Grossman, "Œuf: Minimizing the Coq
  Extraction TCB," *Proceedings of CPP 2018*.
- WebAssembly Core Specification,
  [numerics](https://webassembly.github.io/spec/core/exec/numerics.html).
