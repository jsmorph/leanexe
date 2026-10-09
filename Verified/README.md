# Verified: a compiler with a correctness theorem

## What it is

This library is a second compiler for LeanExe, written as an ordinary Lean function with one
theorem that covers every program it accepts.  The `LeanExe` compiler is meta code over
`Lean.Expr` and is untrusted, so each of its programs needs its own proof.  This compiler takes a
program in a source language with a meaning in Lean, `denote`, and its theorem states that the
compiled module computes `denote` of the program.  It grows in small iterations, each ending with
bytes, a theorem, and a test in Wasmtime.

The library shares the trusted base and the statement of correctness with `LeanExe`: Talos's
semantics, the encoder and decoder with `decode_encode`, `Implements` and its relatives in
[`LeanExe/Pipeline/`](../LeanExe/Pipeline/), and the runtime.  It copies, and will change, the
parts of the IR it needs, so ordinary development of `LeanExe` does not affect it.  Nothing in
`LeanExe` or `Examples` imports it, and it is not a default target of `lake build`.

## What it covers

A program is a list of functions in which each function may call the functions after it in the list
and, when it is recursive, itself, so the only cycles are a function's calls of itself.  A
function's parameters and result are 64-bit words, `Bool`s, floats, tuples of these, arrays of any
of these, and pairs that hold arrays, and its body is a typed expression.  The element types,
`Elem`, are words, `Bool`s, floats, and tuples of element types, and they are a sub-inductive of the
types: `Ty.elem e` is the type of an element, `Ty.array e` the type of an array of elements, and
`Ty.pair` the type of a pair, so an array never holds an array.  An expression of type `t` over a
context `Γ` of types that may call functions with the signatures `S` has type `Expr S Γ t`, so every
expression is well typed, reads only variables in scope, and calls only functions that exist.
Expressions are constants, variables, `let` bindings, calls, pairs and their destructuring, tuples
built with `Expr.mk` and their components, which `Expr.proj` reads from a tuple variable along a
path of first and second steps, the operations `+`, `-`, `*`, `/`, `%`, `&&&`, `|||`, `^^^`, `<<<`,
and `>>>` on words, `min` and `max` on words, the unsigned comparisons `==`, `!=`, `<`, and `≤`,
float literals, the operations `+`, `-`, `*`, `/`, `Float.sqrt`, `Float.abs`, negation, `min`, and
`max` on floats, the comparisons `==`, `!=`, `<`, and `≤` on floats, the conversions
`UInt64.toFloat`, `Float.toUInt64`, `Float.toBits`, and `Float.ofBits`, the `Bool` operations `!`,
`&&`, and `||`, `if`, `LeanExe.loop`, `LeanExe.repeatWhile`, an array's size `xs.size.toUInt64`, the
read `xs[i.toNat]!`, the update `xs.set! i.toNat v`, the extensions `xs.push v` and `xs ++ ys`,
`LeanExe.build`, and `LeanExe.insertAt xs i v` and `LeanExe.eraseAt xs i`, which insert an element
at position `i` and remove the element there, each with Lean's meaning.  Arithmetic wraps modulo
2^64, division by zero gives 0, the remainder by zero is the dividend, a shift uses its amount
modulo 64, a read past the end of an array gives Lean's default element, 0, `false`, or `0.0`, and
an update, an insertion, or a removal past the end leaves the array unchanged.  A float operation
has the meaning of Lean's `Float`, which [`F64Bits.lean`](../LeanExe/ProofKit/F64Bits.lean) proves
equal on bit patterns to Talos's `IEEE64` functions, the semantics of WebAssembly's f64 instructions
in the deterministic profile, in which every NaN result is the canonical NaN.  `LeanExe.loop n init
f` applies `f` to the indices 0 to `n - 1` in order, starting from the state `init`, and the state
may have any of the types.  `LeanExe.repeatWhile fuel init cond step` applies `step` while `cond`
holds, at most `fuel` times.  The source expresses both with one loop that tests a condition on the
state before each pass and leaves when it fails: `LeanExe.loop` is the loop whose condition is
`true`, and `LeanExe.repeatWhile` the one whose body ignores the index.  `LeanExe.build n f` is the
array of `n` elements whose element `i` is `f i`.  A variable is numbered by its distance from the
front of the context: a binding's value is variable 0 of its body, parameter `i` is variable `i` of
the function's body, a loop's condition has the state as variable 0, its body has the state as
variable 0 and the index as variable 1, and a build's element has the index as variable 0.  The
size, the read, the update, and the extensions take array variables, and a call's argument that
holds arrays is a place, a variable or a pair of places, and a variable at an owned parameter.

A value is carried as words, as `Implements` passes it: a word as itself, a `Bool` as 1 or 0, a
float as its bit pattern in an f64 word, a tuple or a pair as its first component's words followed
by its second's, and an array as the address of its length word and its elements' words in memory.
An element of `k` words occupies `k` consecutive words, a `Bool` as 1 or 0 and a float as its bit
pattern, and the length word counts words.  `Elem.words` gives these words, the identity for an
array of words, as Lean's instances for `Array UInt64`, `Array Float`, and arrays of `Flat` types
such as `Bool` store them; Lean has no instance for an array of tuples, and `Elem.wordsInst` stores
one in the same way.  A structure whose `Flat` tuple holds arrays is carried as that tuple, by
the instance `instRepresentOfFlat` of [`FlatRecords.lean`](../LeanExe/Pipeline/FlatRecords.lean),
and the reflector treats it as a pair whose components are the tuple's.  Such a record may be a
parameter, a result, a local value, or a loop state.  A record parameter is always borrowed, so a
callee that updates one of its arrays copies the array.  A function with a pair result returns
several WebAssembly results.  Each value
holds its arrays in a mode, borrowed or owned, which `Expr.mode` computes from the modes of the
variables.  A function's signature gives each array parameter a mode.  The function reads a borrowed
parameter and leaves it in place, and it consumes an owned parameter's array, releasing it at entry
when the body does not use it.  A call's result, a function's result, and a built, updated, or
extended array are owned, so a function copies a borrowed value that it returns.  Each expression
consumes the owned variables that die in it, those live before it and not after: an owned variable
moves into the value where it dies and is copied where it stays live, a reader or a call releases an
owned variable that dies there, and a branch, a binding, and a loop release the owned variables that
die without a use.  A pair has one mode, and a loop's state is owned when its initial value or its
body's value is owned, so a borrowed component or state is copied.  A copy allocates through the
runtime's `alloc` and writes the length word and the elements.  A function's locals are its
parameters, an i64 local for each further position, and an f64 local for every position.  A word of
type f64 occupies its position's f64 local and any other word its i64 local, and a function copies
its f64 parameter words to their positions' f64 locals at entry.  Negation compiles to the
subtraction of the operand from −0, which is Lean's negation on every input, since `f64.neg` turns
the canonical NaN into a NaN with the sign bit set.  `Float.ofBits` compiles to
`f64.reinterpret_i64` followed by the addition of −0, which gives the canonical NaN for a NaN
pattern and leaves every other float unchanged.  A float constant's code holds its canonical bit
pattern, which the compiler computes with integer operations, so the bytes that `tools/Emit.lean`
writes by evaluating the compiler natively do not depend on Lean's native float code.  Each
binding's value is stored in positions of its own, and a call pushes its arguments' words in order
and calls the function, which the module places before its callers.  An argument at an owned
parameter moves its variable into the call when the variable is owned, dies at the call, and no
other argument with arrays reads it, and is copied otherwise.  Every argument's variables stay live
until the call, so a later argument may read a moved array, and the call then releases the owned
variables that die there and that it does not consume.  An `if` stores the words of its value in
locals in each branch and loads them after it, because the encoder writes block types of at most one
result.  A loop keeps its count, its index, and its state in locals, compares the index with the
count at the top of a WebAssembly `loop` inside a `block`, and branches out of the block when the
index reaches the count.  A build keeps its count, the array's address, and the index in locals,
traps at `unreachable` when the count's words would be `2^29` or more, since the array would not fit
in 32-bit memory, allocates the array and writes its length word, and stores each element after the
element's code runs.  The outer variables that only the element reads stay live through the loop and
are released after it.  An update runs its position's and value's code first and then takes the
array in an owned position: an owned array that dies there is updated in its own block, and any
other array is copied first.  An extension takes the array with room for the result: an owned array
that dies there grows in its own block when the block has room and otherwise moves to a block of at
least twice its capacity, which releases the old block, and any other array is copied once into a
block with room.  `push` then writes the new element, and `++` copies the other array's elements
after the first's and releases the other array when it is owned and dies there.  An insertion takes
the array with room for one more element in the same way, moves the words from the position to the
end up by one element, from the last word down, and writes the new element at the position.  A
removal takes the array as an update does, moves the words after the element down by one element,
from the first word up, and writes the shorter length.  Each move stays inside one block, and its
order reads every word before it overwrites it.  An insertion past the end writes the old length
back, after the code has copied or moved the array with room, and traps where the longer array
would not fit in memory.  A read keeps the
position in a local, compares it with the array's size, the length word divided by the element's
word count, and keeps the result as a flag.  It then loads each of the element's words under the
flag, 0 past the end, and converts each float word to an f64 with `f64.reinterpret_i64`.  An update,
a push, and a build store the element's words in locals and write each, converting a float word with
`i64.reinterpret_f64`.  The code uses `min k 2^29` as the word count `k` of an element: an element
of `2^29` words or more is in no array that memory holds, and the bound keeps the count positive and
below `2^64`.  WebAssembly traps on a zero divisor, so the compiled division and remainder save
their operands in scratch locals, test the divisor, and return Lean's result for zero.
[`Source.lean`](Source.lean) defines the syntax and `Func.denote`, [`Compile.lean`](Compile.lean)
the compiler, [`State.lean`](State.lean) the representation of values in the heap and the facts
about variables, [`Heap.lean`](Heap.lean) the specifications of the allocation, copy, and release
code, and [`Correct.lean`](Correct.lean) the theorem.  The compiled module has the layout of
`LeanExe`'s modules, with the runtime's `alloc` and `release` at functions 0 and 1.

A recursive function's meaning is a solution `M` of its body's equation, `M env = body.denote
(Funs.cons M funs) env`, and `Prog.Meaning prog funs` states that `funs` are such meanings for every
function of the program, `Func.denote` for the others.  `Prog.funs` gives the meanings of a program
without recursion, and the reflector gives a recursive definition's meaning as the definition
itself.  The code of a recursive function, and of every function that calls one, takes the call
depth as a first parameter, traps at `unreachable` when the depth reaches `depthLimit`, 1,000, and
passes the depth plus one to the functions of this kind that it calls.  After the program's
functions the module holds an entry for each such function, exported under its name, which calls it
with depth 0.  Talos's semantics bounds no call depth, and Wasmtime ends a deep recursion with a
stack-overflow trap, so the guard keeps every run that the theorem describes within a fixed number
of nested calls.  Wasmtime 44 on aarch64 keeps 8 bytes for each value live across a call and 16
bytes per frame, so the reflector rejects such a function with more than 32 positions: 1,000 frames
of 32 positions take about 280 KB of the 512 KiB default stack, and the rest holds the functions
without the depth parameter at the top of the chain.  The tests run a frame of 32 positions, each
holding a value live across the self-call, at depth 999 under two such functions.

The theorem for each function is `ImplementsA aborts`, the heap form of `Implements` in
[`LeanExe/Pipeline/Implements.lean`](../LeanExe/Pipeline/Implements.lean).  From any heap and store
with the allocator invariant and arguments that represent `x`, the function returns words that
represent `f x` and own its arrays, keeps the allocator invariant and the memory caps, keeps every
region of the caller's heap, and places the result's arrays apart from those regions.  `aborts` is
part of each function's signature.  It is true when the result holds arrays, a parameter is owned,
the body builds, updates, extends, inserts into, or removes from an array, or the body calls a
function whose `aborts` is true, whose result holds arrays, or which owns a parameter, since only
then can the function allocate, and an allocation traps at `unreachable` when memory runs out.  A
call of a function whose code takes the call depth makes `aborts` true as well.  A function whose
`aborts` is false returns without a trap.  The theorem for a function whose code takes the call
depth holds at its entry, with a trap allowed, and its internal function meets `ImplementsA true` at
each depth from the arguments that follow the depth word.

A program may hold constant tables of words.  A table is a Lean constant of type `Array UInt64`,
and the module writes the tables with data segments from the heap base, 4096, each as a length
word and its words, and starts the allocator's bump pointer after them.  A function reads a table
as a borrowed array parameter, so the theorems for borrowed arrays cover it.  A wrapper is a
definition `f x := g T₁ … Tₖ x` that applies a listed function `g` to tables before its own
parameters.  The module exports it as an entry that pushes the tables' addresses and calls `g`, and
its theorem is `ImplementsTables`, `ImplementsA` with two further premises: each table is a borrowed
array at its address, and the blocks that the arguments move lie apart from it.  The instantiation
theorem `compileWith_initialStore` in [`Instantiate.lean`](Instantiate.lean) shows that the store
in which the module starts, as Talos's `Module.initialStore` builds it, meets the allocator
invariant with the bump pointer after the tables and an empty free list, caps the memory at 65,535
pages, and holds each table at its address, so the theorems apply to the first call.  The reflector
states it for each program as `p.initial`.  A wrapper is no function of the program, so other
functions pass tables as parameters.

The reflector, `verified_compile p := [f, g, …]` in [`Reflect/Command.lean`](Reflect/Command.lean),
writes ordinary Lean definitions as a source program.  For each definition `f` it adds the source
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
`repeatWhile_flat_eq` with `loop_map`, and `apply_ite` carry `φ` through bindings, pairs, loops, and
`if`.  An array of structures is the array of its elements' flattenings, `Array.map φ`, and
`size_map_eq` through `build_map_eq` move the map through a size, a read, an update, an extension,
and a build.  A read past the end gives the flattening of Lean's default structure, which the
reflector checks by unfolding to be the default element, as it is when the default takes each
field's default, as `deriving Inhabited` gives.  The theorem for a definition on structures follows
from the theorem for its flattened function by `ImplementsA.transferAgree`, from proofs of `Agree`
that Lean's instances for the argument tuple and the result represent each value as the source
instances represent its flattening.  The reflector builds these proofs by recursion over the source
types, as `argsInst` and `Ty.leanInst` build the source instances: `Agree.scalar` for a type without
arrays, whose words are the words of its flattening, `Agree.flatArray` and `Agree.flatMoved` for an
array of structures, borrowed or owned, whose elements Lean's instance stores as the words of their
`Flat` tuples, `Agree.refl` for another array, and `Agree.prod` for a pair that holds arrays, each
restated along the flattening of the equation's right side.  The kernel checks each step by
unfolding, and the reflector checks it first to name the type that fails.  The reflector builds the
equations and the theorems as terms so that the kernel never unfolds a definition, because it would
evaluate a loop over literal data pass by pass.  `p.f.denote_eq` relates `f` to its body through `f
= fun params => body`, which the kernel checks by unfolding `f` against the lambda.  A call and
`p.f.implements` reach a function's meaning through `Funs.get_there` and `Funs.get_here`, which take
`p.funs.get` to the function's meaning.  A recursive definition, one whose unfolding equation
`f.eq_def` mentions it, is reflected from that equation with a callee for itself, and its meaning
`p.f.meaning` is `f` at the inverses of the flattenings of an environment's values.  Both laws of
the inverse hold, by `rfl` for structures and pairs and by `map_inverse` for arrays, and they give
the self-call's equation `p.f.meaning_eq` and the fixed-point equation `p.f.fixed`, which the kernel
checks without comparing `f` at two different arguments, since `f`'s value is a `WellFounded.fix`.
An enumeration in a parameter type has no inverse on the words that encode no constructor, so the
reflector rejects it in a recursive definition, as it rejects a recursive definition that uses
`sorry`.  Its parameter modes are the choice of `Expr.paramChoice` for the body reflected with the
modes before, from all borrowed, until the choice repeats.  An `if h : c` whose branches do not use
`h` is reflected as `if c`.  The reflector evaluates a body's flags, modes, and positions with the
kernel's `whnf`, and the `bytes` theorem's bound on locals with `decide +kernel`: the elaborator's
evaluation recurses once per level of the body and exceeds its recursion limit on a deep one.  A
`match` on a value that is not a variable meets its alternative through an equation proved by
`cases` on a variable, the flattenings enter as lambdas, and equations compose with explicit middle
terms.  A definition without parameters is the exception: the kernel relates the constant to a body
that is a `match` by unfolding the matcher first, as for Lean's own equation lemmas, so it evaluates
a discriminant that computes over literals.  Only literals become constants: any other closed term
is compiled as written.  An enumeration, an inductive type whose constructors have no fields, with a
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

| Theorem | Statement |
|---------|-----------|
| `Prog.correct` | For every program, meanings `funs` of its functions, and function in it, the function's index in the compiled module meets `FunSpec`: the code computes the function's meaning in the sense of `ImplementsA`, from its arguments when it does not take the call depth, and then without a trap when its signature's `aborts` is false, and from the depth and its arguments at every depth otherwise.  `Prog.correct_funs` states it for a program without recursion and `Prog.funs`. |
| `Prog.correct_entry` | The exported entry of a function whose code takes the call depth computes the function's meaning in the sense of `ImplementsA true`. |
| `compileWith_initialStore` | The store in which the module of a program with tables starts meets the allocator invariant for `initialHeap`, whose bump pointer follows the tables, caps its memory at 65,535 pages, and holds each table as a borrowed array at its address, when the tables end below 65,535 pages.  `tables_written` shows by induction over the segments that each table's range holds its length word and words, and `read64_of_bytes` reads each word back through `read64_write64`, since `wordBytes` gives the bytes that `Mem.write64` stores. |
| `Prog.correct_wrapper` | A wrapper computes its callee's meaning at the tables and its own arguments in the sense of `ImplementsTables`, from `wrapper_correct`: the entry's words are the tables' addresses and its arguments, the tables are borrowed arguments of the callee, `Env.withTables_moves` shows that they move no block, and `Env.withTables_reads` that their regions join the arguments' reads.  `ImplementsTables.lean` carries the theorem to Lean's instances. |
| `Prog.calls` | By induction on the program: a recursive function's internal function meets its specification at depth `d` by strong induction on `depthLimit - d`, since its self-calls happen at `d + 1` and the guard traps at the limit. |
| `bodyFunction_runs` | A function's code, with or without the depth parameter, in a module whose functions at the call indices compute the functions it calls at the next depth, computes the body's meaning.  `Env.Rep.apart` turns the callee's `Separate` into the facts of `Holds` for the parameters at entry. |
| `Expr.code_spec` | From any heap and store with the allocator invariant, in which the variables live before an expression hold words that represent their values in their modes and the blocks of the owned ones lie apart from the other variables' arrays, the code of the expression ends with words that represent the expression's value in its mode.  The step of the heap and store consumes only the blocks of the owned variables that die in the expression, the variables live after it hold their values, an owned value's blocks are new, and the value lies apart from the variables live after it.  The code changes no parameter and no local below the locals it uses.  One lemma per construct proves it, `spec_word` through `spec_eraseAt`; `After.seq`, `After.bind`, `After.bind2`, and `After.release` combine the facts of consecutive codes, of a binding and its body, and of a release.  The loop case uses `wp_loop_cons` with an invariant: the index `i` is at most the count, and the state locals hold the state after `i` passes with the facts of `After` for the variables live in the loop.  Each pass runs the condition with the state as a borrowed variable, in which no variable dies, so `After.test` keeps the invariant at the condition's heap, and a false condition leaves with the state, which `loopState_stop` shows is the loop's value.  The build case's invariant is an owned array of the count's length whose elements below the index are built, with the facts of `After`; `wp_allocArray` gives the array, and `After.writeElement` stores each element in place.  The update case takes the array with `spec_ownedVar`, which moves an owned variable that dies and copies any other, and writes the element with `After.writeElement`.  The extension cases take the array with `spec_room`, which proves the growth in place, the move to a larger block with `After.replace`, and the copy; `wp_allocCopy` and `wp_copyInto` give the allocation and the copy loop that the copy of a value also uses, and `After.rewrite` the writes inside an owned block.  The insertion case takes the array with `spec_room` and the removal case with `spec_ownedVar`.  `wp_shiftUp` and `wp_copyDown` prove the moves inside the block by loop invariants under which the words still to read are unchanged, and `After.rewriteRange` gives the array after the moves, the writes, and a shorter length. `Elem.words_insertIdx` and `Elem.words_eraseIdx` show that the words are those of Lean's `insertIdx` and `eraseIdx`.  The call case pushes the next call depth when the callee takes it, which `FunSpec.runs` turns into the callee's run, and takes the arguments with `args_spec`, which proves that the owned arguments' blocks lie apart from one another and from the borrowed arguments' arrays, as the callee's `Separate` requires, and that the caller's live variables lie apart from the blocks that the call consumes. |
| `ImplementsA.lean` | A function's theorem for the verified compiler's representation gives the theorem with the instances that Lean synthesizes for its argument tuple and result, in which an owned array parameter has type `Moved (Array α)`.  The instances for arrays and their `Moved` forms are those of [`Implements.lean`](../LeanExe/Pipeline/Implements.lean) for `Array UInt64`, `Array Float`, and arrays of `Flat` types, which include `Bool`.  `Ty.leanInst`, `Ty.argInst`, and `argsInst` rebuild those instances by recursion over the types and modes, so no signature needs a proof of its own. |
| `compiled.bytes` | In each example, the bytes of the module decode to the module, which computes the example's Lean functions: [`Poly.lean`](Examples/Poly.lean), `a * b + c * c - 7`; [`Mix.lean`](Examples/Mix.lean), division, remainder, the bitwise operations, and the shifts; [`Lets.lean`](Examples/Lets.lean), four nested `let` bindings, one inside the operand of a division; [`Select.lean`](Examples/Select.lean), `Bool` bindings, `if` on a `Bool` and on `<`, `>`, and `≠`, a `Bool` parameter, and a `Bool` result; [`Pairs.lean`](Examples/Pairs.lean), pairs as parameters and results, `.1`, `.2`, and `match` on a pair, a pair inside a pair, calls that pass and return pairs, and patterns that take nested pairs apart on the left and on the right, skip a component, keep a pair whole, take apart a pair built in place, and take apart a triple that holds arrays; [`Calls.lean`](Examples/Calls.lean), four definitions in which `sumSq` calls `sq` and `pick` calls the other three, with a call as an argument of a call and a `Bool`-valued call as the test of an `if`; [`Loops.lean`](Examples/Loops.lean), loops over a word, over a pair, and over a pair with a `Bool`, a loop inside a loop, a loop whose body branches, and a loop whose body calls an earlier definition; [`Arrays.lean`](Examples/Arrays.lean), sums, a dot product, a count, and a search over arrays in loops, reads at computed positions, a pair of arrays passed to calls, and an array chosen by an `if` and bound with `let`; and [`Owned.lean`](Examples/Owned.lean), array results, copies of parameters, owned call results that a reader, a call, a branch, or an unused binding releases, a moved result, a loop whose state is an owned array, a pair of owned arrays taken apart, and arrays built with `LeanExe.build`, one whose element builds and releases an array of its own and one whose element reads an owned array that dies after the build; and [`Updates.lean`](Examples/Updates.lean), updates of a parameter, of a built array, of a loop's state, two updates in a row, and an update of an array that stays live; and [`Grow.lean`](Examples/Grow.lean), `push` and `++` on parameters, built arrays, and loop states, onto an array that stays live, an array appended to itself, and an owned right operand; and [`Modes.lean`](Examples/Modes.lean), parameters that a function returns, updates, or moves into an owned parameter, also from a loop's state and before a later argument reads the array, and parameters that stay borrowed because the body uses them again.  Its `byHand`, written without the reflector, has an owned parameter that the body never reads and one that it reads last; and [`Floats.lean`](Examples/Floats.lean), a piecewise function, a scaled hypotenuse, float comparisons as conditions and as `Bool` values, `min`, `max`, negation, a loop over a pair of floats, a function with parameters of every kind and a pair result with a float, a call of float functions, the conversions between words and floats, a power of two built from its exponent field, and literal NaN patterns; [`Records.lean`](Examples/Records.lean), structures with a nested structure and a `Bool` field, built, updated with `{ s with … }`, read field by field, taken apart with `match`, chosen with `if`, passed to calls, and carried as a loop's state, with theorems stated for the structures; [`Tuples.lean`](Examples/Tuples.lean), written without the reflector, arrays of tuples of a float and a word and of a nested tuple, built, read along a path, updated in place, extended, and appended, with an `example` per function stating by `rfl` that it means a Lean function; [`Grids.lean`](Examples/Grids.lean), arrays of the structures of `Records.lean`, built, read element by element and field by field, also past the end, updated in place in a loop, extended with a new structure, appended, counted, reduced to a total and a `Bool`, and returned in a pair with a total, and a local array of pairs; [`Repeat.lean`](Examples/Repeat.lean), `LeanExe.repeatWhile` over words, a float, pairs that hold arrays, and a structure, stopping early under fuels up to `2 ^ 64 - 1`, with a condition that reads an owned array of the state and a step that updates it in place, and loops over literal data inside a pair result, under a `match`, behind a call with literal arguments, and in a closed term; [`Enums.lean`](Examples/Enums.lean), two enumerations, one flattened by `ctorIdx` and one by a `match`, as parameters, results, a structure field, a loop state's field, and array elements, with `match` that has a wildcard binding the value, `match` on an array element, `==`, `!=`, `decide`, and `if` on enumerations, and an update in place; [`Recursion.lean`](Examples/Recursion.lean), recursion once and twice per call over words, floats, a pair, a structure, an array of structures, and an owned array that each call extends and moves into the next, a function that calls two recursive ones, and a recursion that returns at depth 999 and traps at depth 1,000; [`Fields.lean`](Examples/Fields.lean), records with array fields, built, read field by field and element by element, also past the end, updated with `{ r with … }` on a borrowed parameter and, in place, in a loop's state, passed to a call, taken apart with `match`, chosen with `if`, returned in a pair, and held in another record; [`Trig.lean`](Examples/Trig.lean), `sin` and `cos` ported from fdlibm, with its reduction by multiples of `π/2` below `2 ^ 20 · π/2`, a Payne–Hanek reduction in word arithmetic above, after Go's `math.trigReduce`, which reads the bits of `2/π` and `π/2` from tables so that no call allocates, `sinWith` and `cosWith` with the tables as parameters and `sin` and `cos` as wrappers, with theorems that allow no trap, and fdlibm's minimax kernels, written with the constants' bit patterns; [`Fourier.lean`](Examples/Fourier.lean), the discrete Fourier transform of a signal of interleaved complex floats by the `n²` products of the definition, its inverse, and the power spectrum of real samples, with factors from `Trig.cosWith` and `Trig.sinWith`, compiled in the same program, with Trig's tables passed by the wrappers `dft`, `inverse`, `powerSpectrum`, and `twiddle`; [`Exp.lean`](Examples/Exp.lean), `exp` ported from Arm's optimized-routines, with its table of 256 words in a data segment, `expWith` with the table as a parameter and `exp` as its wrapper, and the paths for results that overflow or underflow; [`Tanh.lean`](Examples/Tanh.lean), `expm1` and `tanh` ported from fdlibm, with fdlibm's signed reduction count carried as a sign and a magnitude; [`Log.lean`](Examples/Log.lean), `log` ported from Arm's optimized-routines, with two tables of 256 words in data segments and `log` as the wrapper that passes them; [`Tables.lean`](Examples/Tables.lean), two tables read by wrappers, in range and past the end, and an owned array updated from a table; [`Insert.lean`](Examples/Insert.lean), `LeanExe.insertAt` and `LeanExe.eraseAt` on parameters, built arrays, an array that stays live, a loop's state in an insertion sort and in a removal loop, a local array of pairs, and arrays of structures, also past the end; [`Clob.lean`](Examples/Clob.lean), the bid side of an order book, as two arrays of prices and sizes, with insertions and removals of levels in place, a market buy, cancellations, and command streams, and the theorems that a stream run in two chunks gives the book of one run and that `runOut` leaves the book of `runCommands`; and [`Elements.lean`](Examples/Elements.lean), sums, a dot product, and a maximum over arrays of floats, a grid built from converted indices, an `axpy` that updates an owned array of floats in place, an extension, flags of negative elements, a count and a selection by flags, an update and a push of an owned array of `Bool`s, and a sieve of Eratosthenes. |

The proofs use only the axioms `propext`, `Classical.choice`, and `Quot.sound`.  Every example is
an ordinary Lean file: its definitions and one `verified_compile` command.

## Running it

```sh
tools/leanrun --timeout 60m lake build Verified
tests/verified/run.sh
```

The commands build the library and its theorems, write each example's module to `build/verified/`,
validate it with `wasm-tools`, and compare every case of [`Cases.lean`](Examples/Cases.lean) between
the Wasmtime host and native Lean.  The setup is that of [the repository
README](../README.md#commands).  The cases cover words near 0, 2^32, 2^63, and 2^64, where the
arithmetic wraps, zero divisors, shift amounts of 64 or more, equal words in comparisons, loop
counts of 0, 1, and up to 65,537, empty arrays, reads and updates past the end of an array, and
floats that are zeros of both signs, infinities, NaN, and the smallest subnormal.  Native Lean
returns the canonical NaN for every NaN result, and the host enables Cranelift's NaN
canonicalization, so the cases compare float results bit for bit.  Native Lean writes a panic
message with a backtrace for each read past the end and returns 0, and for each update past the end
and leaves the array unchanged; the script counts these messages and fails on any other output to
standard error.  For each case that states the blocks it leaves allocated, the script also reads
the runtime's allocation and release counters after the call and requires the blocks still
allocated to be exactly the host's array arguments and the result's arrays, which shows that the
code releases every block it owns.  Cases that also bound the number of allocations show the
in-place updates and the growth by doubling: a loop of `n` pushes allocates at most
`2 + log₂ (n + 1)` blocks, and an insertion sort of `n` elements at most `3 + log₂ (n + 1)` with the
host's array.  One case builds an array of `2^29` words and must trap
at `unreachable`.

The script then runs five native checks of the numerical examples, which the compiler's theorem
does not cover, since it states that the module computes the Lean definitions and says nothing about
how well those definitions approximate their mathematical counterparts.
[`Reference.lean`](Examples/Reference.lean) computes exact references with Lean's integers and
states the error that each of its truncations leaves.
[`TrigAccuracy.lean`](Examples/TrigAccuracy.lean) compares the words of `2/π` and `π/2` in
`Trig.lean` with those computed from Machin's formula for `π`, and requires each of 360,022 results
of `Trig.sin` and `Trig.cos` to lie within one unit in the last place of a reference computed with
Lean's integers.  It reports the C library's distance from the reference for information: glibc's
`cos` lies 8 units from it at `6381956970095103 · 2 ^ 797`, the double closest to a multiple of
`π/2`.  [`ExpAccuracy.lean`](Examples/ExpAccuracy.lean) compares the table of `Exp.lean` with
`2 ^ (j/128)` and requires each of 180,085 results of `Exp.exp` to lie within one unit of the
correctly rounded value, from arguments over the whole range in which `exp` is finite and positive,
near its thresholds, and at the special values.  [`TanhAccuracy.lean`](Examples/TanhAccuracy.lean)
requires 184,589 results of `Tanh.expm1` to lie within one unit, the bound that fdlibm states, and
160,073 results of `Tanh.tanh` within two units, the largest distance it finds.  fdlibm states no
bound for `tanh`, and glibc's `tanh` lies two units from the reference at the same 74 arguments.
[`LogAccuracy.lean`](Examples/LogAccuracy.lean) compares the tables of `Log.lean` with the centers
they describe and requires 340,066 results of `Log.log` to lie within one unit.
[`FourierAccuracy.lean`](Examples/FourierAccuracy.lean) checks on 20 signals the facts that hold
exactly in floating point, such as the transform of an impulse, and, within a tolerance `τ` from the
error bound of recursive summation, single frequencies, the round trip, Parseval's identity,
agreement with the exact transform computed with Lean's integers, and the power spectrum of a real
wave.  The results lie within `0.1 τ` of the exact transform.

## Related work

[The journal](../devnotes.md) records the analysis that led to this library and its plan.  The
`LeanExe` rule for expressions, `Expr.program_spec` in
[`LeanExe/IR/Expr.lean`](../LeanExe/IR/Expr.lean), proves the same kind of fact for one IR program
at a time.  [`Scale`](../Examples/Scale/README.md)
and [`Axpy`](../Examples/Axpy/README.md) are the closest programs of the `LeanExe` compiler.

## References

- X. Leroy, "Formal Verification of a Realistic Compiler," *Communications of the ACM*
  52(7):107–115, 2009.
- E. Mullen, S. Pernsteiner, J. R. Wilcox, Z. Tatlock, and D. Grossman, "Œuf: Minimizing the Coq
  Extraction TCB," *Proceedings of CPP 2018*.
- WebAssembly Core Specification,
  [numerics](https://webassembly.github.io/spec/core/exec/numerics.html).
