# Supported Lean definitions for the WGSL body compiler

This specifies `LeanExe.WGSL.Compile`, not the
[original GEMM template generator](gemm-template-interface.md). The compiler
reads the elaborated body of the declaration named by `#compile_wgsl`.
There is no requirement that it equal a predefined GEMM function.

## Declaration and invocation

```lean
import LeanExe.WGSL.Compile
open LeanExe.WGSL LeanExe.WGSL.Source

@[wgsl] def pointwise : Kernel := fun arithmetic a b row col =>
  arithmetic.add (a (row * 3 + col)) (b (row * 3 + col))

#compile_wgsl pointwise 2 3 6 6 "build/example-wgsl"
```

The annotation registers an eligible declaration. The command performs
translation, checking and emission. Merely attaching the annotation does not
generate a file. The declaration must be monomorphic, have a definition body,
and have this type, up to definitional equality:

```lean
ScalarArithmetic → (Nat → UInt32) → (Nat → UInt32) → Nat → Nat → UInt32
```

The five explicit parameters are the scalar operations, buffer A, buffer B,
output row and output column. The result is one binary32 word. `UInt32` is the
bit representation, not an instruction to use integer arithmetic in WGSL.
`ScalarArithmetic.add` and `.mul` select the floating-point primitives.

The four command numbers specify output rows, output columns, A's length and
B's length in words. The generated kernel writes C at `row * columns + col`.
The output directory must be new. It receives `kernel.wgsl`, `manifest.json`
and a reproducible Lean proof fragment; none is automatically committed.
Shader text is limited to 64 KiB and must be valid UTF-8.

## Accepted expression grammar

The following grammar describes elaborated expressions after transparent
helper calls, beta redexes and other supported weak-head reductions. A source
construct that computes away completely can therefore be accepted even if
there is no runtime translation for that construct:

```text
index := natural literal | row | col | enclosing fold index
       | index + index | index * index

word  := UInt32 literal | enclosing word local
       | a index | b index
       | arithmetic.add word word | arithmetic.mul word word
       | let wordLocal := word; word
       | let indexLocal := index; word
       | Source.fold literalCount word (fun indexLocal wordLocal => word)
```

`Source.fold n initial step` is an ordinary Lean definition using `Nat.rec`.
It returns `initial` for n=0; otherwise it invokes `step` for k=0 through n−1,
in increasing order, passing the previous accumulator. The compiler recognizes
this specific loop combinator, translates its callback body recursively and
emits a WGSL `for` loop. Nested folds are supported. Initial words need not be
zero. No assumption of algebraic associativity or commutativity is used.

Index-local bindings are substituted. Word-local bindings retain their value
in the emitted shader. The independent parser substitutes immutable shader
temporaries in its pure computation model. Transparent helpers must expose
the accepted grammar within a finite normalization budget: 256 recursive
index-translation steps and 512 word-translation steps along a path. These
are implementation limits, not support for arbitrary recursion.

Literal words must fit u32; both decimal literals and `UInt32.ofNat` of a
literal are accepted. Natural addition/multiplication syntax is accepted for
indices. UInt32 integer arithmetic, even though it has the same storage type,
is rejected. A custom typeclass instance cannot bypass the final checked
equality to the original source.

The subset does not directly translate conditionals, general pattern matching, dynamic
loop counts, general recursion, dynamic allocation, arbitrary array methods,
barriers, shared memory, atomics, subgroup operations or inter-invocation
communication. Opaque/axiomatic helpers without a supported visible body
cannot be translated. Unsupported input causes an error; there is no fallback
to the fixed GEMM template.

## Shape and access checks

Output rows and columns are positive and at most 524280, matching the
8×8 workgroup dispatch limit of 65535 groups in each direction. Each input
buffer and the output buffer has 1 through 33554432 words. Fold counts are
literal naturals at most 65535, including zero.

Indices are nonnegative. Their upper bounds are computed compositionally
using row < rows, col < columns and the enclosing literal fold limits. Every
literal and every intermediate addition/multiplication must fit u32, and each
read's upper bound must be below the associated input length. Zero-iteration
fold bodies are checked conservatively too. These checks can reject safe
programs outside this simple grammar; accepted programs do not rely on u32
wraparound for Nat indexing.

The dispatch wrapper has separate A/B read-only storage bindings, a C storage
binding, group 0 and slots 0/1/2, workgroup size 8×8×1, and an early return for
row/column values outside the output shape. The host must allocate the stated
buffers, keep C disjoint from A/B, and dispatch the stated grid.

## Correctness checks and limits

The compiler translates the Lean body into an expression tree and renders
WGSL. An independent parser then reads the actual emitted text, checks its
declarations, guard, arithmetic, scopes, exact loop control and final store,
and reconstructs its pure computation. It does not consult an expected GEMM
body or the emitter. Complete token consumption is required.
The accepted shader grammar uses compiler-style local names (`v`, `k` or
`acc` followed by decimal digits); it is not a general WGSL parser.

Lean checks two claims for each successful invocation:

1. The actual shader string parses into the recorded computation.
2. That parsed computation equals the supplied Lean definition, as functions
   of all five arguments, for every input buffer and arithmetic interpretation.

Checking occurs synchronously before file emission. All dependencies of the
two theorems are audited; only `propext`, `Classical.choice` and `Quot.sound`
are allowed. No `sorry` or native-computation axiom is accepted. Unsupported
source syntax, shader syntax, changed operations, failed equality proofs,
invalid shapes and out-of-range accesses prevent emission.

The parsed computation is a model of this explicit WGSL subset. There is no
machine-checked refinement of this model against a complete formalization of
the WebGPU/WGSL standard, and no proof of the external shader compiler or
device. The arithmetic argument must match the runtime's scalar policy.
Instantiating it with the existing pure IEEE32 add/mul gives the strict
separate-operation specification. Native WGSL implementations can differ on
fusion, subnormal handling and exceptional values; the execution tests do not
establish universal exact agreement on those cases. The new compiler does not
yet expose the old GEMM path's per-step fusion relation.

The static access checker is executable and covered by rejection tests; a
generic Lean proof of its soundness is not included in this implementation.
The existing GEMM dispatch/memory theorems have not been generalized to this
new grammar. These are explicit remaining proof obligations, separate from
the checked source-to-parsed-computation equality.

`#check_wgsl pointwise 2 3 6 6 "existing.wgsl" "build/checked-example"` applies
the same parser/equality gate to an existing shader. This supports tests that
change a valid shader operation and require rejection against the original
source definition.

See the [usage and test guide](body-compiler.md) and
[development journal](body-compiler-journal.md) for reproducible evidence.
