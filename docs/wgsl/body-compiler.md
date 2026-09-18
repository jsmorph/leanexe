# Lean definition body compiler

This is a separate implementation from the original fixed GEMM template
generator. `LeanExe.WGSL.Compile` reads the elaborated body of a named Lean
definition. Arithmetic operators, buffer indices, local bindings and fold
callbacks determine the generated WGSL computation.

```lean
import LeanExe.WGSL.Compile
open LeanExe.WGSL LeanExe.WGSL.Source

@[wgsl] def matrix : Kernel := fun arithmetic a b row col =>
  Source.fold 4 0 fun k acc =>
    arithmetic.add acc
      (arithmetic.mul (a (row * 4 + k)) (b (k * 3 + col)))

#compile_wgsl matrix 2 3 8 12 "build/my-matrix"
```

The four numbers are output rows, output columns, A elements and B elements.
The directory must not already exist. Run Lean through `tools/leanrun`, as
required by the repository instructions. The command checks the source
equality and statement execution theorem in Lean before writing any output files.

## Supported definitions

The entry has type
`ScalarArithmetic → WordBuffer → WordBuffer → Nat → Nat → UInt32`, abbreviated
`Source.Kernel`. The first argument supplies binary32 operations; the next two
are buffers of binary32 words, followed by output row and column. Operations
are `arithmetic.add` and `arithmetic.mul`, **not UInt32 integer addition or
multiplication**. The existing pure `Wasm.IEEE32` definitions supply the exact
floating-point interpretation in proofs and execution references.

Supported body constructs are finite binary32 word literals, A/B reads, the two arithmetic
operations, word and index local bindings, transparent helpers reducible to
these constructs, and `Source.fold count initial (fun k acc => ...)`. Fold
counts must be compile-time literals at most 65535. Index expressions contain
row, column, enclosing fold indices, natural literals, addition and
multiplication. Static checks reject possible buffer overruns and u32 index
overflow. There are no branches, data-dependent iteration, barriers, atomics,
shared memory, arbitrary recursion or general array manipulation in this
subset. Unsupported expressions cause compilation errors.

The generated shader has two read-only f32 buffers and one output buffer,
8×8 workgroups, an edge guard and one store per output cell. Each cell's
computation comes from the definition body. Changing `arithmetic.add` to
`arithmetic.mul`, including inside a fold, changes emitted operations.

## Verification status

The compiler independently parses the emitted shader text into `entry.wgslCode`,
which retains bindings and scoped loops. `entry.wgslShaderParsed` proves this
parse. `entry.wgslSourceCorrect` proves that its source interpretation equals
the supplied Lean definition. `entry.wgslExecutionCorrect` proves that execution
of those statements, the guard and the store returns the source value at the
correct address, for every invocation and input with adequate buffer lengths.
All three theorem dependency lists are audited before file emission.

The shared execution proof covers local lookup, checked reads, u32 indices,
accumulator updates, counter tests/increments, lexical scope and the checked
output store. It proves successful bounded execution, excluding all modeled
errors, rather than assuming success. The bound checker now has general
soundness and u32 correspondence proofs. Dispatch coverage and distinct output
addresses have separate shared proofs.

The parser checks the complete structured grammar, including the edge guard,
buffer declarations, operations, loop initialization/test/increment, scope and
sole output store. Checking is synchronous: failures and forbidden proof
axioms prevent file emission. The old GEMM artifact checker remains separate.

Eleven examples cover addition, multiplication, a 2×4 by 4×3 matrix
multiplication, changing its product to addition, helper functions, changed
indexing, nested folds, zero-iteration folds, a 1×768 by 768×3 product,
a constant-only kernel using the largest finite binary32 word, and a kernel
using only buffer A.
All have passed the three Lean
proofs and executed using native WebGPU on SwiftShader's Vulkan CPU device.
All 63 output words matched execution of the original Lean definitions using
pure `Wasm.IEEE32` arithmetic.
These are bounded tests, not universal runtime-conformance proofs. Python only
allocates buffers, submits WGSL, reads results and compares words.

Twenty-four rejection cases cover unsupported definitions, invalid dimensions,
buffer/index violations and altered shaders, including changed operations,
loop count, initial accumulator, output indexing, a removed edge guard,
incorrect counter increments, accumulator assignments and escaped locals.
They also cover both infinities, quiet/signaling NaNs, an unused NaN in an
otherwise correct shader, and a custom Nat addition instance that changes the
source computation. The latter must fail source equality rather than silently
being treated as ordinary addition.
Each rejection leaves no emitted package. The saved matrix proof also passed
a fresh Lean check without invoking the compiler.

The ordinary WGSL f32 implementation still requires an arithmetic-profile
assumption for an exact IEEE32 correspondence on all inputs. A successful
sample run does not prove that every driver preserves subnormals, NaN choices
or separate multiply/add rounding.

The remaining boundaries are a refinement of this subset semantics to a
complete formal WGSL semantics, external runtime conformance, and a general
interleaved GPU scheduler model for this new grammar. The proof uses the same
explicit scalar arithmetic on the source and statement sides. See the precise
[source specification](lean-source-specification.md). New GPT-2 builds use this
compiler for all six dense-product shaders; older bundles used the original
GEMM templates. The [GPT-2 verification record](gpt2-verification.md) describes
the connection to its packed matrix specification.

Run the bounded corpus on the configured Mac:

```sh
source tools/macos-env.sh
node tools/wgsl/body-test.js
```

It retains source, generated proof fragments, failed diagnostics, shaders,
Lean reference words and CPU execution reports under a fresh ignored build
directory. Node runs the checks sequentially; Python provides WebGPU host
bindings. Neither implements the tested numerical algorithm.
