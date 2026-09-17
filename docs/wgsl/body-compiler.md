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
equality in Lean before writing any output files.

## Supported definitions

The entry has type
`ScalarArithmetic → WordBuffer → WordBuffer → Nat → Nat → UInt32`, abbreviated
`Source.Kernel`. The first argument supplies binary32 operations; the next two
are buffers of binary32 words, followed by output row and column. Operations
are `arithmetic.add` and `arithmetic.mul`, **not UInt32 integer addition or
multiplication**. The existing pure `Wasm.IEEE32` definitions supply the exact
floating-point interpretation in proofs and execution references.

Supported body constructs are word literals, A/B reads, the two arithmetic
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

The compiler generates `entry.wgslBody` and checks
`entry.wgslSourceCorrect : entry = entry.wgslBody.kernel` in Lean. This is a
source-to-expression-tree equality for all arithmetic interpretations and all
inputs, rather than a match against a fixed GEMM definition.

At this first implementation checkpoint, that equality does **not yet prove
the emitted WGSL text** implements the expression tree. A separate independent
shader parser and artifact check are being implemented. The old GEMM artifact
checker does not accept this new grammar.

Addition, multiplication, a 2×4 by 4×3 matrix multiplication and a mutation
replacing the product with addition have been compiled and executed using
native WebGPU on SwiftShader's Vulkan CPU device. All 24 output words matched
execution of the original Lean definitions using pure `Wasm.IEEE32` arithmetic.
These are bounded tests, not universal runtime-conformance proofs. Python only
allocates buffers, submits WGSL, reads results and compares words.

The ordinary WGSL f32 implementation still requires an arithmetic-profile
assumption for an exact IEEE32 correspondence on all inputs. A successful
sample run does not prove that every driver preserves subnormals, NaN choices
or separate multiply/add rounding.
