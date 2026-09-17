# Original GEMM template interface

**The original `Generate.lean` implementation is a fixed GEMM template generator.
It does not compile a Lean function body to WGSL.** The separate body compiler
is documented in the [source specification](lean-source-specification.md).

This document specifies the implemented template-selection interface. It
supports one operation: row-major binary32 matrix multiplication, `C = A × B`,
with a source-ordered dot product for each output cell. Dimensions are selected
when the shader is generated; input matrix words are supplied at execution time.

A Lean definition can select this template precisely when:

1. It has type `LeanExe.WGSL.GemmImplementation`.
2. A checked Lean proof establishes that the definition equals
   `LeanExe.WGSL.gemmCell`.
3. The selected `GemmConfig` satisfies `GemmConfig.Valid`.

The first two requirements are represented by `KernelCandidate`. The third is
checked by generation. A successful generation result contains the WGSL text
and a proof of configuration validity. Correctness of that text is established
separately by the artifact checker.

## 1. Accepted definition type

The authoritative declarations are in
[Generate.lean](../../LeanExe/WGSL/Generate.lean):

```lean
structure ScalarArithmetic where
  add : UInt32 → UInt32 → UInt32
  mul : UInt32 → UInt32 → UInt32

abbrev WordBuffer := Nat → UInt32

abbrev GemmImplementation := ScalarArithmetic → GemmConfig → WordBuffer →
  WordBuffer → Nat → Nat → UInt32
```

The arguments are scalar arithmetic, matrix configuration, input buffer A,
input buffer B, output row, and output column. The result is one output word.
`UInt32` carries the raw binary32 representation. It does not mean that shader
multiplication or addition uses integer arithmetic. `WordBuffer` is a logical
index-to-word function; it does not allocate storage or establish a buffer's
physical size.

The reference definition starts with positive zero (`0x00000000`) and, for
`k = 0, …, inner - 1`, performs:

```text
product := arithmetic.mul A[row * inner + k] B[k * cols + col]
acc     := arithmetic.add acc product
```

The addition operand order is `acc, product`. The final accumulator is the
result of `gemmCell`. The emitted shader writes it to `C[row * cols + col]`.

The scalar parameter makes this definition independent of a particular
floating-point interpretation. The binary32 artifact proofs instantiate it
with `Project.WGSL.Binary32.arithmetic`.

## 2. Selection and the required equality proof

The current selection interface is this existing structure:

```lean
structure KernelCandidate where
  config : GemmConfig
  implementation : GemmImplementation
  loweringWitness : implementation = gemmCell
```

The equality field certifies the selected definition's meaning. Its type is
equality of the complete functions: it quantifies over every scalar-arithmetic
argument, configuration, input buffer, row, and column. Equality only for one
shape, one checkpoint, a finite set of inputs, or one floating-point
interpretation does not satisfy this field.

V1 has a semantic eligibility condition, rather than a grammar of accepted
Lean loops or operators. A definition may use helper functions or different
Lean syntax if its equality proof meets the condition above. The generator
does not inspect, translate, or execute the selected function body. It emits
the supported GEMM template using the candidate's configuration. The equality
proof is what connects that template's algorithm to the selected definition.

There is no `@[wgsl]` attribute or declaration-name compiler command in this
interface. A caller constructs a `KernelCandidate` and passes it to the
existing `LeanExe.WGSL.lowerCandidate` API. `generateGemm config` selects the
standard `gemmCandidate config` automatically.

### Selecting the template from Lean

This example uses only the compiler-side library and is checked as Lean code.

```lean
import LeanExe.WGSL.Generate

open LeanExe.WGSL

namespace SourceSpecificationExample

def myGemm : GemmImplementation :=
  fun arithmetic config a b row col =>
    gemmAccum arithmetic config a b row col config.inner

theorem myGemm_eq : myGemm = gemmCell := rfl

def shape : GemmConfig := { rows := 3, cols := 5, inner := 2 }

def candidate : KernelCandidate := ⟨shape, myGemm, myGemm_eq⟩

example : candidate.config.Valid := by decide +kernel

def generated : Except String GeneratedKernel := lowerCandidate candidate

-- After the artifact proof establishes the reference result, this equality
-- connects it to the selected Lean definition.
theorem selected_result (c : KernelCandidate) (arithmetic : ScalarArithmetic)
    (a b : WordBuffer) (row col : Nat) (output : UInt32)
    (checked : output = gemmCell arithmetic c.config a b row col) :
    output = c.implementation arithmetic c.config a b row col := by
  rw [c.loweringWitness]
  exact checked

#print axioms candidate
#print axioms selected_result

end SourceSpecificationExample
```

An axiom or `sorry` can syntactically inhabit an equality field in Lean. A
correctness claim requires auditing that proof as well as the artifact proof.
The supported artifact gates admit only `propext`, `Classical.choice`, and
`Quot.sound`; neither `sorryAx` nor native-computation axioms are accepted.

The generic package checker proves correspondence to `gemmCell`; it does not
discover a user-defined candidate, audit that candidate automatically, or
automatically emit `selected_result` for it. A custom caller must check the
candidate proof, match the parsed configuration to the candidate configuration,
and compose the equality as above. The existing GPT-2 checker specializes its
own named matrix-product theorems explicitly.

## 3. Configuration restrictions

These are the exact conditions in `GemmConfig.Valid`. All fields are natural
numbers. Let `M = rows`, `N = cols`, `K = inner`, `X = workgroupX`, and
`Y = workgroupY`.

| Item | Required condition |
| --- | --- |
| Dimensions | `1 ≤ M, N, K ≤ 4,294,967,295` |
| Buffer element counts | Each of `M*K`, `K*N`, and `M*N` is at most `33,554,432` |
| Bind group | `group < 4`; A, B, and C share that group |
| Binding numbers | Each is below `1,000`; A, B, and C have distinct binding numbers |
| Workgroup dimensions | `1 ≤ X, Y ≤ 256`, `X*Y ≤ 256`; Z is fixed at 1 |
| Dispatch dimensions | `ceil(N/X) ≤ 65,535` and `ceil(M/Y) ≤ 65,535`; Z is fixed at 1 |

The buffer cap is 128 MiB at four bytes per element. These are the generator's
supported limits; the execution device must also support the selected sizes.
The default configuration uses group 0, bindings A=0/B=1/C=2, and an 8×8×1
workgroup. Dimensions, bindings, and workgroup size are constants in each
generated shader. Changing them requires another generated instance.

Execution supplies separate A/B/C storage objects with at least `M*K`, `K*N`,
and `M*N` elements. A and B are read-only inputs. Initial C contents do not
contribute to the active output cells. There is no `alpha*A*B + beta*C` term,
bias, activation, or accumulation into a previous C value in this kernel.

## 4. Emitted WGSL and checking restrictions

Each global invocation computes one output cell. Its X coordinate selects the
column; Y selects the row. An invocation outside M×N returns before accessing
a buffer. Active invocations execute K sequential accumulator updates and one
output store. The launch rounds up to whole workgroups.

[Parse.lean](../../LeanExe/WGSL/Parse.lean) independently checks a fixed body
grammar: the edge guard, indices, loop, arithmetic operand order, positive-zero
initialization, and output store. It also checks constants, bindings, workgroup
size, and end of input. Its lexer admits supported whitespace and comments.
Different WGSL bodies, including mathematically equivalent rewrites, are not
automatically supported. The parser does not infer a GEMM meaning from an
unrecognized body.

The current template has no shared-memory tiling, barriers, atomics, SIMD
reduction, batching dimension, or data-dependent control flow beyond its guard
and fixed loop. A `rows` value above one is ordinary matrix multiplication;
it does not introduce a batch of independent matrices.

## 5. Meaning of correctness

Under `leanexe-f32-rne-separate-v1`, the independently checked shader computes
exactly `gemmCell Binary32.arithmetic config A B row col` at every active cell.
Composing the candidate equality gives the selected Lean definition's result.
The profile uses nearest/even rounding, preserved subnormals, IEEE zero signs,
and the specified exceptional-word behavior, including canonical NaNs.

Under `leanexe-f32-rne-fusion-v1`, each source-ordered update may instead use
one rounded fused multiply-add. For the GPT-2 matrix products,
`ArithmeticChoice.evaluate` and `Matrix.fusion_from_dispatch` prove exact word
equality to a Lean computation with a concrete per-step choice sequence. This
does not assert equality to the separate-only function for every fusion choice.
The generic GEMM package exposes the corresponding `Dot` relation.

Both interpretations preserve accumulation order. General reassociation and
alternate subnormal/exceptional-value policies are outside these profiles.
Runtime conformance to a profile is an explicit assumption. Generation does
not establish that a particular GPU compiler or device implements it.

Termination, memory safety, dispatch coverage, and disjoint output writes are
proved for the modeled kernel with its stated buffer and execution premises.
Word correspondence requires no weight-magnitude bound, real-number reference,
or error tolerance. See the [GPT-2 verification specification](gpt2-verification.md)
for the matrix-layout and arithmetic theorems.

## 6. Current command-line interface

From a configured repository root, this emits the standard GEMM candidate and
then checks its word semantics. The output directory must be fresh.

```sh
source tools/macos-env.sh # configured ARM Mac only
tools/leanrun --timeout 60s lake env lean --run tools/wgsl/Generate.lean build/wgsl/source-spec-example 3 5 2 separate
tools/artifact-proof.js wgsl-word-check build/wgsl/source-spec-example
```

The dimensions mean a 3×2 matrix multiplied by a 2×5 matrix. This CLI accepts
dimensions and a profile; it does not accept a Lean declaration name or custom
candidate. Library callers can select other valid bindings/workgroups and
construct a candidate explicitly.

## 7. Acceptance examples and extensions

| Proposed definition or configuration | Current template interface |
| --- | --- |
| `gemmCell` at a valid shape | Supported through `gemmCandidate` |
| A wrapper or another implementation with type `GemmImplementation` and a checked proof of full equality to `gemmCell` | Supported through `KernelCandidate` |
| A specialized `Array Float → Array Float` function | Not the accepted interface; it needs a suitable GEMM representation and proof |
| Equality established only for the current weights or dimensions | Insufficient for the candidate equality field |
| Dot product with reordered additions, a different initial accumulator, or reversed scalar operands | Requires the stated equality proof; algebraic equality over the reals does not supply it |
| Matrix multiplication with an added bias, softmax, GELU, layer normalization, or attention | No corresponding WGSL operation in this interface |
| Zero dimensions, overlapping binding numbers, or an exceeded configuration limit | Rejected by configuration validation |
| A different tiling or reduction algorithm in WGSL | Requires additional emitted syntax, execution semantics, and artifact proofs |

Adding a new supported operation requires its Lean interface and word-level
specification, an explicit selection rule, a generator, an independently checked
WGSL syntax/semantics path, and the corresponding artifact theorem. Adding a
source annotation alone would not provide those capabilities.

## 8. Separate body compiler

`LeanExe.WGSL.Compile` now implements a separate expression-body compiler. It
does not use `KernelCandidate` or require equality to `gemmCell`. This original
template path remains in use by the GPT-2 bundle; adding the new compiler has
not migrated that bundle. See the [body compiler guide](body-compiler.md).
