# LeanExe

LeanExe compiles Lean 4 programs to WebAssembly and supports proofs about their
execution. Write a program in Lean, load its checked declarations, and compile
them into callable WASM exports or a command with byte input and output.

The examples include **GPT-2 text generation**, **two-dimensional Euler flow
solvers**, streaming commands, JSON processing, and numerical kernels. The
compiler supports a defined subset of Lean: machine integers, arrays, byte
buffers, structures, supported inductives and recursion, conditionals, `let`,
`do`, and loops. The [language specification](docs/spec.md) defines the accepted
source forms, memory representation, and host interface.

Verification has two complementary paths. A general compiler theorem covers
an admitted scalar and bounded-loop language. For larger programs, exact-artifact
proofs establish behavior directly from a particular WASM binary's bytes. Both
paths use Lean to check the proofs; their scope is described below.

## Get started

Follow [Developing LeanExe](DEVELOPING.md#prerequisites) to configure the pinned
Lean, Node.js, Wasmtime, C compiler, and `wasm-tools` dependencies on Linux or
ARM macOS. Run the commands below from the repository root in that environment.
Direct Lean, Lake, and compiler commands use `tools/leanrun`; repository drivers
invoke it themselves. Build the compiler with:

```sh
tools/leanrun --timeout 15m lake build lean-wasm
```

## Run GPT-2 in WebAssembly

The [GPT examples](docs/gpt/README.md) implement transformer inference in Lean.
Pretrained GPT-2 124M uses twelve transformer blocks, packed FP32 weights, and
an attention cache retained between token calls. A quantized variant uses INT8
weights and grouped activations for its projections, with FP32 computation
around them. Both generate text through a resident Wasmtime instance.

Install `uv` in addition to the development dependencies, then fetch the pinned
checkpoint and run either model:

```sh
uv run --project training/gpt2 training/gpt2/reference.py fetch

tools/gpt2 --text 'Once upon a time, in a small village' --generate 32

tools/gpt2 --quantized \
  --text 'Once upon a time, in a small village' --generate 32
```

The commands prepare the required packed weights. The FP32 command compiles the
Lean model; `--quantized` loads the exact verified binary named in its model
manifest. Prompt and completion together are limited to 128 tokens. Use
`--top-k 1` for greedy decoding or `--json` for token IDs, binary identity,
timing, and allocation information. The CPU reference runs with:

```sh
tools/gpt2-pytorch --text 'Once upon a time, in a small village' --generate 32
```

The [FP32 example](data/gpt2-124m/README.md) and
[quantized example](data/gpt2-quantized-v1/README.md) include reference
comparisons, completions, memory measurements, and proof instructions. Quantized
weights occupy about 128 MB, versus 498 MB for FP32 parameters. Quantization can
change token choices; execution correctness and numerical accuracy are separate
claims. Smaller [byte-token GPT models](docs/gpt/README.md#models-and-results)
provide examples of real-arithmetic error bounds.

## Compile a Lean function

[`Arithmetic.choose`](LeanExe/Examples/Arithmetic.lean) is a complete scalar
example:

```lean
namespace LeanExe.Examples.Arithmetic

def choose (x y : UInt64) : UInt64 :=
  if x == 0 then y + 1 else x + y

end LeanExe.Examples.Arithmetic
```

Build its source module, compile it, and invoke the export:

```sh
tools/leanrun lake build LeanExe.Examples.Arithmetic

tools/leanrun .lake/build/bin/lean-wasm compile-arithmetic \
  --module LeanExe.Examples.Arithmetic \
  --entry LeanExe.Examples.Arithmetic.choose \
  --out build/choose.wasm

"${WASMTIME:-build/tools/wasmtime/current/wasmtime}" run \
  --invoke choose build/choose.wasm 0 41
```

The result is `42`. `compile-arithmetic` accepts only the language covered by
the [general compiler correctness theorem](docs/arithmetic-correctness.md),
including supported scalar operations, local bindings and functions,
conditionals, pure `Id` blocks, and one bounded range loop with supported
`continue` and `break` forms.

Use `compile` for the broader dialect, including heap values and supported
recursive helpers. `--entries Name.one,Name.two` exports several declarations
with shared helpers and memory. Use `compile-wasi-io` for a `LeanExe.ByteIO UInt32`
entry with sequenced stdin reads and stdout writes. Pure WASI adapters also
support bounded stdin, arguments, output, and explicit error results.
The [user manual](docs/manual.md#entry-shapes) explains which command to choose.

## Explore the examples

| Example | What it demonstrates |
|---------|----------------------|
| [GPT inference](docs/gpt/README.md) | FP32 and quantized GPT-2, cached text generation, exact execution proofs, and numerical bounds for smaller models. |
| [Reconstructed Euler solver](data/euler-reconstructed-v1/README.md) | A complete 2D flow calculation in WASM, with termination, memory, accepted-state safety, and conservation theorems; includes 192 × 192 and 800 × 800 results. |
| [Numerical kernels](data/numerical/README.md) | Exponential, softmax, LayerNorm, and GELU with execution and real-arithmetic error bounds on specified domains. |
| [Running sum](docs/manual.md#running-sum) | Interactive, signed decimal input and cumulative output using timed byte I/O and explicit error codes. |
| [JSON tree command](docs/demo.md) | Typed recursive data, parsing, transformation, and a WASI command interface. |
| [SplitMix64](docs/prng.md) | A Lean/WASM pseudorandom generator: `tools/prng.js 42 5 100` emits five values modulo 100 from seed 42. |
| [Generated programs](demos/README.md) | Specifications, programs, and independently checked artifact proofs produced through `leanexegen`. |

Byte-I/O programs use the repository's nonblocking WASI host, which provides the
clock and polling behavior required by operation timeouts. The
[I/O guide](docs/manual.md#byte-input-and-output) gives build and run commands.

## What is proved?

| Proof path | Guarantee | Scope |
|------------|-----------|-------|
| [Compiler correctness](docs/arithmetic-correctness.md) | Every successfully admitted declaration emits exact bytes that decode, validate, and terminate with the source result in the pinned WASM semantics. | The specified scalar and bounded-range language accepted by `compile-arithmetic`. |
| [Exact-artifact verification](docs/artifact-format.md) | Embedded binary bytes decode and validate, translate to the execution model, and satisfy the named behavioral theorem. | The particular binary and the theorem's input, heap, and host assumptions. No compiler-correctness premise is needed. |
| [Independent core type safety](docs/type-safety.md) | Typed programs preserve their types and cannot become stuck under the core's execution rules. | The independently defined core language; connecting the whole compiler dialect to that core is a separate obligation. |

The [GPT proof guide](docs/gpt/README.md#proofs-and-evidence) distinguishes exact
inference, session allocation and cleanup, and numerical error bounds. The
Euler examples state their physical and numerical conditions alongside the
theorems. The [byte-I/O proofs](proofs/byte-io/README.md) cover modeled host
contracts, transfer laws, and concrete echo executions. Running sum has source
correctness and exact-binary decoding/validation proofs; its universal WASM
execution and memory theorem remains open.

LeanExe does not claim a general correctness theorem for every supported source
feature. Tests compare native Lean, supported IR evaluation, and WASM execution
where those references apply. Formal execution claims use the pinned Talos WASM
semantics; the native host, Wasmtime, and operating system remain outside the
Lean proof. Numerical theorems state their own domains and assumptions.

## Generate a program and its artifact proof

`leanexegen` uses separate headless Codex tasks for a specification, a Lean
program, and a proof about the compiled binary. The outer driver independently
checks the results. This workflow uses an `Array UInt64 → Array UInt64` public
interface and requires the [Codex setup and dependencies](docs/leanexegen.md).

```sh
tools/leanexegen -o myprogram.wasm myprogram.txt
tools/leanexegen verify myprogram.proof
tools/leanexegen run myprogram.wasm 10 20 30
```

The proof package contains the exact binary, specification, theorem, and
verification evidence. Compiler annotations and the knowledge forest supply
proof guidance and reusable lemmas; the resulting theorem must check against
the artifact. See [Verifying a Program](docs/verifying.md) for the manual path.

## Documentation and source

- **Use LeanExe:** [setup and testing](DEVELOPING.md), [user manual](docs/manual.md),
  [language and ABI](docs/spec.md), [GPT guide](docs/gpt/README.md).
- **Understand the proofs:** [compiler theorem](docs/arithmetic-correctness.md),
  [artifact proving](docs/artifact-proving.md), [theorem inventory](proofs/talos/README.md).
- **Work on the project:** [compiler architecture](docs/compiler.md),
  [capabilities and limits](docs/status.md), [roadmap](plan.md), [active task](task.md).
- **Browse further:** [documentation index](docs/README.md), [examples](LeanExe/Examples),
  [models](LeanExe/Models/Gpt2/README.md), [proof-generation demos](demos/README.md),
  [benchmarks](benchmarks/README.md), [papers](paper/README.md).

The compiler lives in `LeanExe/Extract`, `LeanExe/IR`, and `LeanExe/Wasm`.
The proof workspace is under `proofs/talos/lean`; exact packages are under
`proofs/artifacts`. The [experimental WASM binary emitter](docs/self-hosted-emitter.md)
provides a self-hosting example for the serialization stage.
