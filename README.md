# LeanExe

LeanExe compiles a subset of Lean 4 to WebAssembly. It produces callable functions
and commands with byte input and output. Examples include GPT-2 text generation,
two-dimensional Euler flow solvers, JSON processing, and numerical kernels.

The language includes machine integers, arrays, byte buffers, structures,
selected inductive types and recursion forms, conditionals, `let`, `do`, and
loops. The [language specification](docs/spec.md) defines the accepted source
forms, memory representation, and host interface.

A compiler correctness theorem proves that code accepted by `compile-arithmetic`
produces WASM with the same result as the source. Separate artifact proofs
establish properties of specific WASM binaries. Lean checks both kinds of proof.

## Get started

Follow [Developing LeanExe](DEVELOPING.md#prerequisites) to configure Lean,
Node.js, Wasmtime, a C compiler, and `wasm-tools` on Linux or ARM macOS.
Run the commands below from the repository root in that environment.
Direct Lean, Lake, and compiler commands use `tools/leanrun`; repository drivers
invoke it themselves. Build the compiler with:

```sh
tools/leanrun --timeout 15m lake build lean-wasm
```

## Run GPT-2 in WebAssembly

[GPT-2 124M](docs/gpt/README.md) runs a twelve-block transformer in Wasmtime
using FP32 weights and an attention cache. The quantized model uses INT8 weights
and activations, 32-bit integer accumulation, and FP32 rescaling for matrix
projections. Its other model operations use FP32. Weights and caches stay in
one Wasmtime instance between token calls.

Install `uv` in addition to the development dependencies, then fetch the pinned
checkpoint and run either model:

```sh
uv run --project training/gpt2 training/gpt2/reference.py fetch

tools/gpt2 --text 'Once upon a time, in a small village' --generate 32

tools/gpt2 --quantized \
  --text 'Once upon a time, in a small village' --generate 32
```

The commands pack the weights when needed. The FP32 command compiles the
Lean model; `--quantized` loads the verified binary named in its model
manifest. Prompt and completion together are limited to 128 tokens. Use
`--top-k 1` for greedy decoding or `--json` for token IDs, the binary hash,
timing, and allocation information. The CPU reference runs with:

```sh
tools/gpt2-pytorch --text 'Once upon a time, in a small village' --generate 32
```

The [FP32 example](data/gpt2-124m/README.md) and
[quantized example](data/gpt2-quantized-v1/README.md) include reference
comparisons, completions, memory measurements, and proof instructions. Quantized
weights occupy about 128 MB, versus 498 MB for FP32 parameters. Quantization can
change token choices. Execution proofs establish the implemented algorithm's
results; numerical proofs bound its error against real arithmetic. The
[four-byte GPT model](data/tiny-gpt2-v1/README.md) has proved numerical error bounds.

## Compile a Lean function

[`Arithmetic.choose`](LeanExe/Examples/Arithmetic.lean) uses wrapping `UInt64`
arithmetic:

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
including `UInt64` arithmetic, local bindings and functions, conditionals,
pure `Id` blocks, and one bounded range loop. The grammar specifies the accepted
`continue` and `break` forms.

Use `compile` for heap values and supported recursive helpers.
`--entries Name.one,Name.two` exports several declarations
with shared helpers and memory. Use `compile-wasi-io` for a `LeanExe.ByteIO UInt32`
entry with sequenced stdin reads and stdout writes. Pure WASI adapters also
support bounded stdin, arguments, output, and explicit error results.
See the [user manual](docs/manual.md#entry-shapes) for entry types and command options.

## Examples

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

## Proofs and limits

| Proof | Guarantee | Scope |
|------------|-----------|-------|
| [Compiler correctness](docs/arithmetic-correctness.md) | Emitted bytes decode to a valid module whose exported function terminates with the source result in the WASM model. | Every declaration accepted by `compile-arithmetic`. |
| [Exact-artifact verification](docs/artifact-format.md) | The identified binary decodes, validates, and satisfies its behavioral theorem under the WASM execution model. | The binary and the theorem's input, heap, and host assumptions. The proof does not assume compiler correctness. |
| [Independent core type safety](docs/type-safety.md) | Typed programs preserve their types and cannot become stuck under the core's execution rules. | The independent core's syntax and semantics. |

The [GPT-2 session proofs](docs/gpt/README.md#proofs-and-evidence) cover cached
token calls, allocation, and buffer release. The
[byte-I/O proofs](proofs/byte-io/README.md) cover modeled host contracts,
transfer laws, and concrete echo executions. Running sum has source
correctness and exact-binary decoding/validation proofs; its universal WASM
execution and memory theorem remains open.

General compiler correctness is limited to the `compile-arithmetic` grammar.
Tests compare native Lean, supported IR evaluation, and WASM execution where
those references apply. Formal execution proofs use the pinned Talos WASM
semantics. The native host, Wasmtime, and operating system are outside the
Lean proof.

## Generate a program and its artifact proof

`tools/leanexegen` reads a program request from a text file. Separate Codex tasks
generate a specification, a Lean implementation, and a proof about the compiled
binary. The tool checks the generated Lean files and artifact proof before
writing the program and proof package. Programs use an `Array UInt64 → Array UInt64`
public interface. Generation requires an [authenticated Codex CLI](docs/leanexegen.md).

```sh
tools/leanexegen -o myprogram.wasm myprogram.txt
tools/leanexegen verify myprogram.proof
tools/leanexegen run myprogram.wasm 10 20 30
```

The proof package contains the binary, specification, Lean proof, and check
results. [Verifying a Program](docs/verifying.md) describes manual proof
construction and checking.

## Documentation and source

- **Use LeanExe:** [setup and testing](DEVELOPING.md), [user manual](docs/manual.md),
  [language and ABI](docs/spec.md), [GPT guide](docs/gpt/README.md).
- **Understand the proofs:** [compiler theorem](docs/arithmetic-correctness.md),
  [artifact proving](docs/artifact-proving.md), [theorem inventory](proofs/talos/README.md).
- **Work on the project:** [compiler architecture](docs/compiler.md),
  [capabilities and limits](docs/status.md), [roadmap](plan.md), [active task](task.md).
- **Examples and reference:** [documentation index](docs/README.md), [examples](LeanExe/Examples),
  [models](LeanExe/Models/Gpt2/README.md), [proof-generation demos](demos/README.md),
  [benchmarks](benchmarks/README.md), [papers](paper/README.md).

The compiler code is in `LeanExe/Extract`, `LeanExe/IR`, and `LeanExe/Wasm`.
The proof workspace is under `proofs/talos/lean`; artifact proof packages are under
`proofs/artifacts`. The [experimental WASM binary emitter](docs/self-hosted-emitter.md)
runs binary serialization in WebAssembly.
