# LeanExe

LeanExe compiles a subset of Lean 4 to WebAssembly. It produces callable functions
and commands with byte input and output. The project includes Lean-checked proofs
of application behavior for selected programs. Examples include terrain-following
drone routes, GPT-2 text generation, two-dimensional Euler flow solvers, JSON
processing, and numerical kernels.

The language includes machine integers, arrays, byte buffers, structures,
selected inductive types and recursion forms, conditionals, `let`, `do`, and
loops. The [language specification](docs/spec.md) defines the accepted source
forms, memory representation, and host interface.

The application proofs establish properties such as route optimality, continuous
terrain clearance, conservation balances, and numerical error bounds. Compiler
and execution proofs connect program behavior to source definitions; exact-artifact
proofs additionally identify the binary bytes. Coverage varies by program and
compiler mode. Each claim has a specific subject and assumptions, described
below and in [Proofs and limits](#proofs-and-limits).

## Get started

Follow [Developing LeanExe](DEVELOPING.md#prerequisites) to configure Lean,
Node.js, Wasmtime, a C compiler, and `wasm-tools` on Linux or ARM macOS.
Run the commands below from the repository root in that environment.
Direct Lean, Lake, and compiler commands use `tools/leanrun`; repository drivers
invoke it themselves. Build the compiler with:

```sh
tools/leanrun --timeout 15m lake build lean-wasm
```

## Terrain-following flight planning

[`Drone.compute`](LeanExe/Examples/Drone.lean) takes terrain elevations at
stations 100 distance units apart and returns an altitude and horizontal speed
at each station. This is the flight-planning computation: it chooses a route
through a finite graph of altitude and speed choices. The returned words define
a continuous trajectory through specified interpolation rules. For example:

```text
Terrain: [0, 20, 80, 40, 0]
Output:  [0, 0, 145, 10, 180, 15, 165, 10, 0, 0]
         alt0, speed0, alt1, speed1, ...
```

Inputs contain at most 64 unsigned elevations, each at most 1,000,000 relative
to a common datum. Empty or out-of-range inputs return an empty array. For every
accepted nonempty input, Lean proofs establish:

- **Feasibility and optimality.** The [source computation](proofs/talos/lean/Project/Drone/Output.lean)
  returns a feasible route with minimum travel time among all admitted routes
  in the finite graph, breaking ties by the sum of altitude excess above the
  clearance floor at the stations.
  Interior stations have 45 altitude-speed choices. This optimum is relative
  to those choices and the permitted motions between them.
- **Continuous flight constraints.** The [whole-flight theorem](proofs/talos/lean/Project/Drone/WholeFlight.lean)
  proves departure and arrival on the ground at rest, continuous position and
  velocity, and clearance throughout the flight. The clearance floor linearly
  interpolates terrain plus 100 units at interior stations and terrain height
  at the endpoints. Horizontal speed stays in [0, 20] and vertical speed in
  [-20, 20]. Horizontal and vertical acceleration magnitudes are bounded by 1
  and 4 between waypoint times, with one-sided bounds at the joins, where
  acceleration can jump. Speeds use distance units per second; accelerations
  use distance units per second squared. A single station gives a stationary
  flight of zero duration.
- **Execution of the WASM model.** The [execution theorems](proofs/talos/lean/Project/Drone/Spec.lean)
  prove termination, exact agreement with the source output, preservation of
  the input terrain, and a 64 MiB linear-memory bound, assuming a valid caller
  heap, a borrowed input array, and sufficient allocation headroom. Output
  agreement connects the modeled execution to the flight properties above;
  the execution theorem also covers empty and rejected inputs.

These flight guarantees use an ideal point mass, exact terrain interpolation,
and exact following of the prescribed trajectory. Vehicle dynamics, sensor
error, wind, and control-system tracking error are outside this model.

Drone currently has a proof about a generated WASM model. Connecting the emitted
binary to that model still relies on generation and comparison tools; a Lean
proof of its binary decoding, validation, and model identity remains open.
The drone uses arrays and recursive helpers, outside the general
`compile-arithmetic` theorem. The [drone report](paper/drone-verification-report/README.md)
explains the mathematics, proof targets, and recorded native Lean/Wasmtime
comparisons for its stated revision. Those comparisons are tests of concrete
runs; the source and modeled-execution theorems quantify over their input domains.

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
Lean model; its separately packaged exact-binary proof applies only to the binary
identified in that package. `--quantized` loads and checks the binary named in
its artifact manifest, whose proof covers the specified inference computation.
Prompt and completion together are limited to 128 tokens. Use
`--top-k 1` for greedy decoding or `--json` for token IDs, the binary hash,
timing, and allocation information. The CPU reference runs with:

```sh
tools/gpt2-pytorch --text 'Once upon a time, in a small village' --generate 32
```

The [FP32 example](data/gpt2-124m/README.md) and
[quantized example](data/gpt2-quantized-v1/README.md) include reference
comparisons, completions, memory measurements, and proof instructions. Quantized
weights occupy about 128 MB, versus 498 MB for FP32 parameters. Quantization can
change token choices. Execution proofs establish agreement with the specified
inference algorithm, including its floating-point approximations. Numerical
accuracy needs separate proofs: full FP32 GPT-2 124M error bounds remain open.
The quantized model's bounds are too coarse to establish all greedy token
choices. The [four-byte GPT model](data/tiny-gpt2-v1/README.md) has proved error
bounds, but they are too coarse to certify useful output precision.
Tokenization and sampling are outside the execution proofs. The theorems make
no claim about the factual accuracy of generated text. See
[proofs and evidence](docs/gpt/README.md#proofs-and-evidence) for the precise scope.

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
`continue` and `break` forms. The theorem proves preservation of the source
computation. Any claim that the source solves the intended problem requires
an application specification and proof of its own.

Use `compile` for heap values and supported recursive helpers.
`--entries Name.one,Name.two` exports several declarations
with shared helpers and memory. Use `compile-wasi-io` for a `LeanExe.ByteIO UInt32`
entry with sequenced stdin reads and stdout writes. Pure WASI adapters also
support bounded stdin, arguments, output, and explicit error results.
These broader compiler modes are outside the general compiler theorem;
individual programs can have separate execution or exact-artifact proofs.
See the [user manual](docs/manual.md#entry-shapes) for entry types and command options.

## Examples

| Example | What it demonstrates |
|---------|----------------------|
| [Drone flight planning](#terrain-following-flight-planning) | Source proofs of finite-graph optimality and continuous point-mass flight constraints, connected to execution of a generated WASM model. Exact-binary identification remains open. |
| [GPT inference](docs/gpt/README.md) | FP32 and quantized cached inference, execution proofs, identified binary packages, and separate numerical bounds with model-specific limits. |
| [Reconstructed Euler solver](data/euler-reconstructed-v1/README.md) | A complete 2D flow calculation with exact-binary execution, termination, memory bounds, positive density and pressure in accepted states, and conservation balances with rounding residuals. Convergence to a continuous entropy solution remains open. |
| [Numerical kernels](data/numerical/README.md) | Exponential, softmax, LayerNorm, and GELU with execution and real-arithmetic error bounds on specified domains. |
| [Running sum](docs/manual.md#running-sum) | Interactive, signed decimal input and cumulative output using timed byte I/O and explicit error codes. |
| [JSON tree command](docs/demo.md) | Typed recursive data, parsing, transformation, and a WASI command interface. |
| [SplitMix64](docs/prng.md) | A Lean/WASM pseudorandom generator: `tools/prng.js 42 5 100` emits five values modulo 100 from seed 42. |
| [Generated programs](demos/README.md) | Specifications, programs, and independently checked artifact proofs produced through `leanexegen`; the specification still needs review against the request. |

Byte-I/O programs use the repository's nonblocking WASI host, which provides the
clock and polling behavior required by operation timeouts. The
[I/O guide](docs/manual.md#byte-input-and-output) gives build and run commands.

## Proofs and limits

Read a verification claim as a theorem about a named source function, execution
model, or binary, under stated assumptions. Compilation alone does not establish
an application property. The main kinds of proof in this repository are:

| Proof | Guarantee | Scope |
|------------|-----------|-------|
| Application correctness, such as [drone flight safety](proofs/talos/lean/Project/Drone/WholeFlight.lean) | The specified computation satisfies a mathematical property, such as continuous clearance or a numerical error bound. | The named source computation, admitted inputs, and mathematical model. Physical applicability requires the model's assumptions to hold. |
| [Compiler correctness](docs/arithmetic-correctness.md) | Emitted bytes decode to a valid module whose exported function terminates with the source result in the WASM model. | Every declaration accepted by `compile-arithmetic`. |
| Generated-model execution, such as [Drone](proofs/talos/lean/Project/Drone/Spec.lean) | A particular WASM module represented in Lean terminates with the specified results and memory properties. | The modeled module and the theorem's input, heap, and host assumptions. Its connection to external binary bytes is a separate obligation. |
| [Exact-artifact verification](docs/artifact-format.md) | The identified bytes decode and validate as a WASM module. A behavioral proof for that same module establishes its specified behavior. | The binary, the available behavioral theorems, and their input, heap, and host assumptions. Compiler correctness is not assumed. Decoding and validation alone do not prove application correctness. |
| [Independent core type safety](docs/type-safety.md) | Typed programs preserve their types and cannot become stuck under the core's execution rules. | Only the independent core's syntax and semantics. Coverage does not extend to the whole LeanExe implementation. |

The [GPT-2 session proofs](docs/gpt/README.md#proofs-and-evidence) cover cached
token calls, allocation, and buffer release. The
[byte-I/O proofs](proofs/byte-io/README.md) cover modeled host contracts,
transfer laws, and concrete echo executions. Running sum has source
correctness and exact-binary decoding/validation proofs; its universal WASM
execution and memory theorem remains open.

General compiler correctness is limited to the `compile-arithmetic` grammar.
Tests compare native Lean, supported IR evaluation, and WASM execution where
those references apply; passing comparisons establishes agreement on the tested
cases. Formal execution proofs use the pinned Talos WASM semantics and trust
Lean's proof checker and the formal definitions. External file identity and
loading still depend on the checking tools. The native host, Wasmtime, operating
system, and hardware are outside the Lean proof.

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
results. An accepted proof establishes the formal specification supplied in
that package. Reviewing whether that specification captures the original
request remains necessary; the proof checker does not establish that connection.
[Verifying a Program](docs/verifying.md) describes manual proof
construction and checking.

## Documentation and source

- **Use LeanExe:** [setup and testing](DEVELOPING.md), [user manual](docs/manual.md),
  [language and ABI](docs/spec.md), [GPT guide](docs/gpt/README.md).
- **Understand the proofs:** [compiler theorem](docs/arithmetic-correctness.md),
  [artifact proving](docs/artifact-proving.md), [theorem inventory](proofs/talos/README.md),
  [drone development and report](paper/drone-verification-report/README.md).
- **Work on the project:** [compiler architecture](docs/compiler.md),
  [capabilities and limits](docs/status.md), [roadmap](plan.md), [active task](task.md).
- **Examples and reference:** [documentation index](docs/README.md), [examples](LeanExe/Examples),
  [models](LeanExe/Models/Gpt2/README.md), [proof-generation demos](demos/README.md),
  [benchmarks](benchmarks/README.md), [papers](paper/README.md).

The compiler code is in `LeanExe/Extract`, `LeanExe/IR`, and `LeanExe/Wasm`.
The proof workspace is under `proofs/talos/lean`; artifact proof packages are under
`proofs/artifacts`. The [experimental WASM binary emitter](docs/self-hosted-emitter.md)
runs binary serialization in WebAssembly.
