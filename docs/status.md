# Capabilities and limits

LeanExe compiles a defined Lean dialect to WebAssembly, runs substantial example
programs, and supports general compiler proofs for an admitted scalar subset as
well as direct proofs of exact binaries. This page summarizes the boundaries;
the [language specification](spec.md), [theorem inventory](../proofs/talos/README.md),
and individual artifact manifests provide the detailed contracts.

## Compiler and runtime

| Capability | Supported behavior |
|------------|--------------------|
| Lean source | Concrete scalar and heap types, specialization of resolved class evidence, supported structures and inductives, first-order helpers, and recognized recursion forms. |
| Control flow | Conditionals, local bindings, supported pure and monadic `do` forms, loops, folds, and supported `continue`/`break` forms. The source recognizers determine which elaborated shapes are admitted. |
| Heap values | Arrays, byte arrays, flattened records and variants, and internal recursive data, with reference counting and compiler-inserted release at supported ownership boundaries. |
| Callable modules | One or several public exports sharing memory, allocation, reference counts, and internal helpers. |
| Pure WASI commands | Bounded stdin and arguments, stdout/stderr, and explicit error results around pure entries. |
| Byte I/O | Sequenced stdin reads and stdout writes with operation timeouts, partial-transfer handling, EOF, and explicit WASI errors through the nonblocking host. |
| Floating point | Compiler-recognized FP32/FP64 operations over raw word encodings and packed tensors. General Lean `Float` source is outside this interface. |
| Serialization | Native binary and WAT emitters over the same structured instructions. An experimental WASM binary emitter supports the module-image path. |

The [user manual](manual.md) gives accepted source patterns, command modes,
and ownership guidance. Library callers must follow the
[ABI](spec.md#wasm-module-abi); byte-I/O callers must provide the specified
nonblocking WASI contract.

## Programs and proof coverage

| Program or proof family | Established boundary | Remaining limit |
|-------------------------|----------------------|-----------------|
| [Scalar compiler](arithmetic-correctness.md) | General source-to-exact-byte correctness, full module validation, export lookup, and terminating invocation for every admitted scalar declaration. Covers supported UInt64 operations, typed Boolean locals, bindings, conditions, Id control, local functions, and one bounded strided range loop. | Broader dialect coverage, including heap values, top-level helper calls and general loop combinations, is outside this theorem. |
| [Independent core type safety](type-safety.md) | Preservation and progress for the independent core, including bounded naturals, fixed-width words, strict products/sums, direct calls, persistent arrays, and nominal recursive data. | The full runtime-language model and its connection to production extraction remain incomplete. |
| [FP32 GPT-2](gpt/README.md) | Exact cached-step and 128-position session proofs, including input rejection, initialization, cache/logit values, allocation, and release. A separately identified binary has exact-byte proofs. | Real-arithmetic error bounds and formal equivalence with full-prefix inference remain open. The source model and a packaged binary are distinct proof subjects. |
| [Quantized GPT-2](../data/gpt2-quantized-v1/README.md) | Signed INT8 projections, grouped activation arithmetic, complete cached-session and exact-binary proofs, termination, memory conditions, and cleanup. | Propagated numerical bounds certify no greedy choices on the evaluated prefixes. Measured-logit certificates cover specified individual choices under their stated assumptions. |
| [Tiny GPT](gpt/README.md#models-and-results) | Four-byte checked-entry execution, weight validation/clipping, and real-arithmetic output/error bounds. | The unconditional bound is too coarse for useful precision; the 128-position model's complete execution proof is open. |
| [Euler solvers](../data/euler-reconstructed-v1/README.md) | Exact-binary complete calculations for grids of size 2 through 800, termination and a 512 MiB memory bound. The reconstructed solver proves accepted state/face safety, hyperbolicity, CFL conditions, and conservation with bounded rounding residuals. | Convergence to a continuous entropy solution is not proved. Physical and numerical conclusions retain the theorem's acceptance conditions. |
| [Conservation-error observer](../plans/euler-certificates-and-convergence.md) | Generated-WASM execution and memory proofs for interval totals, boundary contributions, trial/retry control, and complete output. | The exact-byte observer package remains open. |
| [Numerical kernels](../data/numerical/README.md) | Execution and real-arithmetic error bounds for exponential, softmax, LayerNorm, GELU, and specified Euler operations. | Each numerical theorem has a stated input domain and arithmetic model. |
| [CLOB and generated programs](../proofs/talos/README.md) | Registered behavioral specifications for the eight CLOB exports, plus independently checked generated-program packages. | Guarantees are attached to the named program and theorem; proof generation is not guaranteed to succeed for arbitrary requests. |
| [Byte I/O](../proofs/byte-io/README.md) | Modeled host contracts, transfer protocol laws, and six exact echo-binary execution cases. | General source-to-WASM I/O refinement and native-host implementation correctness are not proved. |
| [Running sum](../proofs/running-sum/README.md) | Source-level cumulative sums, output order and EOF behavior under successful-I/O assumptions; exact binary decoding, validation, and import/export checks. | Universal compiled-WASM execution and memory correctness remain open. |

## Verification tools

| Check | Purpose |
|-------|---------|
| `tools/arithmetic-check.js proof` | Build the general scalar compiler theorem and audit its axioms. |
| `tools/arithmetic-check.js subset-engine <name>` | Compare native Lean results with emitted WASM for a selected registered test group. |
| `tools/talos-proof.js check <case>` | Regenerate a source-driven execution model, require agreement with its proof cache, and check its specification. |
| `tools/artifact-proof.js check <binary> <target>` | Check an exact binary against its artifact package and named theorem. |
| `tools/artifact-conformance.js check` | Exercise the pinned WASM semantics and artifact decoder/validator against the configured official corpus. |
| `node test/run_all.js` | Run the complete compiler/runtime execution suite. |
| `tools/check-wat.sh` | Compare binary output with parsed compiler-emitted WAT. |
| `node tools/check-docs.js` | Check maintained documentation links and references. |

Run focused checks while developing and the checks required by the affected
boundary before completion. [Developing LeanExe](../DEVELOPING.md) specifies the
pinned environment, serial Lean runner, test selection, and aggregate commands.
The [active task](../task.md) records performed checks and concrete next steps.
Artifact manifests bind proofs to bytes; a successful check of one artifact
does not certify a different binary. Release-record identities can be inspected
with `tools/artifact-release.js inspect`.

## Trust and open work

Lean checks theorem terms against their definitions and allowed logical axioms.
Exact-artifact proofs connect embedded bytes to the modeled execution; they do
not assume that the source compiler is correct. Compiler correctness is proved
separately for its admitted scalar language. Neither route proves Lean's own
logical consistency.

Native hosts, Wasmtime, the operating system, hardware, tokenizers, and sampling
implementations remain outside the Lean proof. Their execution is tested against
the relevant interfaces. I/O theorems assume modeled host behavior and stated
clock progress; floating-point theorems specify their arithmetic and NaN rules.

The [roadmap](../plan.md) and [detailed plans](../plans/README.md) organize work
on broader compiler coverage, runtime-language type safety, complete I/O
refinement, exact observer artifacts, and numerical guarantees. Each compiler
increment must connect admitted source to actual emitted WASM and retain the
corresponding execution evidence.
