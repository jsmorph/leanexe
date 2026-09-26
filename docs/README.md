# Documentation

Start with the [project overview](../README.md), then choose a guide for the
program you want to run, write, or verify.

## Run and write programs

| Guide | What it covers |
|-------|----------------|
| [Setup and development](../DEVELOPING.md) | Pinned tools, Linux and ARM macOS setup, focused builds, tests, and diagnostics. |
| [User manual](manual.md) | Supported source patterns, compile commands, entry types, memory management, and authoring examples. |
| [Language specification](spec.md) | Accepted Lean dialect, numeric behavior, ABI, ownership, byte I/O, and rejection boundaries. |
| [GPT inference](gpt/README.md) | FP32 and quantized GPT-2, tiny byte-token models, run commands, data flow, and proof scope. |
| [Running sum](manual.md#running-sum) | Interactive byte input/output, signed decimal arithmetic, errors, and EOF. |
| [JSON tree command](demo.md) | A typed tree-processing program with a WASI command interface. |
| [Pseudorandom generator](prng.md) | SplitMix64 source, seed/count/modulus command, and execution tests. |
| [Numerical kernels](../data/numerical/README.md) | Executable exponential, softmax, LayerNorm, and GELU examples with numerical bounds. |
| [Euler flow solver](../data/euler-reconstructed-v1/README.md) | Complete 2D WASM calculations, exact-binary theorems, figures, and reproducible data. |

## Understand and check proofs

| Guide | What it covers |
|-------|----------------|
| [Scalar compiler correctness](arithmetic-correctness.md) | General source-to-exact-WASM theorem, admitted grammar, execution tests, and standalone proof package. |
| [Verifying a program](verifying.md) | Creating, registering, proving, and independently checking an artifact package. |
| [Artifact verification format](artifact-format.md) | Binary profile, embedded bytes, decoding, validation, and exact-artifact theorem boundary. |
| [Artifact proving](artifact-proving.md) | Talos, ProofKit, annotations, retrieval, generated proofs, and independent checking. |
| [`leanexegen` reference](leanexegen.md) | Specification/program/proof tasks, public interface, package verification, and reproving. |
| [Byte-I/O verification](../proofs/byte-io/README.md) | Modeled host contracts, transfer protocol laws, concrete exact-binary cases, and host assumptions. |
| [Theorem inventory](../proofs/talos/README.md) | Registered source-driven and exact-artifact theorems and their check commands. |
| [Proof strategies](proof-strategies.md) | Proof construction and diagnosis across artifact families. |
| [Imported-memory semantics](telos-bug.md) | The Talos imported-memory limitation, conformance scope, and artifact-profile restrictions. |

## Language models and compiler internals

| Guide | What it covers |
|-------|----------------|
| [Compiler architecture](compiler.md) | Extraction, specialization, proved scalar lowering, ownership, IR, and WASM emission. |
| [LeanExe type theory](typetheory.md) | Lean source theory, executable terms, runtime values, and artifact propositions. |
| [Fragment type theory](leanexe-type-theory.md) | Typing, representation, specialization, and ownership judgments. |
| [Independent core type safety](type-safety.md) | Preservation, progress, and the exact scope of the mechanized core. |
| [Type-safety coverage](type-safety-coverage.md) | Coverage by operation family and remaining model obligations. |
| [Runtime language](runtime-language.md) | Independent runtime syntax, typing, evaluation, and admissible errors. |
| [Formal compilation and execution specification](leanexe-formal-specification.md) | Compilation relations, operations, heap, ABI, WASI, and open obligations. |
| [WASM annotations](annotations.md) | Sidecar schema, instruction regions, checked adapters, and proof recipes. |
| [WASM binary emitter](self-hosted-emitter.md) | Experimental self-hosted serialization, module-image schema, and bootstrap checks. |
| [Architecture diagram](leanexe.png) | Compilation, annotations, execution, and proof flow. |

## Proof support and project work

| Guide | What it covers |
|-------|----------------|
| [Knowledge forest and LTG](ltg.md) | Lemma, tactic, guidance, and worked-example packages; retrieval and promotion. |
| [LTG metrics](ltg-metrics.md) | Measurements of declarations, tactics, coverage, and package structure. |
| [Capabilities and limits](status.md) | Implemented behavior, proof boundaries, and open work. |
| [Roadmap](../plan.md) and [detailed plans](../plans/README.md) | Priorities and completion conditions. |
| [Active task](../task.md) | Current instructions, checks, and next steps. |
| [Demonstrations](../demos/README.md) | Generated programs and their artifact-proof packages. |
| [Benchmarks](../benchmarks/README.md) | Proof-generation measurements, journals, and acceptance evidence. |
| [Research papers](../paper/README.md) | Publication sources, PDFs, and claim-to-theorem accounts. |

Use the language specification for accepted behavior, the theorem inventories
for formal claims, and the referenced manifests for exact binary identities.
