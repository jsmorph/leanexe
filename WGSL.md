# LeanEXE WGSL Backend Development Plan

There are two distinct implementations. The original GPT-2/GEMM path uses a
[fixed template](docs/wgsl/gemm-template-interface.md). The new
[body compiler](docs/wgsl/body-compiler.md) translates a restricted Lean
definition's expressions to WGSL. Its accepted definitions and proof boundary
are specified in the [source specification](docs/wgsl/lean-source-specification.md).
New GPT-2 builds compile their six dense-product definitions through the body
compiler. Older bundles retain the original template-artifact checker.

## Current verification focus

The completed parent FP32 cached-GPT-2 result was fetched on 2026-09-18.
The [parent integration plan](docs/wgsl/parent-integration-plan.md) records
its exact theorem scope, merge conflicts, source/ABI differences, and the
staged work to incorporate the compiled WGSL products into that model.
The parent is fetched but not yet merged into this branch.

The current implementation work is the [restricted Lean body compiler](docs/wgsl/body-compiler.md),
including a checked connection from parsed statement execution to its Lean
source. The [WGSL artifact fidelity work for pretrained GPT-2](docs/wgsl/gpt2-verification.md)
now connects those compiled definitions to the existing packed matrix specification.
Its objective remains to
prove that the six delivered shaders execute their selected Lean matrix-product
definitions over floating-point words, verify the matrix layouts and split
vocabulary computation, and state the arithmetic choices precisely. Numerical error bounds
and general Wasm/controller proof development are outside this workstream.
The older numerical milestones below are retained as development history.

## Implementation status

Development is underway on `wgsl`. See the [implementation record](docs/wgsl/README.md)
and [journal](docs/wgsl/journal.md) for checked milestones, commands, limitations,
and remaining proof obligations. The phases below remain the intended endpoint;
the existence of an interface or a runtime test does not mark its proof complete.

The current checkpoint includes a narrow Lean parser for the emitted GEMM
subset, a kernel-checked parse of the captured rectangular shader, and general
index/dispatch/u32 arithmetic lemmas. The invocation machine now has checked
termination, safety and dot-product correspondence, packaged with the exact
captured source. Full dispatch now has checked interleaving termination, memory
safety, unique writes, launch coverage and observable output correspondence.
The existing Talos proof workspace now supplies concrete binary32 arithmetic,
restricted exactness, and a composed GEMM error bound under explicit finite-input
and magnitude conditions. The generated rectangular shader also runs headlessly
on this ARM Mac's SwiftShader CPU device; all 15 output words match the reference.
See [generation, independent verification and execution instructions](tools/wgsl/README.md).
The one-command pipeline now checks the exact shader package and passes the
checked input snapshot directly to the native harness. Three matrix shapes and
three rejection cases pass its fixed corpus. The exact Wasm GEMM bridge now has
checked binary-section encodings, byte-transfer lemmas, and a small-step execution
theorem composed with the shader's exactness and numerical results. The native
bridge contract is explicit. The complete bundle gate now verifies both artifacts
before invoking the real Wasm function, executing its WGSL dispatch on the CPU,
and checking the results in Wasm memory. This completes the immediate GEMM and
host-composition plan. GPT integration is in progress: finite precision-conversion
models and wider binary32 accumulation bounds are checked, including gradual
underflow and separate or fused evaluation. The independent package gate now
checks both numerical domains through final Wasm memory. The selected 1×256×4
GPT vocabulary projection has checked dispatch correspondence and restricted
exactness. Its conversion, accumulation, promotion and binary64 bias error is
at most 0.0001 against the real head applied to the computed hidden row, for
every four-byte checkpoint input. `GptNumerical` composes this with the parent's
hidden-state error theorem against the complete real GPT model. Its uniform
epsilon-floor bound is extremely loose (approximately 4.85e9 per logit), so it
does not certify useful precision. The complete GPT artifact-execution bundle is now checked, including the
exact hidden Wasm, dispatch bridge, WGSL head, bias-addition Wasm and checkpoint
bytes. Its CPU corpus matches all 768 logits for three inputs and rejects three
changed-artifact cases. Native runtime/conversion conformance is explicit.
The requested server-side CPU scope is complete. A resident multi-input GPT
session reuses one native process, one weight upload and one pipeline while
checking every output. Five independently verified kernel candidates cover
residency, three-row batching and workgroup choices; all 84,480 output
checks (including warmups) pass. See [performance measurements and scope](docs/wgsl/performance.md).
Physical-GPU conformance and tighter full-model bounds remain future research.

## Purpose

Extend LeanEXE with a narrow WGSL compute backend so that a verified Lean program can produce a heterogeneous artifact bundle consisting of:

- a WebAssembly host artifact, verified using the existing LeanEXE/Talos path; and
- one or more WGSL compute-kernel artifacts, independently parsed and verified in Lean.

The initial target is GPT-2-class inference, with WGSL used only for tensor operations where GPU-style parallel execution provides meaningful benefit. The first kernel should be FP32 GEMM.

The intended endpoint is a pair of linked artifact-level theorems for the complete bundle.  The execution theorem connects the emitted Wasm and WGSL artifacts to a specified mixed-precision computation under an explicit execution profile.  The numerical theorem bounds every permitted result against the real-valued Lean GPT-2 specification.  Restricted profiles can support exact output equality with a specified floating-point computation.

## Design Principles

### Artifact-first verification

Generated WGSL is not accepted merely because the generator is believed correct. Lean parses the emitted WGSL artifact back into a formal representation and proves properties of that artifact.

This mirrors LeanEXE's Wasm approach: generator/compiler correctness can be useful, but it is not required to trust the final artifact theorem.

### Keep the WGSL subset small

Do not formalize all of WGSL initially. Let the kernels needed by GPT-2 determine the subset.

For the first GEMM implementation, the likely subset consists of:

- `f32` arithmetic;
- integer arithmetic for indexing;
- storage buffers;
- workgroup memory;
- workgroup/invocation identifiers;
- loads and stores;
- loops and simple conditionals;
- synchronization/barriers; and
- a deliberately small collection of types and declarations.

Softmax, LayerNorm, exponentials, square roots, and other transcendental operations should remain in Wasm initially unless profiling establishes a reason to move them.

### Explicit implementation profile

Define a small profile model describing permitted numerical choices within shared WGSL execution semantics.  A profile can admit several results.  A restricted profile can fix enough choices to permit an exact-result theorem for a particular kernel.

State the profile and runtime-conformance assumption in each artifact theorem.  Numerical bounds must cover every result admitted by the profile.  Exactness, successful termination, and absence of dynamic errors require proofs.

### Hints are not trust

LeanEXE compiler annotations may guide kernel selection, WGSL generation for supported kernels, tile dimensions, theorem selection, lemma instantiation, and verification tactics.

Annotations remain proof hints rather than axioms. A bad hint may make generation or verification fail; it must never make an incorrect artifact provable.

## Proposed Architecture

A checked Lean definition may be annotated as a WGSL kernel candidate.

```text
Lean specification / implementation
        |
        +---- LeanEXE Wasm compiler ------> Wasm artifact
        |
        +---- supported WGSL generator ---> WGSL text artifact(s)
                                              |
                                              v
                                      parse artifact in Lean
                                              |
                                              v
                                      formal WGSL semantics
                                              |
                                              v
                                        artifact theorem
```

At the application level:

```text
GPT-2 Lean specification
          |
          v
verified Wasm host  <---- formal WebGPU boundary ----> verified WGSL kernels
          \______________________________________________/
                              |
                              v
                     composition theorem
```

The Wasm artifact remains responsible for orchestration and, initially, most GPT-2 operations. WGSL is a tensor-compute accelerator rather than a replacement for the existing Wasm backend.

## Artifact Bundle

A model could produce:

```text
gpt2.wasm
kernels/
    gemm_f32.wgsl
    ...
manifest
proof metadata
```

The manifest identifies the exact artifacts, bindings, entry points, buffer layouts, dimensions, dispatch parameters, and assumptions participating in the composition theorem.  It also identifies the profile definition and its revision, the modeled WGSL revision, and any supported pipeline specialization values.

Artifact identity should ultimately be tied to the exact bytes/text consumed by the verifier and executor. Cryptographic hashes may be useful identifiers, but hashes are not substitutes for parsing and proving the artifact.

## Formal WGSL Model in Lean

The Lean development needs an AST and parser for the supported WGSL subset. The parser is essential because the theorem should concern the emitted artifact rather than merely the generator's internal AST.

Keep the semantic layers separable:

1. syntax, parsing, and validation;
2. scalar value semantics;
3. memory and buffer semantics;
4. invocation/workgroup semantics;
5. synchronization/barrier semantics;
6. kernel dispatch semantics; and
7. the WebGPU host/kernel composition boundary.

Only constructs actually emitted by LeanEXE need to be supported initially.

## WGSL Profile Model

### Profile components

A profile is a small record of permitted numerical choices.  Each component has an interpretation in the shared execution semantics.

| Component | Meaning |
|-----------|---------|
| Rounding | Permitted rounding results for each supported arithmetic operation. |
| Subnormals | Whether arithmetic preserves or flushes subnormal operands and results. |
| Signed zero | Permitted signs of zero results, including results of flushing. |
| Expression evaluation | Permitted evaluation orders and fused or separate operations. |
| Exceptional values | Permitted behavior for overflow, infinities, and NaNs. |

Scalar arithmetic and expression evaluation need separate definitions.  Evaluating `a * b + c` with separate multiplication and addition introduces two rounding steps.  Fused evaluation introduces one.  WGSL permits fusion and reassociation, and its `fma` can use separate operations.  The expression policy must describe which forms a profile admits, including how it interprets supported built-in calls.  The normative reference is [WGSL §15.7, Floating Point Evaluation, 17 August 2026 draft](https://www.w3.org/TR/2026/CRD-WGSL-20260817/#floating-point-evaluation).

V1 will model source-ordered evaluation with explicit choices about multiply-add fusion.  General reassociation requires a later definition of permitted expression transformations and their semantics.  Each profile states the restrictions assumed of its runtime.

Buffer layout, indexing, synchronization, and dispatch use shared semantics.  Input dimensions, buffer separation, scheduling assumptions, and resource requirements appear as theorem preconditions.  This keeps the numerical profile separate from kernel-specific conditions.

### Execution and refinement

The central relation has the schematic form:

```text
Exec profile kernel inputs outputs : Prop
```

Here `kernel` comes from parsing and validating the exact emitted WGSL.  The inputs include the relevant initial buffers and dispatch configuration.  The outputs describe the observable final buffer contents.  The relation permits every successful execution admitted by the profile and shared semantics.

Profile refinement means execution inclusion: if `narrow` refines `broad`, every execution admitted by `narrow` is admitted by `broad`.  Numerical bounds proved for `broad` therefore apply to `narrow`.  Refinement proofs must account for both arithmetic choices and expression evaluation.

Each supported profile needs consistent, nonempty choices on its advertised input domain.  For each supported operation and expression form, justify those choices against the pinned WGSL rules.  Kernel proofs establish successful termination and absence of dynamic errors under the stated scheduling and resource assumptions.  Output theorems require these existence and termination results because a relation describing only successful executions can otherwise be empty.

### Linked execution and numerical theorems

The artifact execution theorem connects `Exec` to a floating-point matrix-computation relation with explicit conversions and evaluation choices.  The numerical theorem bounds every result of that computation against real matrix multiplication.  Their composition gives an error bound for execution of the exact artifact.

An exactness theorem establishes that all permitted outputs equal a specified floating-point result.  It is a property of a kernel under a profile.  Fixed arithmetic choices still require proofs about concurrent memory accesses and observable output.  Exact bit-pattern equality also requires the profile to resolve every observable choice of zero sign and conversion result.

A first restricted exact profile can require source-ordered evaluation, round-to-nearest with ties to even, separate multiplication and addition, subnormal preservation, and specified signed-zero behavior.  The first GEMM theorem can assume finite inputs with explicit magnitude and dimension bounds, then prove that all intermediate results remain finite under every permitted evaluation.  Those range proofs discharge the exceptional-value cases within the theorem's domain.

Applying an artifact theorem to a runtime carries an explicit assumption that its shader compiler, execution system, and device satisfy the selected profile and shared semantics.  Record the implementation, configuration, and evidence supporting that assumption.  Test results provide evidence for the tested executions.  Universal runtime conformance remains an assumption unless established by a separate proof.

## FP32 Semantics

Implement or adapt a binary32 model in Lean and interpret the profile policies over it.  Given LeanEXE's existing binary64/Talos floating-point work, factor reusable machinery by exponent and significand widths where practical.

The initial GEMM semantics need at least:

- addition and multiplication;
- relevant conversions;
- rounding;
- infinities and NaNs;
- signed zero;
- subnormals; and
- fused operations if the profile permits them.

Represent permitted arithmetic results as a relation.  Connect scalar operations to the profile's expression-evaluation policy so that fusion choices enter both execution and error proofs.

Do not add transcendental semantics merely for completeness. They can be layered on later if GPU kernels require them.

## Kernel Proof Library

Raw operational semantics will not scale by themselves. Build a theorem library above them.

The first GEMM proof should link the parsed artifact to its floating-point computation, bound every permitted result against real matrix multiplication, and establish exact output under a restricted profile.  Successful termination and absence of dynamic errors accompany these output results.  Supporting lemmas should cover:

- indexing and bounds;
- correspondence between linear buffers and matrices;
- tile decomposition;
- workgroup partitioning;
- synchronization;
- accumulator behavior; and
- FP32 evaluation choices, profile refinement, and error bounds.

Artifact verification should reduce parsed kernels to these higher-level lemmas instead of repeatedly proving application properties by low-level execution.

LeanEXE annotations can select and instantiate these lemmas and tactics without becoming part of the trusted basis.

## Wasm/WebGPU Composition Boundary

The heterogeneous theorem requires a small formal host interface. Initially model only operations actually needed by the Wasm host:

- buffers and their contents;
- host/device initialization where applicable;
- bindings;
- dispatch dimensions;
- kernel entry-point selection;
- completion/synchronization;
- result visibility; and
- host reads where applicable.

The key result connects a Wasm-side abstract dispatch operation to execution of the particular verified WGSL artifact over the intended buffers.

Do not attempt to formalize an entire browser or the entire WebGPU API.

## Headless Execution and Testing

Testing is independent from proof and should be available before the formal semantics is complete.

Use a native WebGPU command-line harness rather than requiring a browser. `wgpu`/wgpu-native is a plausible implementation route. On a Linux server without physical GPU hardware, a software Vulkan implementation such as Mesa Lavapipe can provide an execution backend where supported.

The harness should:

1. load the exact emitted WGSL;
2. allocate and initialize buffers;
3. dispatch the kernel;
4. read results;
5. check results against the selected profile's reference relation or proved bound, using bit-pattern equality for profiles with a fixed reference result; and
6. optionally emit reproducible traces/test vectors.

These traces are valuable for engineering, differential testing, and later real-GPU testing. They do not replace the Lean proof.

Record the profile revision, runtime, backend, device, and execution configuration with each test.  Reproducible inputs can have several permitted outputs under a broader profile.

## Initial GPT-2 Decomposition

Keep the existing binary64 GPT-2 implementation in Wasm and initially move only dense tensor work.

Use the real-valued GPT-2 model as the shared mathematical specification.  The heterogeneous floating-point computation consists of binary32 tensor operations, binary64 host operations, and explicit conversions.  Give it its own execution and numerical theorems.  Retain the binary64 implementation's corresponding theorems against the same real model.

The heterogeneous error bound must include weight and activation conversions, binary32 accumulation, and propagation through the remaining Wasm operations.  Prove that the resulting intermediate values satisfy the input domains of reused Softmax, LayerNorm, and other component theorems.  Bounds for both implementations against the same real model also give a bound on their output difference.

GEMM is the first target because it provides a relatively small WGSL surface, accounts for substantial transformer computation, requires no transcendental functions, has a clean mathematical specification, supports reusable proof lemmas, and provides a meaningful acceleration experiment.

Only after GEMM works should additional operations be considered. Likely later candidates are other matrix/tensor and simple elementwise operations. Softmax and LayerNorm should move only when the performance/verification tradeoff warrants it.

For autoregressive GPT-2, dispatch and data-transfer overhead can dominate small operations. Long-term performance will likely require GPU-resident weights and selected activations plus fewer host/device transitions. This optimization is deliberately outside the first milestone.

## Order of Battle

### Phase 0 — Profile and theorem definitions

Define the supported profile policies, source-ordered and fused evaluation choices, and the execution relation.  State profile refinement, successful termination, numerical correctness, and restricted exactness as separate proof obligations.  Choose the first profiles and their input domains before emitting WGSL.  Record the intended runtime-conformance assumptions.

### Phase 1 — Minimal kernel generation

Add a LeanEXE annotation or equivalent mechanism selecting a supported Lean kernel definition for WGSL generation.

Implement a generator for one supported WGSL compute kernel. Establish the generation pipeline before requiring a complete proof.

### Phase 2 — Native headless execution

Build a minimal command-line WebGPU harness.  Execute generated kernels on a Linux server using a software backend where necessary.  Establish reproducible inputs, profile-aware result checks, artifact capture, and execution-configuration records.

### Phase 3 — WGSL syntax in Lean

Implement or adapt the required WGSL AST, a parser, and validation checks for the emitted subset.  Add round-trip and golden tests.

The verifier must consume the actual generated WGSL text.

### Phase 4 — Minimal operational semantics

Define value, control-flow, buffer, invocation, workgroup, synchronization, and dispatch semantics only for constructs required by the first kernels.

Interpret the profile components in these semantics.  Prove consistency of the supported choices and the initial profile-refinement results.

### Phase 5 — FP32

Integrate binary32 semantics with the WGSL model. Reuse/generalize LeanEXE's existing floating-point infrastructure where possible.

Validate the formal model against concrete edge-case test vectors, including rounding, subnormal handling, signed zero, and fused versus separate evaluation.

### Phase 6 — GEMM

Generate an FP32 GEMM kernel from Lean. Execute it through the native harness.

Prove successful termination, absence of dynamic errors, and correspondence between the parsed WGSL artifact and the profile's floating-point GEMM relation.  Prove an error bound covering every permitted result and exact output equality under the restricted profile.  Compose the execution and numerical results into an artifact-level error theorem.

Build reusable lemmas and tactics rather than a one-off proof.

### Phase 7 — LeanEXE proof annotations

Connect compiler annotations to theorem/tactic selection.

Ensure annotations remain non-normative: deleting or corrupting a hint may make verification harder or cause failure, but cannot establish an invalid theorem.

### Phase 8 — Minimal WebGPU host model

Define the small Wasm-to-WebGPU dispatch interface needed by LeanEXE.

Prove correspondence among host buffer state, bindings, dispatch parameters, and WGSL kernel execution.

### Phase 9 — Artifact composition

Prove a theorem for a bundle containing a verified Wasm host and one or more verified WGSL artifacts.

The theorem identifies the exact artifacts, execution configuration, profile, and runtime assumptions.  Compose execution relations and numerical bounds.  Prove exact output where the component results and profile support it.

### Phase 10 — GPT-2 integration

Replace appropriate Wasm tensor operations with calls to verified WGSL kernels and explicit precision conversions.

Prove execution correspondence with the mixed-precision specification and an error bound against the real-valued GPT-2 model.  Include conversion errors and the input-domain obligations of reused component theorems.  Prove exact mixed-precision output under a sufficiently restricted profile.

### Phase 11 — Performance work

Only after the basic theorem works:

- keep weights resident on the GPU;
- batch or fuse dispatches;
- add additional kernels;
- tune workgroup/tile sizes;
- consider additional numerical operations; and
- test real GPU implementations against the established profile.

## Non-goals for V1

Do not initially attempt to:

- formalize all WGSL;
- formalize an entire browser;
- formalize all WebGPU API behavior;
- prove a WGSL-to-native-GPU compiler;
- prove GPU hardware;
- support arbitrary user-written WGSL;
- implement every GPT-2 operation on the GPU;
- support every conforming WGSL floating-point behavior;
- introduce a general-purpose GPU IR without demonstrated need; or
- prove the WGSL generator correct as a prerequisite for artifact correctness.

A separate IR may eventually be valuable for multiple backends such as WGSL and PTX, but it is unnecessary for the first artifact-first WGSL experiment.

## Expected Research Result

The intended result combines execution and numerical theorems:

> Under the stated execution profile, input conditions, resource assumptions, and runtime-conformance assumption, this Wasm artifact and these WGSL artifacts terminate successfully and implement the specified mixed-precision GPT-2 computation.  Every permitted output satisfies the proved error bound against the real-valued GPT-2 specification.  For profiles with a proved exactness result, the output equals the specified floating-point result bit for bit.

The Wasm compiler and WGSL generator remain outside the soundness-critical path because the emitted artifacts are parsed and checked.  Applying the theorem to execution retains the explicit assumptions about the Wasm runtime and the WebGPU shader compiler, runtime, and device.

## Annotated References and Related Work

The references below have different roles. Some may provide formal structures worth adapting; others are methodological precedents or background. They should not automatically become LeanEXE dependencies.

### Most useful to the current development

**WGSL and WebGPU specifications.**  
Normative sources for syntax and permitted execution behavior. The Lean subset should document exactly which portions it models and where LeanEXE intentionally assumes a narrower execution profile. These are specification inputs, not software dependencies.

**Existing Lean WGSL/GPU formalization work (including VerifiedGPU-style work).**  
Especially worth examining before designing syntax, ASTs, and concurrency structures from scratch. The immediate value is likely architectural and representational. Unless its semantics align precisely with LeanEXE's requirements, treat it as guidance or a source for audited adaptation rather than a required dependency.

**LeanEXE and Talos.**  
The direct methodological and implementation foundation. Preserve the existing pattern in which the final proof is about the decoded/parsed artifact rather than trusting the compiler. LeanEXE's existing floating-point work should be generalized or reused for binary32 where appropriate.

**wgpu/wgpu-native and Mesa software backends such as Lavapipe.**  
Useful engineering infrastructure for a headless execution harness and CI. These are execution/test components, not proof dependencies. Their output provides empirical validation, not the correctness theorem.

### Particularly useful in spirit

**CUDA au Coq and other formal PTX semantics work.**  
Highly relevant as precedent for formal reasoning about GPU kernel artifacts and operational semantics. The proof assistant, target language, and final trust boundary differ from LeanEXE. Use this work primarily to guide decomposition of GPU semantics, concurrency, and artifact-oriented reasoning.

**CakeML / RealCake.**  
Useful methodological precedent for end-to-end refinement and floating-point-aware verified computation. RealCake is particularly relevant to theorem architecture connecting mathematical specifications, floating-point computations, and executable artifacts. It is not a literal dependency for the WGSL backend.

**cLean and related Lean GPU DSL work.**  
Useful for understanding ergonomic representations of GPU-oriented programs in Lean and proof-friendly kernel APIs. LeanEXE's distinguishing requirement is that the emitted WGSL artifact itself becomes the final proof target. Treat these projects as design guidance unless specific components are demonstrably reusable.

### Background rather than current implementation inputs

**GPUVerify.**  
Important prior work for CUDA/OpenCL race, barrier, and concurrency verification. It helps identify proof obligations that arise in parallel kernels, but it does not supply the desired Lean artifact-level floating-point refinement pipeline. It is therefore background rather than a critical-path component.

**SPIR-V formalization and verification work.**  
Potentially relevant if LeanEXE later needs a portable GPU binary format. For V1, introducing SPIR-V adds another translation and verification boundary before the WGSL experiment has demonstrated value. Revisit it if WGSL's semantic latitude becomes limiting or verifying that binary format becomes necessary.

**PTX semantics and NVIDIA-specific verification.**  
PTX is a plausible future backend if NVIDIA-specific semantics or performance control becomes important. It targets NVIDIA's instruction architecture, sacrifices WebGPU portability, and retains a PTX-to-machine-code translation boundary. It should not block the initial WGSL work.

**Formal transformer/neural-network verification, including TorchLean-style work.**  
Potentially useful for transformer specifications, tensor lemmas, and floating-point neural computation. This work generally addresses a different trust boundary from LeanEXE's concrete heterogeneous-artifact theorem, so it is background rather than an implementation dependency.

## How to Use Prior Work

Before incorporating an external formalization, classify the relationship:

1. **Dependency** — LeanEXE imports or directly relies on the implementation.
2. **Adaptation** — LeanEXE ports or incorporates a useful construction after auditing assumptions and licensing.
3. **Guidance** — the work influences architecture, theorem statements, or proof strategy but is absent from the trusted/build dependency graph.

Prefer guidance and small audited adaptations over unnecessary dependencies, especially in the artifact-verification core.

## Immediate Vertical Slice

The first milestone combines generation, execution, and both proof layers:

> A supported Lean matrix-multiplication definition is selected for WGSL generation.  LeanEXE emits an FP32 WGSL artifact, and a native headless harness executes that artifact under a recorded configuration.  Lean parses and validates the artifact.  Under the stated profile and preconditions, proofs establish successful termination, absence of dynamic errors, and correspondence with the floating-point GEMM relation.  A numerical theorem bounds every permitted result against real matrix multiplication.  A restricted-profile theorem establishes exact output equality with a specified floating-point computation.

The package records the profile definitions, theorem domains, runtime-conformance assumptions, and test evidence.  Runtime conformance and formal artifact correctness have separate evidence records.

This milestone deliberately excludes GPT-2 composition, sophisticated GPU residency, transcendental functions, and broad WGSL coverage.

Once this vertical slice exists, the next step is to invoke the verified GEMM artifact from the verified Wasm host and prove the host/kernel composition boundary. Only then should the complete GPT-2 heterogeneous artifact theorem become the primary integration target.
