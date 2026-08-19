# Proof-Grade `f64` Artifact Semantics

**Status:** Deferred pending an implementation design review.  The current exact-artifact profile covers integer programs, while Talos executes floating-point instructions through opaque native `Float` operations.  This plan defines the proof boundary, implementation order, acceptance gates, cost, and risks for proof-grade binary64 support on Lean 4.31.0.

## Scope and theorem boundary

LeanExe will preserve its exact-artifact boundary: embed the `.wasm` bytes, decode and validate them inside Lean, translate the validated module into Talos, and prove the behavior of that artifact.  The public ABI will carry binary64 inputs and outputs as `i64` bit patterns, with `f64.reinterpret_i64` and `i64.reinterpret_f64` inside the artifact.  Host-language numeric conversion will play no part in input transport, output transport, or the artifact theorem.

The proof has three layers.  The artifact-execution theorem states that the decoded WASM implements a specified binary64 algorithm under WebAssembly semantics, while a safety theorem states that every successful execution satisfies its domain conditions and produces finite values.  A numerical-refinement theorem interprets those finite binary64 values mathematically and proves an enclosure, approximation, or error bound for the corresponding real-valued computation.

The semantic reference is the WebAssembly 3.0 [numeric semantics](https://webassembly.github.io/spec/core/exec/numerics.html), together with its [instruction execution](https://webassembly.github.io/spec/core/exec/instructions.html), [validation](https://webassembly.github.io/spec/core/valid/instructions.html), and [binary encoding](https://webassembly.github.io/spec/core/binary/instructions.html).  The initial profile covers `f64` values, constants, the listed scalar operations, integer conversions, and reinterpretation.  Separate profiles will cover `f32`, SIMD, transcendental functions, and floating-point memory instructions, while the first artifact uses integer loads, stores, parameters, and results around internal reinterpretations.

## Existing system and missing proof boundary

Talos represents an `f64` value by its exact `UInt64` bits and defines arithmetic, square root, comparisons, conversions, and reinterpretation in `Interpreter/Wasm/Float.lean`.  Arithmetic and comparisons currently decode those bits through Lean's opaque native `Float`, execute a host operation, and encode the result, while a common function selects a canonical NaN.  These definitions execute programs but do not expose kernel-checked proofs of round-to-nearest-even, subnormal behavior, overflow, signed zero, or WebAssembly's permitted NaN results.

The exact-artifact profile under `proofs/talos/lean/Project/Artifact/Binary` currently accepts integer value types and instructions.  Supporting `f64` crosses syntax, grammar, decoding, decoder soundness, validation, validity proofs, Talos translation, structural equality, fixtures, and aggregate artifact checks.  Each admitted floating-point opcode needs both a successful exact-byte path and a mutation case that fails at the expected decoder, validator, translation, semantic, or refinement boundary.

LeanExe currently rejects floating-point source types.  A narrow compiler profile can expose binary64 intrinsics over `UInt64` bit patterns, emit internal `f64` instructions and reinterpretations, and retain the current `Array UInt64 -> Array UInt64` generation interface.  General Lean `Float` source support requires a separate source-semantics decision and does not block the narrow artifact profile.

## Scalar semantic model

The logical value remains a `UInt64` bit pattern.  A proof-visible decoder will expose the sign bit, eleven-bit exponent, fifty-two-bit fraction, and classification as zero, subnormal, normal, infinity, or NaN.  Finite values will receive an exact integer or rational interpretation derived from the decoded exponent and significand.

One integer-based round-to-nearest-even function will serve every operation that rounds a real result to binary64.  Its theorems must cover normal and subnormal results, exact halfway cases, underflow to signed zero, overflow to infinity, and a significand carry into a new exponent.  Addition, subtraction, multiplication, division, and integer-to-float conversion will reduce their rounding arguments to this common result.

WebAssembly arithmetic will use an allowed-result relation over input and output bit patterns.  The relation will express the permitted NaN outcomes and the unique non-NaN result, including signed zero, while a proof-visible canonical selector will provide executable Talos behavior and carry a theorem that it satisfies the relation.  Native `Float` execution may remain as a development oracle, but no accepted artifact, safety, or refinement theorem will depend on it.

| Operation family | Required semantic result |
|------------------|--------------------------|
| Classification and reinterpretation | Exact bit decomposition, reconstruction, classification disjointness, and bit-identical `i64`/`f64` reinterpretation. |
| `abs` | Direct sign-bit clearing with payload, infinity, subnormal, and signed-zero facts. |
| Comparisons | Ordered WebAssembly results for finite values, infinities, signed zero, and unordered NaN inputs. |
| `min` and `max` | Exact signed-zero choice and the permitted result set for NaN inputs. |
| `add`, `sub`, `mul`, and `div` | Exceptional-case classification, exact finite operation, shared round-to-nearest-even, overflow, underflow, and allowed NaNs. |
| `sqrt` | Exceptional cases plus an integer-root or equivalent exact bound that determines the correctly rounded binary64 result. |
| Integer conversions | Signed and unsigned `i32`/`i64` to `f64`, trapping `f64` truncation, and saturating truncation, with exact range and rounding rules. |

The first executable semantics can choose one permitted NaN result deterministically and prove that choice sound.  A complete WebAssembly relation must account for a permitted result at each dynamic floating-point event, without tying the choice to the fuel used by Talos execution or weakest-precondition proofs.  Numerical kernels will avoid that complexity in their final result theorem by proving that every successful path excludes NaN and infinity before an affected operation can produce a non-unique result.

## Numerical obligations and failure

Verified kernels will return an explicit tagged result such as `ok bits` or `domainError`.  Under the current array interface, a fixed two-word output can carry the tag and payload, while a later direct scalar interface can use the same logical result type.  The design review will assign the concrete tag values and the payload rule for an error result before compiler work begins.

The proof generator may produce certificates for intermediate ranges, finiteness, nonzero divisors, valid square-root arguments, accumulated rounding error, and branch stability.  Rational intervals with outward rounding provide a small certificate language in which each step names input intervals, an operation, and an enclosing output interval.  Lean will check every certificate step against a soundness theorem, leaving an external interval or numerical tool outside the trusted base.

A comparison whose proved intervals overlap its decision boundary lacks a branch-stability certificate.  The initial kernel will return `domainError` for that input region, and its central theorem will state that each `ok` execution returns finite bits within the required mathematical bound.  A certified higher-precision fallback adds another arithmetic semantics, compiler path, and refinement proof, so it remains a later project after rejection semantics work end to end.

## Implementation sequence

The work is divided into narrow checked increments.  Each milestone leaves the integer artifact profile unchanged and adds one independently reviewable semantic or artifact layer.  A milestone completes only after its Lean proofs, exact-artifact checks, conformance cases, and relevant mutations pass.

| Milestone | Work | Completion evidence |
|-----------|------|---------------------|
| 0. Design record | Fix the first arithmetic operation, tagged-result ABI, allowed-NaN relation, certificate endpoint representation, initial conversion set, and Talos execution API. | Reviewed definitions and theorem statements, with no implementation dependency added. |
| 1. Binary64 foundation | Add bit decomposition, classification, exact finite interpretation, reconstruction, and direct `abs` and reinterpretation semantics. | Exhaustive classification partitions, round-trip theorems, boundary examples, and checked sign-bit operations. |
| 2. Exact-artifact closure | Add `f64` types, constants, selected scalar opcodes, conversions, and reinterpretations to the binary syntax, grammar, decoder, soundness proof, validator, validity proof, translation, and equality layers. | One exact artifact decodes, validates, translates, and rejects opcode, immediate, type, and translation mutations. |
| 3. Deterministic scalar base | Add comparisons, `min`, `max`, exceptional-case classification, the allowed-result relation, and a canonical selector proved allowed. | WebAssembly conformance cases cover NaNs, infinities, subnormals, and both zeros.  WP rules expose the proved semantics. |
| 4. Shared rounding and one arithmetic operation | Prove the common round-to-nearest-even kernel and use it for either addition or multiplication. | Normal, subnormal, halfway, underflow, overflow, and carry-boundary theorems.  Selector membership in the allowed-result relation. |
| 5. Vertical artifact kernel | Compile one guarded kernel through the `i64` bit ABI, generate one narrow interval certificate, and prove execution, safety, and numerical refinement. | Exact bytes, direct artifact theorem, finite `ok` result, explicit `domainError`, checked enclosure, independent package verification, and mutation failures. |
| 6. Complete scalar profile | Add the remaining arithmetic operations, division side conditions, correctly rounded square root, and the complete integer-conversion set. | Per-operation semantic theorems, WP rules, conformance corpus, and a whole-program result independent of permitted NaN selection on finite-success paths. |
| 7. Reusable numerical certificates | Generalize the vertical certificate into a checked format for ranges, finiteness, domains, accumulated error, and branch stability. | Certificate parser and checker, soundness theorem per step, generator documentation, accepted certificates, and rejected corrupt certificates. |
| 8. Narrow LeanExe compiler profile | Add explicit bit-pattern intrinsics, internal `f64` emission, domain guards, annotations, and certificate output. | Source rejection outside the profile, source/execution comparisons, byte-stable artifacts, annotation checks, and end-to-end `leanexegen` proof generation. |

The first vertical slice ends at milestone 5 and supplies the earliest evidence about feasibility, proof-checking cost, and the usefulness of generated certificates.  Work on the complete operator set follows only after that artifact passes independent verification and its numerical-refinement proof remains tractable.  Square root begins after the shared rounding theorem because it forms the longest serial proof dependency.

## Effort and risks

The estimates assume Lean 4.31.0, one experienced Lean developer, and no new floating-point dependency.  Decoder, validator, and conformance work can proceed alongside the semantic foundation, while the common rounding theorem and square-root proof remain sequential.  Any move to another Lean version or a third-party arithmetic library requires a separate toolchain or dependency review.

| Result | Estimated effort |
|--------|------------------|
| Vertical artifact slice through milestone 5 | 4–8 engineer-weeks. |
| Complete scalar Talos and exact-artifact path through milestone 6 | 6–10 engineer-months in total. |
| Reusable checked certificate system in milestone 7 | 2–4 additional engineer-months. |
| Narrow LeanExe compiler profile in milestone 8 | 1–3 additional engineer-months after the semantic API stabilizes. |

| Risk | Assessment | Control |
|------|------------|---------|
| Correctly rounded square root | High: exact root bounds, tie handling, subnormals, and classification boundaries interact. | Start after common rounding.  Divide the proof into exact bounds, rounding decision, and encoding.  Check every exponent boundary. |
| Shared rounding theorem | High: every arithmetic operation depends on it. | Use one small integer kernel and separate normal, subnormal, halfway, underflow, overflow, and carry proofs. |
| Permitted NaN behavior | High: WebAssembly permits several results for some operations, while Talos currently chooses one. | Separate the relation from the selector, prove selector membership once, and prove finite-success paths choice-independent. |
| Lean checking cost | Medium-high: exact integer and rational normalization may dominate artifact proofs. | Keep checked arithmetic theorems opaque, use small certificate steps, and measure each milestone before broadening the operator set. |
| Numerical-certificate soundness | Medium: every kernel refinement depends on the checker. | Keep the certificate language small, use rational endpoints, and prove one soundness theorem for each certificate operation. |
| Artifact decoder and validator extension | Medium: the change crosses many checked modules. | Add instruction families in stages and preserve decoder, validator, translation, conformance, and mutation gates at each stage. |
| Public bit-pattern ABI | Low-medium: transport is exact, while the tagged result needs a stable encoding. | Fix the encoding in milestone 0 and keep reinterpretation inside the proved artifact. |

## Trust boundary and acceptance

The Lean kernel will check the binary64 definitions, WebAssembly allowed-result relation, Talos execution rules, artifact theorem, safety theorem, interval-certificate soundness, and numerical-refinement theorem.  The compiler, headless proving agent, certificate generator, Wasmtime, native `Float` evaluator, and source program remain untrusted producers or comparison tools.  Exact bytes, generated certificates, and suggested proofs enter the trusted result only through their Lean checks.

The first acceptance artifact will take binary64 inputs as `i64` bit patterns, reinterpret them internally, execute one proved arithmetic operation behind explicit domain guards, and return a tagged integer result after `i64.reinterpret_f64`.  Lean must prove the exact artifact execution, finite successful result, domain rejection, and one numerical enclosure, while the independent package verifier must reconstruct that theorem from the frozen bytes.  Mutating the opcode, rounding result, domain guard, output tag, or certificate must make the corresponding artifact, semantic, safety, or refinement check fail.

Full scalar completion requires checked semantics and artifact coverage for every operation family in the table, including subnormals, infinities, signed zero, and permitted NaN results.  At least one multi-operation kernel must prove a cumulative error bound and stable control flow, and at least one boundary case must return `domainError`.  Performance measurements must report kernel checking time, artifact-proof checking time, certificate checking time, and the largest proof reduction boundary before compiler support expands.

## Decisions before implementation

Milestone 0 must select addition or multiplication for the vertical slice, define the tagged output encoding, and fix the initial certificate endpoints.  It must also define how the deterministic Talos selector relates to the full WebAssembly allowed-result relation and which integer conversions enter the first artifact.  These decisions determine the public theorem statements and require review before code changes.

The plan keeps Lean 4.31.0 and adds no dependency by default.  A later Lean release may offer useful logical floating-point components, but a toolchain comparison must account for WebAssembly's NaN relation, exact artifact integration, and certificate checking rather than arithmetic definitions alone.  A third-party floating-point library or higher-precision runtime requires a separate review of maintenance, licensing, proof assumptions, and the trusted boundary.
