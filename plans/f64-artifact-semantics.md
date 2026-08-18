# Proof-Grade `f64` Artifact Semantics

**Status:** Deferred.  The current artifact profile covers integer programs, while Talos executes floating-point instructions through opaque native `Float` operations.  This plan records the required proof boundary, likely cost, and staged implementation so later work starts from an explicit design rather than the current interpreter behavior.

## Goal and theorem boundary

LeanExe should embed exact `.wasm` bytes, decode and validate them inside Lean, translate the validated module into Talos, and prove the behavior of that artifact.  The public ABI should carry binary64 values as `i64` bit patterns and use `f64.reinterpret_i64` and `i64.reinterpret_f64` inside the artifact.  This keeps every input and output bit exact across the host boundary, including signed zero and NaN payloads.

The proof has three layers.  The artifact theorem proves that the decoded WASM implements a specified binary64 algorithm under WebAssembly semantics.  A safety theorem proves that every successful execution stays in the finite domain, satisfies the divisor and square-root side conditions, and returns a finite result.  A numerical-refinement theorem interprets finite binary64 values mathematically and proves an approximation, enclosure, or error bound for the corresponding real-valued computation.

Numerical refinement requires a separate theorem.  A correct binary64 implementation of Euler's method can still have an unacceptable accumulated error or an unstable branch.  Each numerical kernel therefore needs explicit range, error, and branch-stability obligations in addition to its exact execution proof.

## Current implementation

Talos already represents an `f64` value by its exact `UInt64` bits and implements arithmetic, square root, comparisons, conversions, reinterpretation, and the other scalar instructions in `Interpreter/Wasm/Float.lean`.  Arithmetic and comparisons decode those bits through Lean's opaque native `Float`, execute a host operation, and encode the result; a common function selects the canonical NaN for numeric results.  This supplies executable behavior, but it does not expose a kernel-checked proof of round-to-nearest-even, subnormal behavior, overflow, signed zero, or the WebAssembly relation of permitted NaN results.

The exact-artifact binary profile under `proofs/talos/lean/Project/Artifact/Binary` currently accepts integer value types and instructions.  Adding `f64` requires changes to syntax, grammar, decoding, decoder soundness, validation, validity proofs, Talos translation, equality, fixtures, and aggregate artifact checks.  Talos's general validator currently stops its straight-line type check when it encounters an unmodelled floating-point instruction, so the new artifact profile must add checked typing rather than inherit that behavior.

LeanExe currently rejects floating-point source types.  A narrow compiler profile can expose explicit binary64 intrinsics over `UInt64` bit patterns, emit internal `f64` instructions and reinterpretations, and preserve the integer public ABI.  General Lean `Float` source support has a broader source-semantics and compilation boundary and belongs in a separate decision.

## Scalar semantic model

Keep `UInt64` as the value representation and add a proof-visible binary64 decoder.  The decoder should expose the sign, exponent, significand, and classification as zero, subnormal, normal, infinity, or NaN.  Finite values should have an exact integer or rational interpretation based on the decoded exponent and significand.

Use one shared round-to-nearest-even operation for every arithmetic result.  Its theorem must cover normal and subnormal outputs, exact halfway cases, underflow to signed zero, overflow to infinity, and carry into a new exponent.  Addition, subtraction, multiplication, division, integer conversion, and finite-result lemmas should reduce their rounding obligations to this operation.

Define WebAssembly arithmetic through an allowed-result relation over input and output bit patterns.  This relation should state the permitted NaN outcomes while fixing all non-NaN results, including signed zero.  Talos may retain a deterministic canonical selector for execution after Lean proves that the selector always satisfies the allowed-result relation.  A kernel theorem that excludes NaN and infinity then reduces the relevant execution to the unique finite result and removes dependence on payload selection.

The first vertical slice can prove each scalar operation through the allowed-result relation and canonical selector.  A full-profile whole-program theorem must quantify over each permitted result at each dynamic floating-point event.  That later execution API should keep the choice cursor private to the interpreter and independent of fuel so existing fuel and weakest-precondition arguments remain stable.

`abs` and reinterpretation are direct bit operations.  Comparisons, `min`, and `max` require exact treatment of NaN and signed zero, while integer conversions require their specified rounding, range, trap, and saturation behavior.  Correctly rounded square root forms the hardest isolated arithmetic proof and should follow the shared rounding and finite arithmetic infrastructure.

## Numerical obligations and failure

Verified kernels should return an explicit tagged result.  The initial ABI should encode `ok bits` and `domainError` as an integer tag plus one payload word; invalid domains, uncertified ranges, and unstable numerical decisions select `domainError`.  Every `ok` theorem should state that the result bits are finite and satisfy the kernel's mathematical error or enclosure bound.

The proof generator may produce certificates for intermediate ranges, finiteness, nonzero divisors, valid square-root arguments, accumulated rounding error, and branch stability.  Rational intervals with outward rounding provide a small certificate language: each step names input intervals, an operation, and an enclosing output interval.  Lean must check the certificate and use a soundness theorem for each step, so an external interval or numerical tool remains an untrusted producer.

A comparison whose proved intervals overlap its decision boundary has no branch-stability certificate.  The first implementation should return a rejection result for that input region.  A certified higher-precision fallback would add another arithmetic semantics, compiler path, and refinement proof and should begin as a separate later project.

## Staged work and estimates

The estimates assume Lean 4.31.0, one experienced Lean developer, and no new floating-point dependency.  They describe engineering effort rather than calendar time, because binary-decoder work and tests can run in parallel while the rounding and square-root proofs remain sequential.  A later Lean release may supply reusable logical float components, but it would still require an explicit toolchain decision and a WebAssembly-specific NaN relation.

| Stage | Result | Estimated effort |
|------|--------|------------------|
| Vertical artifact slice | Bit classification, `i64` bit ABI and reinterpretation, comparisons and `abs`, one proved add or multiply path, checked artifact decoding and validation, and one bounded tagged kernel theorem. | 4–8 engineer-weeks. |
| Complete scalar Talos path | Shared round-to-nearest-even, subnormals, overflow, signed zero, add, sub, mul, div, correctly rounded sqrt, selected conversions, permitted NaNs, weakest-precondition integration, exact artifact checking, and conformance. | 6–10 engineer-months in total. |
| Reusable numerical certificates | Checked range, finiteness, error, and branch-stability certificate language plus a generator-facing format. | 2–4 additional engineer-months. |
| Narrow LeanExe compiler profile | Explicit bit-pattern intrinsics, internal `f64` emission, domain guards, and annotation or certificate output after the semantic API stabilizes. | 1–3 additional engineer-months. |

## Main risks

| Risk | Assessment | Control |
|------|------------|---------|
| Correctly rounded square root | High: it combines exact root bounds, tie handling, subnormals, and boundary cases. | Implement it after the common rounding theorem and test every exponent and classification boundary through checked properties and WebAssembly conformance cases. |
| Shared rounding theorem | High: a defect affects every arithmetic operation. | Define one small integer-based rounding kernel and prove its normal, subnormal, tie, underflow, and overflow cases separately. |
| Permitted NaN behavior | High: WebAssembly permits several result patterns for some operations, while Talos execution chooses one result. | Separate the allowed-result relation from the executable selector and prove selector membership once. |
| Lean checking cost | Medium-high: exact integer and rational normalization may dominate artifact proofs. | Keep arithmetic semantic theorems opaque after checking, use small certificates, and divide proofs at operation and interval boundaries. |
| Numerical-certificate soundness | Medium: range and error claims become part of every kernel theorem. | Use a small checked certificate language with rational endpoints and one soundness theorem per certificate operation. |
| Artifact decoder and validator extension | Medium: the change crosses many checked modules. | Add types and instruction families in stages, preserving decoder, validator, translation, and mutation gates for each stage. |
| Public bit-pattern ABI | Low-medium: representation is exact, while tagged results and source intrinsics need a stable layout. | Specify the integer ABI before compiler work and use reinterpretation only inside the proved artifact. |

## Decisions before implementation

The first implementation review must select the vertical-slice operation, the exact tagged-result ABI, the allowed-result relation, and the certificate endpoint representation.  It must also select the initial conversion and memory-operation scope, the full or deterministic WebAssembly profile, and continued use of Lean 4.31.0 or a toolchain comparison.  A third-party floating-point library or higher-precision runtime requires a separate dependency and trust-boundary review.

The first acceptance gate is one exact binary artifact whose public inputs and outputs are `i64` bit patterns and whose internal body uses `f64.reinterpret_i64`, one proved arithmetic operation, explicit domain rejection, and `i64.reinterpret_f64`.  Lean must prove exact artifact execution, finite successful output, and one checked numerical enclosure.  Mutating the opcode, rounding result, domain guard, output tag, or certificate must make the corresponding artifact, semantic, safety, or refinement check fail.
