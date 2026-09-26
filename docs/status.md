# Development Status

This report combines the scalar compiler correctness work on `correct` with
I/O and quantized GPT from `iogpt`. Integration is being checked on `ciogpt`.
The parent branches' verification records describe their respective revisions;
fresh combined checks are recorded in [task.md](../task.md). The root
[Development Plan](../plan.md) records remaining work, and repository registries
define the source and exact-artifact proof inventories.

## Current capabilities

| Boundary | Current evidence |
|----------|------------------|
| Source compilation | LeanExe loads checked Lean declarations, accepts the subset in the [language specification](spec.md), and emits standalone WASM, bounded WASI adapters, or primitive timed byte I/O through `compile-wasi-io`. |
| Byte I/O | `ByteIO.read` and `ByteIO.write` run through the nonblocking WASI host.  The complete execution suite passes, including ownership, release, streaming, and EOF tests.  The separate [byte-I/O gate](../proofs/byte-io/README.md) checks host-model specifications, byte-transfer protocol laws, and six exact-binary execution cases.  C host, Wasmtime, and OS behavior remain external assumptions checked by execution tests. |
| Self-hosted binary emission | The experimental image path can freeze lowered modules and invoke the pure emitter compiled into WebAssembly.  Its retained Wasmtime Stage 1 and Stage 2 receipt reproduces the complete emitter artifact and all twenty compiler artifacts registered when that receipt was recorded, byte for byte.  Production compilation uses the direct native serializer, and self-hosting is not an aggregate gate. |
| Execution | The execution suite compares accepted programs with ordinary Lean or the IR evaluator where those references apply, and runs generated modules with Wasmtime. |
| Pretrained GPT-2 | [GPT-2 124M](../data/gpt2-124m/README.md) generates text through LeanExe/WASM with FP32, packed external weights, and cached attention.  Tests compare 6,432,896 logits with PyTorch across contexts one through 128, check cache reset and cleanup, and reproduce a greedy PyTorch completion exactly.  Checked source-agreement proofs cover packed reads and construction, both allocation paths, row mean, inverse standard deviation, attention score, linear matrix projection, and complete layer normalization.  Internal row statistics, matrix projection, and normalization check against the complete cached module.  Normalization includes all three constructors, temporary-buffer release, output ownership, and preservation of protected tensors.  Cached key/value lookup, scores, row maximum and sum, exponential evaluation, scalar GELU, and complete tensor activation now have checked proofs.  Tensor activation and residual addition include allocation, output ownership, and protected-input preservation.  Complete cached attention now has an exact source-agreement theorem covering six tensor constructors, the weighted-value fold, temporary-buffer release, output ownership, and protected-region preservation for positions zero through 127.  Complete block and hidden-state theorems now include embedding, all twelve blocks, cache assembly, output ownership, protected-input preservation, and temporary-buffer cleanup.  Vocabulary projection now has a complete execution theorem for all 50,257 scores, including allocation, ownership, and input preservation.  The complete exported cached step now proves termination and exact source cache and logits under represented-input, heap, and allocation-capacity assumptions.  It includes all four input-rejection cases and temporary cleanup, with arbitrary runtime weight words.  The checked 128-position invocation theorem derives the input representation, heap validity, and allocation premises and composes reset, weight loading, token calls, and cache/logit releases.  The runtime target is Wasmtime with Cranelift's NaN canonicalization enabled.  The 19,083-byte binary now has kernel-checked decoding, grammar, validation, model-equality, and complete session theorems.  The final theorem uses only the three standard logical axioms.  Numerical error bounds remain deferred. |
| Quantized GPT-2 | The [scalar projection](../proofs/talos/lean/Project/Gpt2QuantizedLinearRows/README.md) has checked accumulation, execution, ownership, release, and exact-binary proofs.  Its refreshed binary contains 4,741 bytes.  The [grouped projection](../proofs/talos/lean/Project/Gpt2QuantizedGroupedRows/README.md) now has a complete exact-binary theorem and a refreshed 5,409-byte module.  All 38 focused quantization cases pass.  The grouped cached candidate matches 6,432,896 independent-reference logits and every cache through 128 prefixes, passes rejection and cleanup tests, and reproduces all nine grouped completion streams.  Greedy choices agree with FP32 on 120/128 retained prefixes and 85/101 completion-prompt prefixes.  The retained benchmark from the GPT branch gives a 3.59× median speedup and 34.7% lower WASM linear memory across three warm traces.  The merged binary reproduces every retained logit and cache value across 128 prefixes.  The 127,695,972-byte model reduces weight storage by 74.3%.  The [evaluation record](../data/gpt2-quantized-v1/README.md) retains identities, failures, comparisons, and measurements.  The complete cached session has checked execution, termination, allocation, and buffer-release proofs.  The refreshed cached binary contains 28,017 bytes.  Its exact-byte package passes the aggregate check.  Conditional numerical propagation and its outward-rounded session evaluator pass.  Forward bounds certify no token choices across 302 evaluated prefixes.  Separate certificates from measured logits establish 232 individual greedy choices.  The complete execution, WAT/binary comparison, and conformance suites pass.  The merged branch passes the aggregate source and artifact checks in the existing checkout. |
| Source-driven proofs | The registry includes completed specifications for the FP32 and quantized GPT-2 sessions, all eight CLOB exports, and the complete Riemann solvers.  The merged branch passes the aggregate source check, including regeneration, per-case proofs, and the combined library.  The incomplete tiny GPT-2/128 sequence case remains paused. |
| Exact-artifact proofs | The merged branch passes the aggregate artifact check on 2026-09-25, including the frozen packages, their behavioral specifications, and registered declaration audits.  Each package embeds exact bytes, decodes and validates them, proves translation equality with its Talos execution module, and connects that module to its behavioral theorems. |
| Artifact decoder | Checked decoder soundness connects successful complete-file decoding to an independent declarative grammar for the accepted Core 3.0 binary profile. |
| Artifact validator | Checked validator soundness connects accepted modules to the independent `CoreValid` judgment for the supported sections and instructions. |
| Proof generation | `leanexegen` generates a specification, source program, WASM artifact, annotations, and direct artifact proof for a fixed `Array UInt64 -> Array UInt64` interface.  Demo 12 independently verifies a bounded first-zero search whose found branch allocates and copies an array with one element removed. |
| Proof support | The compiler emits annotation schema 1, ProofKit supplies checked semantic lemmas and tactics, and the knowledge forest selects filtered entries from versioned LTG packages. |
| Stateful proving | `leanexegen` records accepted runs with distinct attempt identities and exact generated proof adapters.  A separate Codex task can compose selected package-local modules into one candidate, promotion checks its declarations and axioms, and a later run selects the resulting forest.  Live proving receives catalogs and checked sources without archived proof evidence; an accepted Demo 10 run used a Demo 9 worked example through this boundary. |
| Compiler theorems | The [general source-to-exact-WASM theorem](arithmetic-correctness.md) covers admitted UInt64 arithmetic, complement and min/max, lets, nested and mixed propositional/Boolean conjunction, disjunction and negation over comparison and literal guards, pure Id operations, local functions, and one bounded strided range loop with continue and break. It proves exact bytes, full module validation and terminating exported invocation. Loop steps include monadic/result bindings, scalar and step-result helpers of arbitrary finite UInt64 arity; helpers can surround a loop, and ordinary lets can bind its result. Dependent conditionals retain proof-binder scope through scalar and loop code. Ordinary Boolean locals, aliases and ordinary/dependent Boolean conditions preserve distinct binding types, proof-binder scope and captured values. Standard numeral instances also admit constant let/lambda/application/metadata wrappers, and standard Nat numerals retain metadata in UInt64 conversions and instance arguments. Standard Id Boolean binds preserve typed flags through scalar and loop code, including nested Id action annotations. Boolean-valued choices over Boolean and closed propositional guards, including Eq/Ne with saved flags and dependent branches with unused proof binders, compose through bindings, captures, loop steps and nested conditions. Exact proof-domain checks and proved binder transformations preserve nested scopes. Bool- and UInt64-typed lets inside Boolean values preserve mixed nested bindings, shadowing and captures, including scalar operands using bound values. Unused bound values are checked, and recursive type conditions prevent direct Boolean reads of word slots. Standard Id layers on these binding annotations retain exact source types while derived scalar operands use the proved underlying-type representation. Unary Boolean-parameter scalar/step helpers cover conditional Boolean binds, captures and scalar helpers surrounding a loop. Explicit decide and implicit Prop-to-Bool conversions cover closed guards and Boolean equality/inequality with saved flags, including truth coercions and nested decisions. Bool.toUInt64 converts admitted Boolean values to words throughout scalar and loop code. Bool-valued equality and inequality compare admitted Boolean inputs using the exact standard instance. Propositional Bool equality and inequality also select scalar/step results through ordinary and dependent branches, with exact decision evidence and proof-binder types. The latest pre-integration checkpoint passed all nine compiler audits and 527 native Lean/V8 comparisons in a fixed thirty-declaration group, preserving the eighteen selected preceding modules byte for byte. The preceding full min/max checkpoint covers 259 declarations and 5,074 comparisons; the corpus now contains 660 declarations. Earlier scalar-certificate theorems continue to cover selected IR emitters used by annotation checks. Broader dialect coverage is being added incrementally. |

The checked conservative-state Euler side now has total exact generated-WAT
execution and safety theorems, plus 38 passing compiled regression vectors.
For arbitrary raw inputs, it preserves the complete store and returns the
seven pure-model words. Acceptance implies exact physical internal energy
at least density/2 and finiteness of all twelve rounded intermediates.
The focused package gate checks its exact 2,019 bytes through decoding,
validation, translation equality, both behavioral theorems and axiom audits.
See [the side checkpoint](../proofs/talos/lean/Project/EulerConservative/README.md).

The dynamic Rusanov interface now has total exact generated-WAT execution
and safety theorems for every six raw input words, preserving the complete
store. Accepted output has finite mass/momentum/energy fluxes, positive finite
signal speed and physically admissible input states. Its 76 compiled vectors
pass. The 3,167-byte frozen interface passes its focused exact-package gate.  See the
[dynamic interface checkpoint](../proofs/talos/lean/Project/EulerDynamicFlux/README.md).

The checked cell update now has total exact generated-WAT execution for
all ten raw inputs, complete store preservation, and seven exact result words.
Its safety specification attaches finite/admissible updated state, positive
finite pressure and signal speed, and a decoded rounded Courant number in
(0, 1/2]. All 43 compiled vectors pass. The 4,592-byte cell binary passes its focused
frozen-package gate. See
[the cell checkpoint](../proofs/talos/lean/Project/EulerCellStep/README.md).

The checked maximum-speed scan now has exact generated-WAT execution for
every logical input array fitting memory. Empty and malformed arrays reject;
both generated loops terminate, return the exact model status/speed and
preserve the complete store. Acceptance gives a positive finite selected
speed bounding every checked cell's computed speed. Both public declarations
pass standard-axiom audits. Its 3,292-byte frozen package passes the focused exact-byte gate. See
[the scan proof](../proofs/talos/lean/Project/EulerGridScan/README.md).

The complete grid-step export now has exact terminating execution and
accepted-payload safety proofs, including malformed entries, numerical
rejection, allocation, all cell updates and final release. Its public contract
requires a represented input and a disjoint bounded arena with an empty free
list. Its 8,866-byte frozen package passes independent decoding, validation,
translation and all three behavior checks, including reset. The generic
repeated-step proof and [maintained Sod data](../data/euler-sod-v2/README.md)
are complete: 100 cells reach t=0.2 in93 accepted steps, and100–800-cell
refinement errors decrease. The requested true2D visualization is [published](../data/euler-2d-v1/README.md). See [the grid proof](../proofs/talos/lean/Project/EulerGridStep/README.md).

The [Talos proof inventory](../proofs/talos/README.md) names each source-driven and artifact theorem.  [Artifact Proving](artifact-proving.md) explains how the exact binary remains the subject of the final theorem when annotations and compiler-derived evidence help construct the proof.  The proof packages can be checked without invoking LeanExe or Codex and without a compiler-correctness premise.  Source-agreement specifications import their Lean source definitions.

The additional `euler_certificate_flux` case proves exact generated-WASM
execution and outward enclosure of real pressure and Rusanov interface
fluxes, conditional on each component's status.  Its focused source-artifact
gate passes.  The [conservation-certificate plan](../plans/euler-certificates-and-convergence.md)
continues with grid totals, boundary accumulation, the accepted-step
observer, and complete exact-byte verification before the 192 and 800 runs.

## Release state

The saved release record is historical.  Release-record maintenance and separate-checkout reproduction are outside the requested merge work.  The merge checks run in the existing checkout with the pinned toolchains.

## Known limits

| Area | Current limit |
|------|---------------|
| Source language | Programs use the monomorphic, first-order subset; `compile-wasi-io` also accepts the two `ByteIO` operations.  Public ABI values exclude recursive inductives and function values. |
| Arithmetic | `UInt64` follows wrapping arithmetic.  `Nat` is bounded by the compiler's runtime representation where it crosses executable code. |
| Floating point | Five `UInt64` bit-pattern intrinsics lower to `f64.add`, `f64.sub`, `f64.mul`, `f64.div`, `f64.sqrt`, and the two i64/f64 reinterpretations.  Their source-driven cases, and Euler's exact frozen artifact, have proof-grade Talos execution and numerical theorems.  For `ε = 2^-52`, the fixed step decodes to left cell `[207/256, 9/80 - ε/20, 257/128]` and right cell `[81/256, 9/80 + 3ε/40, 95/128]`; their signed errors against the decoded-input exact-real quarter step are `[0, -3ε/64, -7ε/512]` and `[0, 5ε/64, -25ε/512]`, and the rounded physical two-cell balance residual is `[0, ε/32, -ε/16]`.  This is one closed Sod quarter-step certificate, not an input-generic Euler solver or time-integration theorem; its exact-byte package and [verified raw dataset](../data/euler-rusanov-step-v1/README.md) are complete.  The independent binary profile now includes all five arithmetic operations; its decoder/validator/translation tests and soundness proofs pass.  All three new primitive packages pass their focused exact-artifact and behavioral checks, and the prior aggregate artifact theorem check passed all twenty-five packages then registered. The new conservative-side package passes its focused full gate.  General Lean `Float` runtime values, classification intrinsics, and floating-point comparison instructions remain outside this source profile. |
| Strings | Lean `String` is not a supported runtime value.  `LeanExe.AsciiString` and `ByteArray` provide the supported textual representations. |
| Heap updates | Generated programs may mutate freshly allocated or uniquely owned heap objects internally.  Public array inputs are borrowed, so an operation returning a changed array allocates a distinct result rather than overwriting the caller's array. |
| Compiler correctness | The general compiler theorem proves source-to-exact-WASM correctness for the admitted scalar and bounded-range subset. Other dialect capabilities retain their documented per-program or modeled-host proof boundaries. The ciogpt integration checks that theorem against the combined compiler. |
| Talos conformance | The last accepted receipt has six known failures for imported-memory limit handling in `memory_grow.wast`.  The artifact profile forbids imports, and the historical conformance gate reports the exact rows as an upstream warning.  The 2026-09-04 current-input attempt matched all fifteen exact invalid-module classifications, then timed out while warming the pinned runner's broad Mathlib import closure; it emitted no conformance receipt. |
| Proof generation | Generation time remains variable and can exceed thirty-one minutes for structured loops.  Proof size, retrieval, revisions, checked abstraction use, and transfer across demos remain relevant measurements. |

## Immediate work

Demo 12 supplies the accepted structurally different artifact: its five loops implement early-exit search, allocation, prefix copy, and shifted-suffix copy.  ProofKit contains checked theorems for the compiler's one-word literal-key search, public erase-result reconstruction, and exact raw-cell prefix and shifted-suffix loops under symmetric source-target nonoverlap.  The compiler emits `leanexe.array.find-idx-eq.v1` and `leanexe.array.erase-copy.v1`, and the retained clean reproof covers the unchanged digest `7cdd8adba75d4f076d0a142f824a19a0d34d6a5cedd1a810a417a7fc5789f7b6`.

A separate `tools/leanexegen verify -s` invocation accepted the measured package before the follow-up ProofKit changes.  Stage 5 took 3,987.145392 seconds against the 3,907.231311-second baseline, an increase of 2.045 percent.  The proof decreased from 860 to 607 lines, 3,516 to 2,587 words, 39,249 to 28,874 bytes, and 47 to 38 journaled checks, reductions of 29.419, 26.422, 26.434, and 19.149 percent.  A current-ProofKit re-freeze later preserved the artifact digest and passed independent verification without running fresh proof generation or evaluating current LTG retrieval.

The reproof used seven LTG entries and rejected none.  `FixedArrayFindIdxEq.program_spec` and `FixedArrayCopy.eraseIdxProgram_spec` removed every local search, prefix-copy, and shifted-suffix loop invariant.  ProofKit now also contains the dynamic local length-store theorem and the encoded-index comparison fact identified by the journal.  Erase setup and branch-aware result transfer remain under review.

Phase 3 selected the compiler's zero-or-index-plus-one decoder because the same six-top-level-instruction region appears after the Demo 12 search, in ClobCancel, and twice in ClobDepth.  The compiler descriptor and certificate prove emitter agreement after successful IR recognition, while a separate annotation scanner records matching source, scratch-start, destination, and encoding roles.  The artifact consumer checks the complete nested instruction shape and generates a Lean equality to the neutral `EncodedIndexDecoder.program`.

The Demo 12 annotation pass preserved its 2,183-byte artifact and digest, generated the exact decoder equality, and passed separate package verification.  The pass reused the accepted behavior proof, so it measured neither LTG retrieval nor fresh proof generation.  The provisional LTG entry therefore records a checked capability rather than an accepted Demo 12 proof use.

The annotation consumer now emits a resolved-tail theorem for every version-two direct semantic recipe with an exact Lean program equality.  `proof-recipes.json` names that theorem in `direct.tailEquality`, while archived version-one recipes remain valid.  A current Demo 12 annotation pass generated tail theorems for the nested find-index, encoded-index, and erase-copy regions, preserved the artifact digest, and passed independent package verification.

ProofKit now exposes `EncodedIndexDecoder.resultFrame_get_ne`, `EncodedIndexDecoder.resultFrame_validIndex`, `FixedArrayAllocatorWindow.allocFrame_shape`, and `FixedArrayAllocatorWindow.allocFrame_validIndex`.  A fixed-artifact Demo 12 reproof retrieved and used the broader decoder getter, while the accepted source did not use either new allocator declaration.  Independent package verification accepted the resulting theorem over the unchanged artifact digest.

Stage 5 took 5,903.365887 seconds, and the accepted proof contains 1,059 lines and 50,046 bytes.  The result is slower and larger than the 3,371.682385-second, 735-line guided decoder-tail run, so it establishes capability and retrieval rather than a performance improvement.  Its journal records repeated work on opaque resolved suffixes, the encoded-option control path, dynamic erase setup, allocator getter reconstruction, and deeply nested continuation frames.

The ClobDepth compiler run preserved the registered 3,602-byte artifact and identified two matching decoder regions with different scratch and destination locals.  Its source proof now applies `EncodedIndexDecoder.program_spec` twice, removing four decoder-specific `wp_iff_cons` applications and four associated `wp_run` calls, while explicit region decomposition and premises produce a net increase of 21 source lines.  The complete `clob_depth` Talos proof gate passed, but this cross-program refactor has no comparable proof-generation-time measurement.

The2D conservative-state function now passes exact generated-WAT execution,
physical/rounded safety,44 Wasmtime vectors and independent verification of
its2,212 frozen bytes. Directional interfaces and updates are also complete. The maintained
Sod v2 runtime uses the pinned Wasmtime44 C API and passes the execution-policy
guard, now covering .js/.mjs/.cjs. All retained v1 raw results and diagnostics
are reproduced exactly; v1 remains preserved as a historical publication.

The2D directional flux now has complete all-input exact-WASM execution and
accepted-state/field safety. Its3,514-byte package passes independent
verification;71 Wasmtime vectors and the focused old1D Spec regression pass.
The completed sweep runner and2D visualization are described below.

The2D directional cell now proves all13-input execution, eight raw results,
store preservation, updated-state safety and rounded CFL in (0,1/2]. Its
5,190-byte package passes independent verification. All79 original Wasmtime
vectors and one targeted post-update rejection pass; the old1D cell Spec
regression also passes. The sweep/run bridge and final2D data are complete.

The2D x/y sweep and finite accepted-run trace now pass, including physical
state preservation under momentum exchange and the four-quadrant initial
state certificate. Every pointwise numerical call is linked to actual WASM;
the runner contract transfers to the existing exact cell bytes. Native C/JS
grid/time orchestration is outside the formal proof. Both 192² native runs
(pulse 130 steps, quadrants 165) and all saved raw/controller records match
an independent oracle. Fresh Wasmtime runs reproduce all eight canonical
files. [Data, 21-frame animations and inspected SVG/PNG posters](../data/euler-2d-v1/README.md)
complete the earlier Euler visualization agenda.  Current inventories
contain 46 source cases, 46 complete,
46 caches, 25 completed floating-point
cases, including both complete Riemann solvers, and 43 exact-byte packages.

The revised outward-speed interface has complete generated-WASM proofs
of exact output, termination, store preservation, rejection-or-safe
behavior, and physical-flux residual bounds.  The eight-input scalar
entry returns four flux components, the certified speed, and status.
Its 7,175-byte package now passes complete decoding, validation,
translation, behavior transfer, and independent verification.  All public
and manifest audits use standard axioms.  The complete revised solver now
has exact-byte proofs.

The revised scalar face-step source composes two certified interface fluxes
and four conservative updates.  Its checked theorems establish output-state
admissibility, physical speed bounds for all supplied faces, exact-real
Courant bounds, and physical-reference error bounds.  The mesh-CFL bridge
connects acceptance to exact unit-domain dt*n.  Its generated-WASM proofs
now establish termination, exact output, store preservation, and all three
public specifications.  The entry has 21 raw inputs and eight result words.
Its 9,077-byte package now passes decoding, validation, translation equality,
all three behavioral transfers, and independent verification.  All eight
manifest audits use standard axioms.  The complete solver now has
exact-byte proofs.

The revised face-row source proofs establish shared-flux cancellation and
computed and physical Rusanov reference balances.  The reference residual
bound contains the two boundary-flux errors and summed update errors.
All seven audits use standard axioms.  The reconstructed traversal now
instantiates these balances through its accepted timestep trace.

The complete revised source now uses five-cell reconstruction, outward grid
speed bounds, checked mesh ratios, and timestep retry.  Its source proofs
cover accepted-state safety, grid size and index preservation, terminal
status, and the exact accepted numerical trace.  The generated module has
30,726 bytes and two runtime inputs: grid size and reconstruction trials.
Its five-cell update and internal grid scan have checked terminating
execution with exact output and store preservation.  Both directional
sweeps and their composition now have terminating execution, exact array
output, ownership, page-limit, and memory-reservation proofs.  The complete
retry function now proves termination and exact source behavior for
acceptance, CFL rejection, trial rejection, invalid time advancement, and
fuel exhaustion.  It preserves source ownership, a supplied page limit,
and the heap reservation.  Complete time advancement, initialization, and
output now compose into a terminating generated-WASM solver theorem with
exact source output and a 512 MiB memory bound.  It covers grid sizes from
two through 800 and every runtime reconstruction-trial word.  The revised
traversal now has checked conservation for all four components throughout
its accepted trace.  The area-weighted real-reference balance bounds
update, boundary-flux, spacing, and outward-ratio errors.  All four
generated-WASM specifications now compose execution and the numerical
theorems, including every accepted trace prefix.  Source regeneration
passes with unchanged bytes and standard axiom audits.  The complete
30,726-byte package now passes decoding, validation, translation, all
four behavioral theorems, and independent verification.  The revised
[192-grid and 800-grid data and figures](../data/euler-reconstructed-v1/README.md)
are complete.  Both returned status zero at time 0.8 using eight
reconstruction attempts.  Runtimes were 176.7 seconds and 3 hours
58 minutes.  The short article includes both figures, data, comparison,
and the claim-to-theorem table.

The [complete Riemann solver](../plans/euler-riemann-complete.md) now has
kernel-checked exact-byte proofs of complete execution, termination,
output, a 512 MiB memory bound, final-state safety, and the numerical
trace through time 0.8 when its status is zero.  Complete decoding,
validation, and Talos translation equality pass.  The independent
package checker accepted the frozen 21,767-byte artifact and its
manifest theorems.  All final Euler audits contain only the three
accepted logical axioms.

The [192-grid and 800-grid data and density/pressure figures](../data/euler-riemann-complete-v1/README.md)
are complete.  Both runs returned status zero at time 0.8, using the same
binary and one local WASM solve call per grid under the standard runner
limits.  Recorded monotonic runtimes are 49.6 seconds and 61.6 minutes.

The [2D hyperbolicity extension](../plans/euler-hyperbolicity.md) passed its
focused independent artifact check on 2026-09-14.  It proves the physical
flux derivative and a complete real eigenbasis in every unit direction
for positive-density, positive-pressure states with gamma 7/5.  The
registered exact-binary specification applies the theorem to accepted
states, intermediate sweep grids, and terminal arrays.  All eight manifest
audits contain only the accepted logical axioms.  The outward speed and
interface maximum helpers have exact-byte characteristic-speed bounds.
The mesh CFL helper's exact-byte theorem bounds dt*n by the returned
ratio and ratio*alpha by one half.  The revised solver includes these
helpers and their accepted-trace proofs.

The [net conservation-error observer](../plans/euler-certificates-and-convergence.md)
has complete source proofs for totals, reconstructed boundary fluxes,
accepted-step accumulation, numerical projection equality, and residual
enclosure.  Its source output appends four status/lower/upper triples to
the existing solver words.  The complete observer's generated execution,
allocation, exact output, and 512 MiB memory bound now have checked proofs.
The scalar interval-flux module also has checked generated execution.
New production runs await exact-byte proofs and independent package checking.

The observer's generated grid-total and boundary-contribution functions now
have exact execution and store-preservation proofs.  The existing sweep,
initialization, output, release, and scan proofs transfer through checked
function-region equality.  The trial and retry functions now have complete
execution proofs for success, rejection, invalid time, and fuel exhaustion.
They prove exact interval results and preserve heap reservations and owned
grids.  The complete time-step loop and enclosing run also pass, including
initialization, final totals, and the exact residual intervals.  Final packing
and the exported entry pass, with standard logical axioms.  The focused
source-artifact gate passes.  The exact-byte package remains open.

Standard Boolean Id.run/pure and metadata now compose inside Boolean expressions, including annotated bindings, choices, captures and loop conditions. The nested Boolean Id evidence records all nine audits and the focused native/V8 execution checks.

Standard nested Id annotations on ordinary word, Boolean and helper lets now compose through scalar, step and range code. Matching nested Id numeral instances are checked at every layer. The ordinary Id-let evidence records all nine audits and focused native/V8 execution checks.
