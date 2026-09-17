# WGSL development journal

## 2026-09-16 — Profile foundation and first generator

Started from the plan-only `wgsl` branch. Split work into generation, native
execution, and profile/proof integration, with all Lean verification serialized
by the root agent through `tools/leanrun`. The first kernel uses independent
output invocations rather than introducing shared memory or barriers before a
simple artifact can be checked.

The checkout had no Lean installation or dependency cache. Downloaded the pinned
Lean 4.34.0-rc2 Linux release into ignored `build/tools/lean`; checked the GitHub
release SHA-256 `3d011041203acacf300d343a39673f7d233743397993797c941346ae9e5df1a8`.
Sandbox access to the systemd user bus failed, but the approved runner outside
the sandbox established the required scope. Local mode was not used. The runner
reported exact Lean commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.

Lean checked the profile refinement, evaluation inclusion, nonempty evaluation,
and theorem-composition modules. The generator's first build reported a record
layout syntax error; expanding the record fields fixed it. Generation tests then
passed, including rectangular indexing, partial workgroups, zero/oversize
dimensions, invalid bindings, excessive workgroups, and dispatch overflow.

These are ordinary handwritten Lean proofs with no agent proof-generation or LTG
retrieval run yet. No accepted artifact theorem or independent artifact package
verification is claimed. The useful shared abstractions so far are operation
choices separate from fusion, and total execution obligations separate from
universal output predicates. The scalar interpretation remains an explicit hole
in the development, not a hidden assumption presented as a theorem.

Read the pinned WGSL floating-point rules before choosing the candidate runtime
profiles. The existing Talos dependency already has a pure integer `IEEE32`
model and binary32 error lemmas; this is a better reuse candidate than a new
parallel arithmetic implementation. Its source remains in the dependency.

## 2026-09-16 — Native execution and adversarial parsing review

The checked generator emitted the captured 3-by-5-by-2 kernel under
`test/wgsl/artifacts/rectangular`. A pinned wgpu-py 0.31.1 / wgpu-native 27.0.4.0
harness executed the exact source on Mesa 26.2.2 llvmpipe through native OpenGL.
All fifteen output words matched the restricted separate-operation profile.
The machine had no accessible physical GPU or software Vulkan ICD; the native
OpenGL software adapter supplied the initial execution path without system
package changes. Reports retain adapter details, library hash, exact source,
manifest, inputs, results, permitted outputs, and driver diagnostics.

Eight dependency-free tests passed for exact rational nearest-even arithmetic,
subnormals, signed zeros, fusion-sensitive examples, rectangular indexing,
manifest validation, serialization, failure evidence, and child timeout. Wrong
stores and malformed WGSL produced the expected native mismatch/error; their
reports are preserved alongside the successful execution.

Independent parser review caught a serious mismatch in line-comment handling.
The initial lexer stopped comments only at LF, while WGSL also treats CR and five
other characters as line terminators. A CR-hidden second output store parsed as
the original program in the first lexer but executed on llvmpipe and overwrote
the result with zero. The native failing report is preserved as
`test/wgsl/evidence/rejected-hidden-cr-store.json`. The lexer now uses all seven
specified line terminators, and tests inject the extra store after each one.
This failure demonstrates why native negative tests and independent parser
review are necessary before accepting any artifact theorem.

The first profile/generator milestone was committed and pushed as `9498db70`.
The binary32 model's existing pinned dependency was fetched and its import-free
`Interpreter.Wasm.IEEE32` module built successfully. No foreign source was copied
into the root library. Artifact execution and numerical theorems remain pending.

## 2026-09-16 — Local continuation: artifact parser

Resumed at a6b7b53f in the clean ARM Mac checkout. Existing local execution
and inherited-priority approvals apply; no remote executor is used. The
pinned Lean/lake binaries are present under build/tools/lean-4.34.0-rc2-darwin_aarch64,
with SHA-256 1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554
and c8c24f1398162ab4004e2a869952d8469f54293651151feaad4526f2b8474c6e.
The earlier journal describes an experimental lexer, but no parser/lexer
module was included in the fetched commit. That experiment is not treated
as an available checked implementation.

Read the pinned WGSL textual-structure rules before implementing the narrow
GEMM recognizer: all seven line terminators, eleven blankspaces, nested block
comments, token boundaries, null prohibition and canonical decimal literals.
Added Lexer.lean and Parse.lean. The latter consumes complete actual source,
parses constants/bindings/workgroup dimensions and checks an independently
written fixed-body token grammar. It does not compare against regenerated
source or trust manifest values. This is a restricted AST with one body form,
not a claim to parse arbitrary WGSL. Unknown syntax and trailing instructions
fail closed. Formal operational and numerical correctness remain open.

First build: Lexer314ms, Generate4.2s; Parse failed on a multiline record
layout and the reserved identifier syntax. Preserved the failed source in
task work/wgsl-Parse-first.lean; replaced the binder with ast and expanded
record fields. Added an exact captured-source literal plus adversarial
lexer/parser tests; its file identity is checked separately at runtime.
No proof from the failed build is counted as accepted.

Parse now builds in915ms; config_valid has no axioms. The test build
failed only because Except has no BEq instance in two lexical assertions.
Changed those assertions to decidable propositional equality and preserved
the failed test source. The remaining evaluated parser probes passed.
The local #guard command requires Bool rather than coercing decidable Prop;
replaced the two assertions with direct Except pattern matches. The second
failed draft is retained; this is a test-harness correction, not parser logic.

Focused parser corpus now builds in1.0s; the separate --run gate confirms
that the embedded golden literal equals the captured WGSL file exactly.
No timeout or resource-limit increase occurred. No new dependency, Python
execution, native runtime-conformance claim or GPU correctness claim was
introduced. Reviewed checkpoint paths: Lexer.lean, Parse.lean, ParseTest.lean,
docs/wgsl/README.md and this journal. All changes are scoped to WGSL.

Parser checkpoint3db4791f95801fd17609b43cff1439cfebdd1c6d was pushed
with parenta6b7b53f510a7402234fc642848876cf70892655 and tree
b3389637a5dade3f966ced14b641aa4fd9beaf45. Non-forced GitHub publication,
fetch, exact tree/index/worktree and local CAS checks passed; clean.

Added Index.lean with row-major bounds/injectivity, rounded-up dispatch
coverage, exact u32 access arithmetic, validated cell/loop bounds and a
decreasing loop measure. The first check found an unnormalized successor
product and a tactic unavailable in the dependency-free root library.
Preserved the draft and normalized the product before composition; replaced
the tactic with definitional numeral conversion. No assumption or limit
changed, and no audit from that failed build is treated as accepted.

Index passes in936ms. All seven public audits have no axioms or only
propext/Quot.sound. The concrete rectangular parsing theorem first lacked
a Decidable equality for Except; preserved that draft and switched to
definitional reduction (rfl), avoiding new global equality instances.

Direct rfl hit elaborator recursion on the full character stream. The
failed draft is retained. Split the closed parser reduction from the small
Except-to-Option transport lemma and use existing kernel-mode decide for
the former; no native-decide axiom or recursion/heartbeat increase is used.
Kernel-mode decide rejected the complete parser equality with an application
type mismatch after19s. This was not a timeout or an accepted theorem.
Isolating tokenization and the closed result in a separate retained diagnostic
before changing the proof boundary again.

The smaller diagnostic passes: native parser returns the expected complete
AST, lexical token count218, and kernel checks pass for the source length
and a complete declaration. Split the production interface into tokenization
and parseGemmTokens. The artifact now proves each boundary separately and
composes them; the candidate218-token literal is untrusted until its lexer
equality checks. Preserved the earlier combined source and parser boundary.

The scalar diagnostic isolates the blocker: reducing even the core
String.toNat? applied to "3" exhausts200,000 elaborator heartbeats; the
parser reaches the same boundary when reading its first dimension. Neither
limit was raised. Replaced slice-based decimal parsing with a total character-
list fold that directly enforces canonical ASCII digits and the u32 range.
The exact lexer equality already passes; token parsing will now be checked
independently. Simplified the small Except composition by explicit reduction.
All earlier drafts and diagnostic outputs remain preserved.

After structural decimal parsing, both kernel reduction boundaries pass.
The concrete composition change tactic still unfolded too much and hit
recursion. Added a small generic parseGemm_of_tokens composition lemma with
symbolic inputs and explicit Except.bind simplification; the artifact now
applies that lemma without recomputing its checked token stream.

The complete artifact composition now passes: Parse935ms, Index926ms,
RectangularArtifact19s, ParseTest1.0s. The exact parsing theorem audits to
propext/Classical.choice/Quot.sound; its resource validity has no axioms and
its instantiated access bounds use propext/Quot.sound. No sorry, admit,
new axiom or native-decide witness appears in these sources.
The separate --run gate passes exact binary file identity against the
proved source's UTF-8 bytes. Shader SHA-256 6fc06d865910ef3e615a1e33757e011feb56461958212160b04bf52c8d447455.
The full adversarial parser corpus still passes after the decimal-parser
change. No shader, native evidence, generator or numerical profile changed.

Review of the proof and failures supports two reusable choices: separate
lexer and token-parser equalities, then compose without reevaluating either;
and use a structurally recursive ASCII decimal parser instead of a general
string-slice conversion at the artifact-checking boundary. No LTG retrieval
or cross-kernel performance claim is made. The theorem now concerns actual
captured text, while operational and numerical obligations remain open.

Reviewed checkpoint paths: Parse.lean, ParseTest.lean, Index.lean,
RectangularArtifact.lean, WGSL.md, docs/wgsl/README.md and this journal.
Focused checks and git diff --check pass. Intended publication:
“Prove WGSL artifact parsing and GEMM index safety”.

2026-09-16: continuing the complete WGSL plan at the user's request. Previous
checkpoint f29678c6f5cf759721fd2e385b2c231d6a5a4414 was pushed with parent
3db4791f95801fd17609b43cff1439cfebdd1c6d and tree
d576673b61475d380c00586b7e3def5a8aa6d0d5; exact publication checks passed.

Added candidate accumulator and invocation semantics. Accumulate preserves the
parsed `acc + product` operand order explicitly, with local fusion as a separate
profile choice. Dot is independent of the control-flow machine. Invocation
steps include entry guards, checked loads, loop progress, final stores and
explicit dynamic-error states. The candidate invariant links reachable loop
states to Dot; a decreasing natural measure excludes infinite transitions.
Disjoint buffer objects are explicit in the model and remain a host-binding
precondition. No native runtime claim is inferred. First focused build follows.

The first invocation build exposed missing explicit binder types in Invariant;
the second exposed a core-vs-Mathlib induction name and elaboration order for
the initial-state invariant. Retained both failed drafts and logs, supplied the
explicit entry state and used core Nat.strongRecOn. No resource limits changed.
The third build passes in 976 ms. Invocation no-infinite-transition, safety,
existence and ExecutionTheorem audits use propext/Quot.sound only; restricted
accumulator and Dot exactness use no axioms. Failures are not accepted audits.

Added an artifact package connecting the exact captured source parse with this
invocation theorem. Its restricted exactness theorem remains conditional on a
concrete scalar interpretation; this is the next numerical integration boundary.
Full dispatch scheduling and native profile conformance remain separate.

Artifact invocation build passes in 879 ms after removing a redundant tactic
following a congruence step that had already solved the value equality. The
failed draft remains in task work/. Both artifact audits contain only standard
logical axioms. Reviewed Accumulate, Invocation, ArtifactExecution, WGSL.md,
README and journal. Focused build and diff whitespace checks pass; no sorry,
admit, new axiom or native-decide appears. No broad regression run is needed
for these additive proof modules. Publishing this completed invocation layer
before starting interleaved dispatch and concrete binary32 integration.

Invocation checkpoint 33cfa51a274dbef537f4312148b1ce862d06e46f published with
parent f29678c6f5cf759721fd2e385b2c231d6a5a4414 and tree
6f8dd9b07fee908d5ae8618825ce408b1ab72f6e; fetched identity and clean checks pass.

Dispatch now models arbitrary interleaving of invocation transitions. Its sum
of remaining work decreases on every transition; progress plus scalar totality
provides a completed schedule, while every reachable state preserves the Dot
invariant. Disjoint-coordinate final writes have different addresses; stores
at different addresses commute. After fixing an elaboration-order issue in the
head invariant, the focused Dispatch build passes in 881 ms with standard-only
audits. Its failed draft/log are retained. No scheduling fairness axiom is
added: runtime progress, as distinct from arbitrary external stalling, remains
part of the runtime-conformance boundary.

Launch enumerates all global coordinates of the rounded-up dispatch, including
padding. Candidate proofs cover uniqueness, active-cell coverage, u32 global
coordinate range, total completion, error exclusion and a Dot store per cell.
The initial check exposed implicit argument arity in Pairwise.imp and overly
aggressive placeholder application; replaced these with explicit arguments.

Launch and Output now pass. The second launch draft only needed explicit
projection reduction in decode_injective; no larger proof budget was used.
Output reconstructs completed stores and proves Dot at every active cell,
then instantiates ExecutionTheorem with actual success/error/infinite-trace
outcomes. Added reachable coordinate uniqueness and pairwise disjoint-write
proofs, so the conflict claim applies to the enumerated launch rather than
requiring distinct coordinates as an unchecked caller assertion.

The final artifact build passes: Launch 886 ms, Output 883 ms,
ArtifactExecution 887 ms. All public audits contain standard logical axioms
only. The exact captured shader now carries dispatch termination, safety,
output correspondence and conditional restricted exactness. Scalar totality,
concrete arithmetic interpretation, storage-object realization and runtime
conformance are still explicit boundaries. No new native evidence is claimed.
Reviewed Dispatch, Launch, Output, ArtifactExecution and status documentation;
diff whitespace and forbidden-proof-token checks pass. Publishing before
starting the concrete binary32 interpretation in the existing Talos workspace.

Dispatch checkpoint ca6775030492aa2beb504867c1ac942b79fb3cca published with
parent 33cfa51a274dbef537f4312148b1ce862d06e46f and tree
31c8621232057391cbb947d09c8127ee6c84c851; fetched exact identity and clean checks
pass. Binary32 integration now begins inside Project.WGSL in the existing Talos
workspace, preserving the compiler/dependency boundary. It reuses the pinned
pure integer add/mul and dyadic rounder. A new fused operation forms the exact
product-plus-accumulator numerator before rounding, with explicit exceptional
and signed-zero cases. Kernel-checked edge vectors exercise fusion sensitivity,
subnormals, ties, zero signs, overflow and NaNs. No dependency is added.

Concrete Binary32 and all eleven edge theorems pass (950/940 ms), including
negative-zero preservation and an exact fused result distinct from separate
rounding. The numerical draft initially mixed Nat/Int bound inference and
attempted concrete exponent simplification above the tactic's default threshold.
A second draft reached recursion while rewriting the full dyadic expression.
Both drafts/logs are retained. Isolated signed-magnitude transport over symbolic
integers, separated the two closed signed-zero facts, and use algebraic power
identities instead of increasing recursion, heartbeat or exponent thresholds.

2026-09-16: binary32 numerical composition now passes. FusedError transports the
shared dyadic-rounder bound through signed integers; AccumulationError proves
finite intermediates and the 2*K*2^-23 absolute bound for every permitted separate
or locally fused accumulation under DotDomain. ArtifactNumerical composes that
bound with the exact artifact's dispatch theorem and proves a sufficient product
budget of 1/(4K) for positive K up to 2^20. The first ArtifactNumerical run failed
only because `ring` followed a `field_simp` that had already closed its goal.
Retained that draft in task work/wgsl-artifact-numerical-first.lean and its failed
log; removed the redundant tactic. The second focused build passes in 4.6s.
Public audits contain only propext, Classical.choice and Quot.sound. Existing
FusedError warnings about unevaluated large powers and one unused simp argument
remain visible; no threshold was increased. Numerical input bounds are narrower
than the native harness's test envelope. No runtime conformance follows from
these arithmetic proofs.

The user's immediate priority is simple server-side execution of generated WGSL.
Installed the approved pinned Python runtime into build/wgsl/macos-venv-20260916;
macOS additionally resolves rubicon-objc 0.5.6. Generate.lean emits the existing
supported GEMM candidate to fresh artifact paths. The generated 3x5x2 shader in
build/wgsl/macos-rectangular-20260916 is byte-identical to the captured rectangular
source (SHA-256 6fc06d865910ef3e615a1e33757e011feb56461958212160b04bf52c8d447455).

The initial installed macOS runtime exposed no adapters. Metal attempts are
stopped at the user's instruction. The user rejected a browser route; an unused
HTML smoke page remains in task outputs, and browser URL policy rejected its
opening. It was not executed and is not runtime evidence. A Podman attempt,
after explicit access approval, failed because macOS reported virtualization
unavailable on this hardware (tmp/wgsl-podman-start-debug.log). Podman is not a
requirement for CPU WGSL execution; that detour did not advance the kernel test.

Found SwiftShader's native CPU Vulkan driver in the existing Chrome 152.0.7977.84
installation. A direct Vulkan API check successfully created an instance and
enumerated one CPU device, SwiftShader Device (LLVM 10.0.0), without launching
Chrome. The standard pinned macOS wgpu-native binary lacks Vulkan. With explicit
approval, installed checksum-pinned Rust 1.90.0 only under build/tools and built
the already pinned native runtime at commit
768f15f6ace8e4ec8e8720d5732b29e0b34250a8 using locked Cargo dependencies and one job.

The first source build used the outer vulkan-portability feature but still
exposed no adapter. Inspection showed that this pinned wgpu-native feature only
enables wgc/vulkan, while wgpu-core's Apple build requires wgc/vulkan-portability.
Enabled the core feature explicitly, without modifying upstream source. Also set
the upstream WGPU_NATIVE_VERSION build variable to 27.0.4.0 so runtime identity
is recorded correctly. Both earlier binaries, all failed reports and build logs
remain under build/wgsl and tmp. The corrected build finished in 47.25s; the
final library SHA-256 is
e95dcf3e6b1a4c5915371d040c2fbef3853f56c97d0881f8c81814d506aeb422.

The unchanged native harness then executed the newly generated rectangular
shader on SwiftShader through Vulkan. All 15 output words exactly matched the
separate-rounding reference; elapsed time was 0.728s. Three additional small
1x1x2 cases passed the fusion-profile reference: fusion-sensitive arithmetic
returned 00000000, signed-zero accumulation returned 00000000, and the subnormal
case returned 00400001. The fusion case permits either separate or fused output;
its observed zero does not demonstrate that the runtime fused the operation.
No more native cases were needed for this checkpoint.

Retained these four reports in test/wgsl/evidence/macos-swiftshader together with
runtime.json, recording source/lock/driver/library/toolchain identities. Optional
extension warnings (swapchain colorspace, memory budget, portability subset)
remain in the reports; shader compilation, dispatch and readback succeeded.
These records establish only the tested executions. Universal runtime profile
conformance and independent artifact-package checking remain open.

Added build-macos-cpu.sh with the exact successful build configuration and an
installation check that reuses existing Rust components. Its checked repeat run
completed with the same native hash and no source modification. run-macos-cpu.sh
sets the native library and CPU driver for the existing harness; the wrapper was
used for all four successful executions. Neither wrapper introduces a new
shader executor. Report creation now rejects existing paths and uses exclusive
creation so repeating a command cannot destroy previous evidence. A focused
regression covers that preservation behavior. No system-wide tool installation,
VM, browser process or remote execution is used by the successful path.

Final checkpoint checks: all nine arithmetic/harness boundary tests pass in
1.148s, including rejection of an existing evidence path. Shell syntax checks,
the repeated setup command, the exact shader-byte comparison and git diff
whitespace checks pass. The modified harness also repeats the rectangular CPU
run successfully using a fresh report, preserving the original four captured
reports. Reviewed the five binary32 proof modules, generator CLI, Mac setup/run
scripts, evidence, preservation guard and status documentation. No sorry, admit,
new axiom or native_decide occurs in the new Lean sources. The coherent checkpoint
is ready for non-forced publication on wgsl; Wasm composition and independent
package checking are not claimed complete.

The runtime/binary32 checkpoint cbd61b4777332abf6b1f5fb30bf95e2a887e6bb2 was
published with parent ca6775030492aa2beb504867c1ac942b79fb3cca and tree
58d45ec16d2458b495dd3c8c5d7eb034edd9feb9; exact fetched identity and clean status
were checked. The user has now requested completion of the next plan: a single
generate/verify/run path, a small size corpus, and a verified Wasm host/kernel
composition, while checking concurrent GPT work on the parent branch.

Fetched origin and established that wgsl diverged from main at
00a011520a4da0085f66b3f38a5aa4be494eb401. The observed main tip f38cb7a3 has thirteen
subsequent commits: complete tiny-model inference execution, checkpoint ranges,
runtime weight validation/clipping, wider LayerNorm bounds, and degree-eighteen
negative-exponential numerical proofs. Its new exponential generated-Wasm
execution proof and complete model numerical composition are still open.
Inspected these changes without modifying main or merging its ongoing work.

Manifest.lean now describes the runtime metadata and proves its agreement with
the shader configuration and selected profile. Package.lean connects any
independently parsed supported shader to the existing binary32 dispatch,
numerical and restricted exactness results. The first Manifest check found a
constructor/theorem name collision and a shadowed fusion identifier. The next
Package check needed the artifact's kernel projection exposed before rewriting
the profile. Failed drafts/logs remain in task work/ and tmp. The corrected
Manifest and Package builds pass in 1.1s and 3.2s, with standard-only axiom audits.

Prepare.lean reads actual shader/manifest files, parses the shader independently
and emits untrusted token hints and a proof draft. Separate kernel reductions
check lexical identity, parsing, resource validity and manifest agreement. The
first draft incorrectly indented multi-line structure literals; the next used
an inferred theorem type where Lean requires a declared type. Retained both
failed attempts and corrected the emitter's indentation and proof aliases.
Aliases produce the harmless defProp linter warning; their complete axiom
dependencies are still checked. No limits were increased and no timeout occurred.

The package driver is exposed through tools/artifact-proof.js wgsl-build,
wgsl-check, wgsl-run and wgsl-corpus. Checking never trusts a generation result,
an existing receipt or a supplied proof file: it prepares and checks a fresh
proof of the actual frozen input. The kernel theorem concerns exact shader text
and typed metadata; JSON decoding and file identity remain explicit checker
operations. A cross-check rejects differences between the JSON interpretation
and checked metadata, including extra fields. The executor receives the verified
snapshot directly over stdin, and its evidence must identify those same bytes.

The rectangular end-to-end gate passes with 15 exact outputs. The fixed six-case
corpus in build/wgsl/verified-corpus-v1 then passes: 1x1x1 separate, 3x5x2 separate,
9x17x3 fusion (153 output cells and partial workgroups), plus rejection of an
incorrect store address, wrong dimensions and extra metadata. All failed
attempts remain intact. Accepted package inputs, proof drafts, verification
receipts and native reports are copied without replacement to test/wgsl/packages.
All ten focused Python harness tests pass in 1.186s, including protection against
reopening changed input files after verification. JavaScript syntax checks pass.
The runtime profile assumption and the numerical theorem's domain remain explicit.

This checkpoint completes the generate/verify/run and small-corpus steps. The
next step uses Talos's existing HostEnv/HostSpec and authoritative small-step
host-call rule to connect the checked shader with an actual Wasm host artifact.
The existing exact-binary decoder excludes imports, so that byte boundary must
also be addressed before claiming the new Wasm artifact verified.

The minimal host artifact is now 90 bytes: one imported gemm_f32 function,
three i32 offsets, an exported run function, and exported memory. HostBinary
checks its exact sections against the existing Wasm binary grammar and a narrow
function-import grammar. The existing import-free decoder remains unchanged.
Whole-file definitional decoding exhausted the default heartbeat budget, and
the code-section parser reduction also exhausted it. The retained drafts/logs
show both failures. Splitting into per-section proofs and constructing the four
instruction encodings directly solved the proof boundary without changing any
limit. The general Talos validator includes opaque partial computations, so no
kernel reduction of that validator is claimed. The interface check, normative
binary grammar, actual instruction execution, and external wasm-tools validation
are checked separately.

HostMemory proves byte upload correspondence, output readback correspondence,
i32 address conversion without wrapping, and preservation outside the written
region. This avoids importing native-decide bitvector round-trip evidence into
the standard-only proof gate. HostExecution uses the authoritative small-step
local.get, host-call and finish rules. Its contract explicitly requires the
foreign runtime to execute the checked shader on snapshots and copy completed
output back; it does not claim the Python/JavaScript/native driver is verified.
Input regions may overlap because both uploads precede output copying. Resource
caps and in-bounds, aligned addresses are explicit preconditions.

The composed host theorems prove finite completion and final Wasm read32 equality
for the separate profile, plus the conditional numerical bound for either
profile. All public host/transfer/encoding results use only propext,
Classical.choice and Quot.sound. HostCheck independently compared the actual
wasm-tools-produced binary with the kernel-checked bytes and passed. Corrected
proof-layout, existential-trace and projection-rewrite drafts remain available;
the final focused build took 3.9s. The native Wasm-to-WebGPU runner remains the
next step; this checkpoint makes no claim that it has already executed.

Published the checked host foundation as fe87593562b705cd227ce7eb3538af608a721721
with parent 9b378e1925f326d46d5bf2964fe5a301f6a41a71. The native bridge then ran
the actual exported Wasm function through Node's built-in WebAssembly engine.
Its import snapshots the two memory regions, sends the checked shader and words
to the existing wgpu-native worker, validates the returned buffer, and copies it
back before returning zero. SwiftShader's CPU Vulkan adapter produced all
fifteen expected words in the first rectangular run; every byte outside C was
unchanged. No new library, browser process, Metal backend or VM is involved.

The bundle commands independently check both artifacts. Existing shader checking
is followed by exact host-byte comparison and a fresh BundleProof instantiating
the host execution/numerical theorems with that checked shader package. All
axioms remain standard-only. The runtime receives the held shader text and
instantiates the held Wasm bytes. Existing proof files and receipts are ignored
as authorities. The adapter and execution engines are explicitly outside the
formal proof; HostExecution.contract states their required behavior.

The complete fixed bundle corpus passes: scalar (one output), rectangular
(fifteen), partial workgroups (153, fusion profile), and a changed host call
target rejected by the exact-byte gate before instantiation. Four boundary
tests pass through the actual Wasm body using a controlled import: argument/byte
order, overlapping input/output snapshots, seven invalid-address cases rejected
before dispatch, and malformed output rejected before any write. The ten
existing reference/harness tests pass in 1.211s. JavaScript and shell syntax,
diff whitespace, and the 136 maintained-document checks pass. Positive worked
bundles, composed proof drafts, receipts and native results are preserved in
test/wgsl/bundles; all execution attempts and rejected inputs remain in build/.

Rechecked concurrent parent work. Main advanced from f38cb7a3 to
9f231789 with four commits: the negative exponential's generated-Wasm execution,
wider GELU numerical results and generated-Wasm execution, and wider softmax
verification using relative weight bounds. The wider GELU bound is 200000u;
softmax's sum of absolute probability errors is at most 10053u, with
normalization error at most 52u (binary64 u = 2^-52). The parent still records
GPT integration of these replacements and the composed model numerical bound
as open. No concurrent parent changes were merged or edited.

The current three-step GEMM plan is complete: one generate/check/run path, a
small size/rejection corpus, and an exact verified Wasm host composed with the
checked WGSL kernel and executed through CPU WebGPU. The broader WGSL roadmap's
mixed-precision GPT composition and performance stages are not claimed complete.

An additional independent wgsl-bundle-check of the saved scalar bundle passes
from test/wgsl/bundles, without generation or native execution. This confirms
the worked artifact is sufficient for a fresh package check. Final review
moved the bundle rejection case into the same checked corpus configuration as
the positive shapes; its mutation bytes and expected rejection match the
retained corpus attempt. No additional Lean or runtime test scope was added.

## 2026-09-17 — Full-roadmap continuation and parent integration

The user's instruction now explicitly covers the entire WGSL agenda, including
mixed-precision GPT integration and the subsequent performance stage. The
completed GEMM bundle is a checkpoint, not the completion of this request.
Fetched main at 9f2317890ab72e89483b81e32213efb91945d146 and prepared a conflict-free
merge preserving both branch histories. The parent brings complete tiny-model
inference execution, checkpoint output bounds, runtime weight preparation,
wider LayerNorm, and the negative exponential / wider GELU / wider softmax
component results. Its composed real-model GPT numerical theorem remains open.

The first selected GPT operation is the 4-by-256 vocabulary projection of the
last hidden row. Binary64 hidden-state computation and bias addition remain
explicit in the mixed-precision specification. Binary64-to-binary32 conversion,
source-ordered binary32 GEMM, and exact binary32-to-binary64 conversion each
need their own proof boundary. The existing small-input GEMM error domain is
insufficient for checkpoint hidden values bounded by seven and weights bounded
by four. General binary32 packing and dyadic-rounding lemmas are being prepared
before using the projection in a new artifact. Native Float conversion externs
are opaque in the pinned interpreter and are not a numerical proof.

The aggregate inference dependency build reached its 180-second limit without
an error. A second, narrower inference execution build also exhausted its
120-second aggregate budget while building dependencies. Split subsequent
checks into softmax, projection, contraction, and hidden-state composition;
the first three pass with only the standard three axioms. The failed aggregate
logs and all completed dependency artifacts are retained. No timeout or
heartbeat limits have been increased, and no unrelated regression suite is run.

The hidden-state check also exhausted its 120-second aggregate budget after
spending 69 seconds compiling HiddenCode and completing the composition macro
module. No error was reported; the final hidden theorem was not rechecked to
completion in this attempt. This merge checkpoint records successful softmax,
projection and contraction execution checks, not a new full-inference proof
run. The imported source and its parent history are unchanged. Subsequent work
will use smaller theorem boundaries where this composition is required.

The new binary32 foundation passes at the default heartbeat limit:
F32Packing proves finite packing below scaled magnitude 2^276 and a relative
error of 2^-24; F32AddBounds transfers it to addition/subtraction for exact
results of magnitude below 2^127. F32DyadicBounds proves single rounding for
arbitrary positive extra fractional-bit counts, including subnormal outputs.
F32MulBounds obtains error at most 2^-24 times the exact product magnitude plus
2^-150, again below the explicit finite-range bound. Every printed public
result uses only propext, Classical.choice and Quot.sound.

The binary64 proof structure supplied the packing/multiplication scaffold;
existing IEEE32 field and roundShift lemmas supplied the trusted arithmetic
steps. Direct reduction of the zero encoding caused kernel recursion, and broad
simplification around powers exhausted default heartbeats. A separate zero
encoding lemma, separate scaled-half lemma, separate small-magnitude lemma,
and explicit power rewrites resolved those boundaries without larger limits.
Failed drafts remain in the task work directory and failed logs in tmp/.
The accepted packing build took 2.0s; addition 2.9s; multiplication 3.4s.
These are numerical foundations, not yet a GPT artifact theorem.

Re-fetched the parent: main advanced to
8309cc9bf88d69553fb4aa81bd4f09fe809e94d4, integrating wider exponential,
GELU and softmax into the actual GPT inference artifact and execution theorem.
The parent still records the complete real-model error composition as open.
This change will be merged separately; no concurrent parent files are edited.

Published the binary32 foundation as 7a7540cfd368d1c32effa43f14ffdc5b40f25cce.
Merged parent 8309cc9bf88d69553fb4aa81bd4f09fe809e94d4 without conflicts.
The updated Model target passes locally, and the checked CLI executes its
17,371-byte Wasm artifact on the four bytes "Lean", returning 256 finite logits.
Maintained-document checks and staged whitespace checks pass. The parent's
journal records successful full generated-WAT gates (hidden semantic proof
174–180 seconds) and 1,656 trained hidden/logit checks. Those are parent results,
not a claim of a fresh complete local gate. Earlier 120-second hidden checks
here were below that known semantic-proof duration; future integration checks
will use the documented evidence and separately compiled dependencies.

The conversion and wider accumulation composition now passes. F64ExactShift
proves exact rounding of shifted significands; Precision uses it to prove exact
finite binary32 promotion, including the sign, and uses the general dyadic
rounder to bound binary64 demotion by 2^-24*abs(input)+2^-150 below magnitude
2^127. F32DyadicReal is the shared real interpretation of that rounder.
The definitions are pure integer conversion models; opaque native conversion
externs are not substituted into their proof statements.

The fixed precision-vectors corpus has 14 promotion and 21 demotion cases:
both zeros, smallest and largest subnormals, normal boundaries, adjacent
midpoint words, both ties-to-even directions, checkpoint magnitude bounds,
and a large safe exponent. All 35 pure-model words and native CPU conversion
words equal the recorded expected words. No new package or backend is involved.

WideScalarError proves the per-update error for both modeled accumulation
choices. WideAccumulationError establishes intermediate finiteness, magnitude
and accumulated error using explicit product and accumulator budgets; it
removes the old magnitude-at-most-one restriction. ArtifactNumerical, Package
and HostExecution compose this result through the actual output memory read.
All public audits use only the standard three axioms. The wider host build
took 3.8s; the dot induction 3.6s; the conversion proof 2.7s.

The independent generator/checker now instantiates and audits both numerical
domains. A fresh check of the saved scalar bundle passes at
build/wgsl/package-checks/check-K0hNvR, including exact shader text, exact
Wasm bytes, both host numerical theorems and the separate-profile exactness
result. No prior proof or receipt is trusted. JavaScript syntax, maintained
document checks and diff whitespace pass. The earlier failed cast/rounding
drafts and diagnostics are preserved. Next is the four-term GPT projection:
converted hidden coordinates, converted weights, binary32 GEMM, exact promotion,
and binary64 bias, followed by its full hidden-state error composition.

The four-term vocabulary head now has a checked specification. HeadNumerical
uses the checkpoint's hidden bound 7 and coefficient/bias bound 4. Conversion
error is bounded before multiplication; the wider dot domain uses accumulator
budget 161 and product budget 40. The resulting dot error is at most 1/12000;
exact binary32 promotion and binary64 bias addition give 1/10000 per logit.
GptHead connects an independently parsed 1x256x4 shader dispatch to this relation
and proves bit equality with the declared separate-operation mixed specification.
GptHeadCheckpoint discharges the input bounds for all four-byte inputs and all
256 vocabulary coordinates. Its full-real-model staging theorem explicitly
requires hidden error E and gives 1/10000+16*E; that premise is not yet discharged.

HeadNumerical checks in 3.7s, GptHead dispatch in 3.8s, and the checkpoint
instantiation in 3.9s, all with only propext, Classical.choice and Quot.sound.
The initial dispatch draft had a nested-structure indentation error and a
free-variable decide call; the corrected proof uses direct size reflexivity.
The failed draft and logs are retained. Cold checkpoint prerequisites reached
a 120s aggregate timeout; splitting at SoftmaxWide.Row, CheckpointScore and
CheckpointAttentionValue completed the needed boundaries without raising proof
limits. CheckpointFinalNorm and the residual prerequisites then passed.
The parent origin/main remains at 8309cc9b, already merged.

The head bridge theorem now reads the actual final Wasm memory word and proves
it belongs to GptHead.Result. Its Inputs contract identifies the four converted
hidden words and 1,024 converted weight words. Dot.congr_buffers is a small
reusable lemma showing that only the accessed prefix coordinates matter.
This avoids incorrectly requiring equality of unused buffer addresses.
GptHeadHost checks in 3.9s with standard axioms. The first draft exposed an
unreduced artifact projection and exhausted default heartbeats; making that
boundary's buffer types explicit resolved it without increasing limits.

FinishBinary independently proves exact parsing, validation and execution of
the 61-byte binary64 bias-addition artifact. FinishCheck compares the supplied
file to those exact proved bytes. The build took 4.7s; its saved-file check
passes with standard axioms. Earlier constructor and tactic-import failures
are retained. Promotion is an explicit input to this Wasm operation, not an
unproved claim about a native conversion instruction.

The local compiler executable was stale (September 7) and rejected the merged
Wasm.IEEE64.add primitive after the first 60s compile attempt timed out. The
split WAT diagnostic exposed that rejection. Rebuilding the extraction module
and compiler resolved it; the current compiler emits the expected 16,006-byte
hidden module, SHA-256 d03534266e4171a07512566429763ba890506ba306a6073379d2433b395837a2.
Its exact binary proof is next. GptHeadGenerate successfully emits the selected
Lean head candidate. Maintained-document and whitespace checks pass.
The generated head package also passes a fresh independent shader gate at
build/wgsl/package-checks/check-FIwx6w. This checks exact shader text, manifest
agreement, both numerical domains and restricted exactness; it does not yet
constitute execution of the full GPT bundle.

The hidden artifact proof now checks its exact 16,006-byte representation and
function decoding for functions 0–23. Raw-module hints are generated by the
existing pure decoder, then checked through independent kernel proofs. Balanced
byte lookup is reused from the existing artifact framework. Function-type
resolution and static validation of functions 0–3 also pass. These are partial
binary-proof milestones; the whole hidden artifact theorem remains open.

Direct CBV decoding hit recursion limits on several bodies. Eight-instruction
sequence certificates, including nested branch certificates, resolve those
failures at the original limits. Body 5 takes 20s; body 8 takes 57s; smaller
split bodies take roughly 5s. The initial 24 function decodes use only propext.
The main hidden function is split into 17 modules, but its first part exposed
an additional linear-list lookup limit at instruction index 1571. A balanced
instruction lookup boundary is being prepared; failed drafts and logs remain.

This checkpoint publishes only the checked modules. Unfinished generated proof
modules remain untracked locally and are listed explicitly for the publication
helper, rather than being included in a verified milestone prematurely.

The large hidden-body failure was reproduced with a single unreachable
instruction. Direct parsing of that instruction and its two-byte sequence
passes; the failed cached theorem instead returned another deep lookup into
the 1,937-instruction list. Literal branch results now check in 8s. The next
boundary uses opaque eight-instruction suffix chunks, with a separate checked
equality back to the complete cached AST. No recursion or heartbeat limits
were increased. Failed linear, balanced, routed and first chunk drafts remain
under the hidden-binary draft directory.

Two reusable lemmas are checked: instructionAt_apply exposes a single parser
instruction without unfolding its mutual-recursion fuel, with no axioms; and
validateInstrs_eq_append composes validation of consecutive instruction lists,
using only propext. The balanced instruction lookup itself is also checked
with the existing instrListEqualFuel_sound theorem, using propext and Quot.sound.
These supporting proofs and the now-checked first branch part are published
separately from the unfinished whole-artifact proof.

A fresh parent fetch found 26646de8, bc97edf8 and bf6fcc42. They add finite
runtime-weight GPT results, a composed real-model error theorem, and exposed
allocation state for the verified weight checker. The hidden-error theorem
is directly relevant to the remaining mixed-precision composition; it will be
merged and checked before being used.

The opaque suffix chunks check all 1,937 instructions of hidden function 74.
Each sixteen-certificate module takes about 9–10s, with 5.2s for the final
part. The final AST equality uses the existing checked Boolean equality
procedure. A first simp-based composition exceeded recursion depth; explicit
congrArg composition passes in 4.7s with propext and Quot.sound. The complete
function's decoding is established; other module decoding and validation
obligations remain separate.

Merged parent main through bf6fcc42 without conflicts. RuntimeResidual and
NumericalLogits rebuild successfully with standard axioms. GptNumerical now
uses inputHidden_accuracy to discharge the formerly explicit hidden-error
premise. Both its floor-parameterized full-real-GPT theorem and its uniform
all-four-byte-input theorem check in 3.9s, using only propext, Classical.choice
and Quot.sound. The head contributes 1/10000; hidden propagation contributes
16*ErrorBudget.hidden(4, floor1, floor2, floorFinal). This is a composed
arithmetic bound, not an output-magnitude shortcut. The uniform epsilon-floor
instantiation is extremely loose (approximately 4.85e9 at the logits) and
must not be presented as a tight numerical guarantee. Sharper denominator
and parameter-specific propagation bounds remain a quality improvement.

Function decoding now passes through index 55, in addition to function 74.
The combined 24–35 target reached its 120s aggregate timeout after finishing
most body dependencies; splitting the remaining targets completed them. The
36–43 and 44–55 groups pass without source changes or increased proof limits.
All these decoding proofs use only propext.

Direct kernel evaluation validates function 74 successfully. A diagnostic
attempt to synthesize Decidable for an Except result failed because that
instance is unavailable; checking its Boolean success observation and the
new ok_unit_of_isSome lemma avoids that unnecessary interface requirement.
Whole-module kernel-evaluation diagnostics timed out at 60s, so validation
and decoding remain split into explicit boundaries. Those attempts are
retained. The shared decode_eq_of_comparison lemma is also checked and may
support bounded Boolean decoder comparisons; it does not itself establish
this complete module's parsing.

Decoding now passes through function 67. Function 57 reproduced the deep
cached-result lookup failure, so the function-74 suffix representation was
applied to it and prepared for the remaining large bodies. Its five parts
check in roughly 8–10s each, and the final body equality/composition takes
4.1s with propext and Quot.sound. The following four-function wrapper reached
an aggregate 90s timeout after those dependencies finished; independent
function modules complete it without increasing proof limits. Functions 60–67
and their body dependencies also pass. A fresh parent fetch found no commits
beyond the already merged bf6fcc42.

All 79 function bodies now have independent decoding proofs. The final large
bodies use the same suffix-boundary construction as functions 57 and 74;
function 69's twelve parts take approximately 8–10s each. A grouped command
again exhausted its aggregate timeout after completing its body dependencies;
splitting the small wrapper functions completes the group. The final 72–75
and 76–78 groups pass with propext and, for AST suffix equalities, Quot.sound.

All 79 function validations also pass. Kernel evaluation of the Boolean
success result checks each four-function group in less than one second,
using only propext. The combined raw-module validation takes 12s and also
uses only propext. Its unnecessary dependency on binary decoding was moved
to the translation module, keeping validation and decoding distinct. The
module section decoding is the remaining binary-parser obligation.

Documentation now records the completed full-model arithmetic composition
and its extremely loose uniform bound, separately from the pending complete
artifact-execution check. The maintained-document checker passes 137 files.
The GPT runtime and gate drafts pass JavaScript syntax checks but are not
published as an executed or verified bundle yet.

The complete 16,006-byte hidden artifact is now parsed and validated, and its
translated module is proved equal to the execution model. Type-section parsing
takes 38s; function-type indices take 34s. Export-name parsing initially hit
recursion limits in byte-array slicing. Eleven exact slice equalities, checked
by kernel evaluation in 9.8s, give that parser a small reusable boundary; the
export section then passes. Memory, globals and the composed code section pass.
The full binary-to-execution-model theorem checks in 4.8s with only propext,
Classical.choice and Quot.sound. Failed export drafts and logs are preserved.
This establishes artifact identity and validity; the hidden execution theorem
and complete native GPT bundle still need their final local checks.

The isolated HiddenCode build reached its 60s limit. Separating the equality
from the definitions showed the data declarations alone also exceeded that
bound. Seven small definition modules now check in 8.6–22s each, retaining
the same tail definitions and public names; program_eq checks in 3.8s. The
reusable Composition macro also checks independently. This split preserves
the original source and failed logs and adds no proof axioms or limit changes.
The final hidden execution theorem is now being checked with these prepared
dependencies. Parent main remains at the already merged bf6fcc42.

The complete hidden execution theorem checks in 155s with only propext,
Classical.choice and Quot.sound. GptHiddenArtifact needed an explicit module
property when applying artifact_correct_of; the first failed elaboration and
its diagnostics are retained. With that property supplied, the exact hidden
binary theorem and the complete GptBundle artifact theorem pass. GptBundle
checks in 4.2s and uses only the three standard logical axioms.

The independent GPT gate then accepts the exact shader/manifest, the 16,006-byte
hidden Wasm, 90-byte dispatch bridge, 61-byte bias-addition Wasm and 2,488-word
checkpoint. The complete pipeline executes on SwiftShader CPU through native
WebGPU. All 768 logits for Lean/zero/byte-edge token cases exactly match Lean's
integer floating-point model. Hidden memory and bridge memory outside C are
preserved. Altered hidden bytes, finish bytes and checkpoint bytes are rejected
by the same exact-file gate. The six-case evidence is retained at
build/wgsl/gpt-corpus-20260917-a and check-CIiblJ; the portable artifacts and
recorded evidence are also kept under test/wgsl/gpt. Native orchestration,
conversions and runtime conformance remain explicit assumptions, and the full
real-model bound remains extremely loose. Performance work follows this gate.

The five fixed head performance candidates all pass independent artifact
verification and native output checks: one-row 8×8, 32×1 and 64×1 workgroups,
plus three-row 32×1 and 64×1 batches. Two warmup and nine measured rounds check
84,480 words. Recreating each one-row pipeline costs approximately 17.9–18.4ms
per three contexts; one resident pipeline costs 0.276–0.300ms. A resident
three-row batch costs 0.120–0.121ms. Those are CPU-only measurements; the small
32/64 workgroup difference is not a reliable selection criterion. Portable
artifacts and reports are preserved under test/wgsl/head-performance.

Stage timing also identifies roughly 445ms of native process setup per
unshared inference. A bounded resident session now reuses one process, weight
buffer and pipeline behind the unchanged synchronous Wasm import. Its first
complete run matches all 768 Lean logits, rejects a changed resident-weight
snapshot, and closes the native process and Node worker before success. Warm
head calls measure 0.783–0.856ms, with about 1.1–1.2ms for all three Wasm/WGSL
stages excluding proof/reference generation. A final focused run checks the
separate native-startup timing field added after that first successful run.
The four existing Wasm host boundary tests also pass after the native adapter
refactoring. No new Wasm binary or new trusted axiom is introduced.

The final resident-session run also passes all 768 exact logit comparisons and
the changed-weight rejection, with one weight upload, one pipeline and three
dispatches. Native startup is now recorded separately, and orderly native/worker
shutdown is checked before success. Its complete receipt and output evidence
are preserved in test/wgsl/gpt/session-evidence.json and check-TiMETC. The
maintained-document checker passes 138 files. This completes the WGSL agenda
within the user's explicit server-side CPU scope: the exact heterogeneous GPT
artifact theorem, native execution, residency, batching/workgroup experiments
and documented decisions about additional operations. Physical-GPU conformance
and tighter full-model accuracy bounds remain clearly identified research
extensions, not claims supplied by these CPU results.

The numerical audit begins from the unchanged artifacts at 59f57a59 and the
research notes at 385b05d3. A parent fetch found checked runtime-weight
inference and the coarse magnitude cap in 9fb277da. Six diagnostic cases now
compare a source-order JavaScript transcription against the existing hidden
Wasm, and compare its real target at 80 and 120 decimal places. All 24 hidden
words and all 768 recorded checkpoint mixed logits match. The opposite-sign
adversarial embeddings both round to the same constant row; their real logits
are separated by approximately 119.8454. The mathematical lower-bound argument
and exact rational checks are retained separately from execution evidence;
they are not presented as a new Lean theorem. This establishes reproducible
inputs for the three requested audits without generating a new artifact.

The numerical audit now records every intermediate stage for six contexts.
A diagnostic Lean executable calls the existing pure floating-point definitions;
all 3,888 resulting words agree with the JavaScript transcription. The stage
report distinguishes fresh local rounding/approximation from error inherited
from previous stages. For the signed adversaries, the first embedding addition
loses 2^-55; later large errors occur even where fresh local error is zero.
These are finite executions of existing definitions, not new universal theorems.
No Wasm or WGSL bytes changed. Sequential runner logs are retained under
`build/wgsl/numerical-audit`; portable traces and stage reports are checked in.

The three numerical audits are complete. Exact-real sensitivity, fresh rounding
and proof slack are reported separately, retaining the single cap B=4. The
strict counterexample concerns the existing evaluation order, not every
algorithm for the real model. Pointwise finite differences converge under two
step sizes and show a large contrast between the checkpoint and the constructed
parameter family. That contrast is diagnostic, not a universal guarantee.

Component-preserving centering repairs the first loss but leaves cancellation
in nearly uniform weighted attention. A second binary64 prototype computes the
small weighted deviation with expm1. Across twelve fixed cases its binary64
logit error is below 5.7e-15; its mixed error remains below 1.24e-6. It calls
native Math.expm1 and is deliberately kept outside the production compiler and
artifact pipeline. Neither prototype has a universal accuracy proof. Existing
checkpoint errors sometimes increase by a few ulps, so it is not described as
an improvement on every input.

Recomputing the unchanged proof recurrence attributes 98.3251% of its 4.85e9
allowance to the first normalization's local allowance and its later propagation.
The report derives sharper normalization, attention and GELU constants and a
shared-head range cap below 128.000046, without claiming these are already new
Lean theorems. Parent main at 9fb277da was inspected: its checked runtime-weight
inference and 1456 cap remain separate from the unchanged artifacts measured
here. All new evidence is reproducible with the focused audit driver; no broad
project regression, new native dependency, Metal setup or Wasm generation was
needed.

A final remote check found main advanced to 529a5e85 with a trained 64-position
checkpoint and sequential-sum bounds. Its inference implementation/proofs are
explicitly still in progress. Inspection showed no changes to the four-position
ErrorBudget or CheckedBounds under audit. The report records the new parent
state without substituting its distinct checkpoint into these measurements.

Float-level verification development starts with an independent algorithm
specification over UInt64/UInt32 words and typed vectors/matrices. It explicitly
fixes balanced binary64 dots, sequential binary32 accumulation from positive
zero, normalization arithmetic, causal masking, coefficient words, nonlinear
branches and finite-input precision conversion. It does not import the GPT
implementation model or a real-number specification. Pure conversion definitions
were separated from their numerical theorems without changing the definitions.
The specification and conversion model build successfully; correspondence and
artifact integration are the next verification steps, not yet claimed here.

The independent float algorithm now has universal correspondence proofs for
its primitives and complete hidden computation. The theorem covers arbitrary
parameter words, every four-byte context and all four valid positions; the
artifact theorem will additionally require the packed parameter array to fit
in memory. All public proof axioms are standard logical axioms. An initial
attempt to infer projection indices through expanded IEEE operations exhausted
the elaborator heartbeat limit; specifying the four finite indices explicitly
removed that boundary and the complete network module checked in 5.9 seconds.
A preliminary bit-vector tactic introduced native decision axioms, so that
approach was discarded. The accepted sign-setting specification uses explicit
mask/add word operations with direct logical correspondence instead.

The new GptFloatArtifact theorem now composes exact hidden Wasm decoding,
validation and execution with the parsed WGSL head, bridge readback and finish
Wasm. Its output contract compares both the raw binary32 head word and the
final binary64 result with the independent vector algorithm. It is parameterized
by runtime parameter arrays, all four-byte contexts and all four positions;
it has no real-valued reference or error allowance. Native transfer/conversion
and restricted-profile runtime conformance remain explicit premises. The shared
head bridge proof now exposes the raw Dot result before bias addition, avoiding
an inference of raw-word equality from a potentially non-injective final add.
The artifact module checked in 3.8 seconds with standard logical axioms only.

The float contract now has seven kernel-checked word examples covering signed
zero, preserved subnormals, balanced versus sequential accumulation, the
exponential cutoff and canonical NaN arithmetic. Export-name checks also bind
the hidden and finish interfaces to the proved function indices. Public axiom
audits still contain only the three standard logical axioms.

Direct evaluation of the function-valued independent algorithm reached the
120-second reference limit. A first function-returning cache was proved equal
but still reached a 60-second diagnostic limit: returning a function did not
establish the intended sharing during compiled evaluation. The accepted
evaluator returns concrete array tables at each intermediate stage and proves
their lookup function equals the original specification. Its proof checked in
249ms, and a standalone checkpoint reference evaluation completed successfully.
The failed diagnostics remain under build/wgsl/float-spec and the original
package attempt check-ol7hQT. No artifact or algorithm bits changed to make the
reference run. The focused exact-word execution corpus is the remaining gate.

A fresh parent check found main advanced to 6ba953cb with a trained 128-position
checkpoint and revised source-equivalence plans. That commit changes training,
data and documentation, not the four-position implementation or proof modules
being checked here. It remains separate from this artifact comparison.

The independent float package gate and ten-case corpus now pass. Six CPU
executions cover all four positions, alternate checkpoint contexts, and both
adversarial parameter arrays. All 24 hidden words, 1,536 raw binary32 head words
and 1,536 final binary64 words match the independent checked reference. The
four rejection cases fail for their specified reasons. The package theorem,
interface checks, correspondence proofs, table evaluator and seven word examples
pass the standard-axiom audit. Portable evidence is in test/wgsl/float-spec;
full attempt diagnostics remain in check-sNdkJe and float-spec/corpus-v2.

The accepted generated package proof is a small composition of the generic
GptFloatArtifact theorem with the independently parsed shader's shape/profile
equalities. There was no per-context proof synthesis or artifact regeneration.
Runtime reference evaluation uses the proved table evaluator; native execution
uses the existing SwiftShader CPU adapter through Vulkan. The focused numerical
audit regression remains unchanged, including all six reports and 27 exact
rational comparisons. The maintained-document check passes 141 files.
The existing GptBundle module also rebuilds successfully in 4.1 seconds with
standard logical axioms, confirming that the shared raw-word dispatch lemma
preserves its previous theorem. JavaScript syntax checks and diff whitespace
checks pass. No unrelated project regression suite was run.

GPT2/128 development starts by merging parent main at 2f4e024a into wgsl in
28575838. The parent supplies the trained 2,984-word checkpoint, sequence source,
six source/native comparison cases, and exact sequence sum/maximum execution
proofs. Its complete hidden-Wasm execution theorem is still unfinished. The
merged four-position artifact theorem and sequence inference source build.

The first 128-position execution path therefore evaluates the parent's hidden
function directly in Lean and retains the proved Wasm bridge, parsed WGSL head,
and proved finish Wasm. No unfinished 128-position Wasm is executed. The user's
optional choice between this path and completing the entire Wasm proof first
was requested; independent head integration proceeded while awaiting a reply.

TinyGpt2Seq.Mixed names the mixed-precision function separately from the parent's
binary64 inference function. Its checked entry reuses F64Clip.prepare. The new
GptSequence theorem connects the head at offset 1,680 and bias at 2,704 to the
same checked 1x256x4 shader. The head equality, raw dispatch equality and composed
bridge/finish theorem pass with standard logical axioms; the final module checks
in 3.9 seconds. The exact function and theorem are shared across all sequence
lengths and runtime parameters. Native Lean evaluation and transfer remain
explicit execution boundaries. The runtime gate/corpus is the next check.

The GPT2/128 gate and corpus pass in check-hTFGw7. Seven cases include lengths
one, four, 64 and 128, full-length zero/255 contexts, and clipping at 0.5. All
1,792 raw head words and 1,792 final logits match Lean; four invalid token-domain
cases are rejected. The checker validates all required reference fields and
compares native promotion words explicitly. No new Wasm or shader is generated.

Parent main advanced to bd6f58dc during the run. Its sequence map execution
proofs and shared allocation lemmas were merged in f50ddf39. A second complete
head package check and execution in check-d7rBqu uses a readable 128-byte prompt
ending "outrageous fortune". All 256 head and final words match; space is the
highest-scoring next byte. Both verification receipts are identical, including
all recorded model source hashes. The older GptFloatArtifact also builds after
the parent merge, with standard logical axioms. The maintained-document checker
passes 142 files.

The accepted proof reuses dispatch correspondence and exact finishing lemmas;
its only layout-specific work is the head buffer mapping. It does not attempt
to recreate the parent's unfinished sequence allocation/hidden-Wasm proofs.
The small input review checks the changed matrix/bias offsets, UTF-8 byte limits,
bounds, malformed tensor shapes/counts and malformed parameter words. Portable
evidence in test/wgsl/gpt128 retains all eight native runs and complete Lean
reference values. The maximum observed mixed-versus-binary64 difference is
1.0703345028062472e-6, recorded as an observation only. The executable command
and documentation identify the Lean hidden stage and incomplete full-Wasm proof.

## Native/browser GPT2/128 demo preparation

The user requested both interfaces with model computation entirely in generated
Wasm/WGSL and no generated artifacts checked in. Parent main through f6bd2cff
was merged in 17131e8f. Its sequence-softmax proof is complete; the registry
still marks tiny_gpt2_seq incomplete. A fresh fetch finds no newer parent commit.

The first hidden-entry compilation failed at normalizedInputs with the old
local compiler executable. Parent development notes identified the existing
structured-array materialization fix. Rebuilding lean-wasm from current source
resolved the failure without source changes; the direct hidden entry emits a
21,070-byte module and passes wasm-tools validation. No unchanged failing
compiler invocation was repeated: the executable was rebuilt first.

The native C host builds against the existing Wasmtime C API and wgpu-native.
It loads the generated transformer, existing WGSL and finish bytes, plus a
small Wasm transfer/greedy adapter. Conversions and selection stay in Wasm.
The adapter has no artifact proof. SHA-256 identities are embedded in the
native executable at build time. Output, weights, generator output and tests
are under ignored build/. Source and a browser page layout are prepared.

Execution is waiting on explicit resolution of the earlier requirement for
completed Wasm proofs. Browser host bindings likewise await clarification of
whether JavaScript is permitted for API/UI/byte-transfer work only. No model
port to JavaScript was made, and no unproved Wasm was executed in this step.
C compilation, shell/Python syntax, Wasm validation, and an empty-prompt
rejection pass. The native differential and generation tests remain unrun.

The user subsequently authorized incomplete proofs for the demo. Native
execution now passes all eight retained Lean references, including the clipped
weights: 32 hidden words, 2,048 raw head words, and 2,048 final logits match
exactly. The focused test also runs 160 generated bytes across the context
window boundary, rejects six invalid inputs, and rejects an altered shader.
Evidence remains in ignored build/demo-test-_tywjlgo. The first 32-byte run
continues "To be, or not to be" with repeated "the", faithfully reflecting
this tiny checkpoint's greedy predictions. The browser host-only JavaScript
question was explained; browser bindings remain pending that clarification.

The user approved browser host bindings. The static browser version now runs
from localhost with model arithmetic, conversions and selection in Wasm/WGSL.
Actual UI tests execute all eight references: all 32 hidden words match; the
browser GPU returns 773 different head words out of 2,048, with matching final
logit differences. These are reported, as the user accepts WebGPU semantic
differences. The page produces the same 64-byte greedy repetition as native.
The build creates a portable browser ZIP under ignored build/.

The user then required a decent completion. Inspecting logits shows the trained
width-four checkpoint has a greedy space/t/h/e cycle, with only about 0.13
probability on t after a space. This is not stale output or failed dispatch.
The model's recorded validation cross-entropy is 2.6916 nats. A larger trained
checkpoint is being evaluated separately; a pending scope question distinguishes
actual pretrained GPT-2 from a smaller Shakespeare transformer. No new checkpoint
or generated artifact is committed. The original exact-reference tests remain
unchanged so that the demonstration cannot hide altered model semantics.
