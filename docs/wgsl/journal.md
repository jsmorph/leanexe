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
