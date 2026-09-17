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
