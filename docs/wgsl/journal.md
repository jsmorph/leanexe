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
