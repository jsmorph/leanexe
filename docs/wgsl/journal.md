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
