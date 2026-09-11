# LeanExe type theory and specification notes

## Scope

The user requested a formal type theory for LeanExe's subset of Lean, followed by a full formal specification, on 2026-09-11.  The assigned files are [Type Theory](../docs/leanexe-type-theory.md), [Formal Specification](../docs/leanexe-formal-specification.md), and this journal.  The Euler work continues in the same checkout.  This task changes no implementation, existing documentation, proof, dependency, or generated artifact.

The documents describe mathematical judgments with explicit links to the compiler's executable recognizers.  Kernel typing, extraction acceptance, representation, ownership, emitted WebAssembly behavior, and artifact theorems have separate judgments.  Mechanization remains a scope question for the primary agent and user.

- [x] Read repository instructions, the overview, developer guide, language specification, user manual, existing type-theory account, and operating requirements.
- [x] Inspect runtime type recognition, specialization, extraction dispatch, IR definitions, demand analysis, explicit-release checking, production lowering, and allocator code.
- [x] Write the type-theory draft with independent runtime rules and implementation-indexed acceptance.
- [x] Write the operational and compilation specification draft.
- [x] Review the stated rules against source declarations and record unresolved differences.
- [x] Have the primary agent review the documents and run documentation checks.

## Source survey

[Existing Type-Theory Account](../docs/typetheory.md) describes the fragment in prose.  [Type Recognition](../LeanExe/Extract/Types.lean) supplies executable predicates rather than an inductive typing derivation.  Its `typeAtom?`, `valueLayout?`, `supportedPublicArrayElementType`, `supportedParamAbiType`, and `specializedInlineCall?` fix the position-sensitive type and specialization rules.  [Extraction](../LeanExe/Extract/Core.lean) fixes the shape-sensitive term boundary.  Acceptance is therefore indexed by the checked environment and compiler revision.

[Reference IR Evaluation](../LeanExe/IR/Core.lean) has a restricted interpretation: `Expr.eval` returns zero for traps and many heap operations, and its `natAdd` and `natMul` use wrapping arithmetic.  [IR Evaluation Entry](../LeanExe/Extract/Eval.lean) filters heap constructs, but its scalar predicate admits traps and checked-Nat operations.  A complete compiled operational relation must use production lowering and WebAssembly execution, with the reference evaluator's narrower comparison scope stated explicitly.

[Production Binary Lowering](../LeanExe/Wasm/Binary.lean) defines `CoreWasm.moduleBytes` as `legacyModuleBytes`.  Its image path is separate.  `Extract.Core.reservedExportNames` lists `memory`, `alloc`, and `reset`, while [Language Specification](../docs/spec.md) reserves ten names.  The image validator's duplicate-export check therefore does not establish that the production path rejects every documented reserved name.  This gap was reported to the primary agent.  No compiler change belongs to the assigned task.

Primary external references are the [Lean Type System](https://lean-lang.org/doc/reference/latest/The-Type-System/), [WebAssembly Numeric Semantics](https://webassembly.github.io/spec/core/exec/numerics.html), and [WebAssembly Instruction Validation](https://webassembly.github.io/spec/core/valid/instructions.html).  The checkout's pinned source controls implementation-specific claims.  WebAssembly floating-point NaN results require a relation of allowed results when the claim quantifies over conforming engines.

## Work record

2026-09-11: Read-only source and documentation inspection completed before drafting.  No Lean, Lake, compiler, verifier, C build, or numerical process ran in this task.  The primary agent owns the globally serialized execution slot.  The initial status inspection showed concurrent Euler source and proof changes.  Those paths remain untouched.

2026-09-11: Wrote both assigned documents.  The primary agent's first review requested stronger independent typing rules and explicit limits on implementation-function references.  Added constructor, projection, match, and callback context rules, plus primitive-signature and coverage tables.  The status now identifies the remaining independent-formalization and equivalence work.  The recursion families still use exact implemented recognizer premises; the drafts make no general soundness claim.

The export-name concern is supported by `Extract.Core.reservedExportNames`, `CoreWasm.exportSection`, and `CoreWasm.moduleBytes = legacyModuleBytes`.  The child-mask concern is supported by `Values.heapChildMaskFromType`, `Binary.i64Const` reducing modulo `2^64`, and `CoreWasm.coreReleaseInstrs` using a runtime `i64.shr_u` test for each slot.  Layout recognition supplies no visible general 64-slot bound.  These are source-inspection findings.  No compiled reproducer or proof check ran, and neither issue was changed.

Read-only checks found that every relative document link resolves.  Source-declaration review corrected the expression extractor name to `extractValueFrom`, the numeric dispatcher to `extractPrimitivePairFrom`, and the proof names to `Wasm.Binary.Proof.decode_sound` and `Wasm.Binary.Proof.validate_sound`.  A prose scan removed a contrastive opening and checked the banned-word list.  The primary agent retains responsibility for repository documentation gates and integration.

The final review added context-formation conditions and checked callback signatures against the pattern handlers.  Each new file passed `git diff --no-index --check /dev/null <path>`.  The broad `git diff --check` also returned no whitespace diagnostic.  These read-only checks ran without invoking Lean or a repository verifier.  The files remain untracked for the primary agent to review and integrate.

Correction to the preceding check record: each `git diff --no-index --check` command returned status `1` and no output, reflecting the content difference from `/dev/null`.  The observed result is absence of whitespace diagnostics, rather than a zero exit status.  The relative-link check returned status `0` with an empty missing-link list.
