# UInt64 comparison-controlled conditionals

Candidate `b06b8e12` extends the general source-to-exact-Wasm theorem to ordinary
UInt64-valued conditionals over `=`, `<`, `≤`, `>`, `≥`, `==`, and `!=`. Arbitrary
nesting with arithmetic and pure UInt64 let bindings is covered, including
conditionals inside comparison operands and bindings inside either branch.

Admission recognizes the exact standard comparison instances and their complete
decision evidence. Source evaluation selects one branch; static validation
bounds cover both branches. Dependent conditionals, general Boolean expressions,
Boolean binders and effects remain outside this increment.

The pinned environment remains Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0, macOS arm64, and
authorized local `tools/leanrun` execution under the shared serial lock.

- `tools/arithmetic-check.js proof` passed the general acceptance, successful
  admission, exact-byte decoding, whole-module validation, export and invocation
  theorems, with all nine axiom audits. Lake reused unchanged dependencies.
- `tools/arithmetic-check.js engine` passed admission/reserved-export checks and
  254 native Lean/V8 comparisons across twenty declarations. Eight new emitted
  modules are retained here alongside all expected native results.

The first execution attempt is retained because it exposed distinct elaborated
`GT.gt` and `GE.ge` heads. The completed candidate explicitly recognizes those
forms, checks reversed decision arguments, and proves their lowering through
unsigned comparisons and Boolean negation. The final execution log includes all
nested-choice cases that the first attempt could not compile.

The arithmetic source archive remains fixed. No type-safety implementation or
independent runtime semantics changed, so their full checks were not repeated.

The focused `test/scalar_class_evidence.lean` check also passed through
`tools/leanrun --timeout 60 lake env lean`, covering standard and custom source
instances through the normal compiler against native Lean evaluation.
