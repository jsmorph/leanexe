# Id annotations on ordinary lets

Candidate `cef8b86ee0f86b663007a8f393188afc4e73bd75` supports standard nested Id annotations on ordinary let
bindings throughout admitted scalar, loop-step and surrounding range code.
The source relation preserves each exact annotated let, including its name,
value, body and nondependency flag, while relating it to the underlying let
with one standard Id layer removed. A checked size lemma justifies terminating
extraction. Underlying word, Boolean, helper and step-result binding rules still
apply; unused bound values remain checked.

Annotated numerals use matching nested Id.instOfNat evidence. The recognizer
checks every type layer, standard universe, numeral and inner instance. Its
acceptance and reconstruction proofs compose with the scalar compiler proofs.
Source totality, acceptance, source reconstruction, semantics and invariants are
checked through scalar, step and range compilation. No emitter/runtime change.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial tools/leanrun execution:

- `tools/arithmetic-check.js proof`: all nine audits, including complete module
  type validation, exact bytes and terminating source-equal exported execution.
- `tools/arithmetic-check.js subset-engine id-let`: admission, reserved exports
  and 623 native Lean/V8 comparisons across 34 declarations.

The first focused fixture passed 304 native/IR comparisons, eighteen additional
typed-numeral comparisons and 148 rejection tests. These cover four excluded
declarations, 64 malformed lets and eighty malformed numeral forms. Cases include
word/Boolean/helper bindings, nested annotations, shadowing, overflow, unused
values, captures, do notation, joined loop updates, continue/break, strided
bounds, step helpers and code surrounding loops. Bad types, universes, evidence
layers, numeral values and word/Boolean slot mismatches are rejected.

Five valid pre-implementation probes rejected and now compile unchanged.
All twenty focused/admission declaration bodies match, as do the sixteen
accepted native bodies. The preceding nested-Id and annotated-Boolean-let
fixtures pass unchanged with 304 comparisons each and 164/100 rejection tests.
Eighteen selected prior modules retain identical bytes. Emitted modules, native
results, sizes and SHA-256 hashes are retained.

The full corpus has 648 declarations; this was a focused 34-declaration run.
The last full 259-declaration evidence remains in ../extrema-2026-09-25.
Cached dependencies, the fixed arithmetic archive and unrelated runtime suite
were reused. Annotation support applies within the admitted underlying grammar;
additional Id annotations on arithmetic inputs/instances and comparisons are
separate capabilities to investigate next. Boolean-returning helpers, Boolean
public ABI, mixed Bool/word helper parameters, broader saved-flag propositions
and loops inside helpers remain later capabilities.
