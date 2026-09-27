# Boolean-result prefixes in loop sequences

Preserve fixed probes for Boolean-to-word, Boolean-to-Boolean, dependent bounds,
exits/continue, unused Boolean results and alternating result kinds. Add Boolean
prefix rules to both existing sequence grammars. The bound Boolean computation
uses the independent single-loop BooleanRange grammar. Continuations may be any
supported word or Boolean sequence, so arbitrary chains of such prefixes compose.
A bound Boolean expression containing its own multi-loop sequence remains a
separate extension.

Reuse the same sequence plans and WASM proofs. Add a captured Boolean local
matching lemma, exact Boolean let/bind annotation checks, source totality,
complete admission, source reconstruction, correctness and bounded-read proofs.
Keep old word-prefix dispatch first. Validate zero/one encoding through public
Boolean correctness and old scalar binding proofs. Finish focused native/IR,
malformed-input, complete compiler-proof and V8 checks before further coverage.
