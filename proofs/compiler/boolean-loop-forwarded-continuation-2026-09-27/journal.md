# Standard Id binds forwarding to local loop functions

BooleanCall is indexed by the helper input kind. Word and Boolean forwarding
constructors preserve the exact input/output Id annotations and lambda binder.
Their syntax binds the action and calls the existing helper at index one with
the newly bound argument at index zero. The action cannot capture the helper
itself; binder removal preserves its outer references. Standard wrappers around
the whole bind remain supported.

The parser checks the exact standard Id bind instance, input/domain agreement,
Boolean output and argument kind. The existing source application proof then
uses the checked action as the local function's argument. Source totality and
the scalar helper priority remain unchanged.

The first source build passes. Lean's generated functional induction principle
fails for the parser's dependent Boolean-kind match. Soundness now uses ordinary
well-founded induction on source expression size, as used elsewhere in extraction.
The direct acceptance case lets Lean infer the indexed constructor's Boolean kind.

The well-founded soundness proof passes. Extraction acceptance/support,
correctness, invariants, public compilation and WASM admission all build. The
recursive loop extractor and its induction cases did not need structural changes.
Tests now exercise direct and nested forwarding for both argument kinds, captured
helpers, break/continue, stride and repeated Id annotations. Raw tests also cover
wrappers around the bind and malformed forwarding callbacks, domains and instances.

The raw tests pass on their first run: 32,256 native/IR comparisons, 23,040
invalid-input checks and 1,152 equivalent-binding controls. The first native
fixture used `show Id Bool from do`, which Lean elaborates as an extra `let this :=
ACTION; this` around the action. That separate saved-result form remains outside
the current call grammar; the failed source and complete diagnostic are retained.
Using `Id.run do` keeps the exact monadic forwarding computation under an already
proved wrapper. All ten cases then pass 240 native/IR comparisons. The saved-result
form stays on the coverage list after conditional forwarding.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1266 declarations.
