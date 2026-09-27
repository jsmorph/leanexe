# Saved local Boolean loop-call results

BooleanCall now retains a saved-result let whose body returns exactly its new
variable. The value is parsed in the original helper scope, so captured arguments
need no additional shifting. The result annotation must be Bool or standard Id
Bool, and the original name and nondependent flag are retained. Standard wrappers
and repeated saved-result lets can surround direct or forwarded calls.

The parser's source-size proof handles a smaller let value as well as existing
wrapper bodies. Acceptance and ordinary well-founded soundness gain the exact
saved-result case. Both proofs pass on their first build. Existing source
application, extraction and loop-plan proofs reuse the call shape.

The native fixtures restore the forwarded-call show failure with unique names.
Raw tests add nested saved results, name shadowing and both let flags to the
existing wrapper cases. They reject wrong returned variables, wrong Boolean/Id
types, unsupported saved values and invalid applications of the saved result.

Public extraction and WASM admission proofs pass on their first build. All ten
restored native show fixtures pass 240 comparisons. Raw tests pass 96,768
native/IR comparisons, 76,032 invalid-input checks and 3,456 equivalent-binding
controls. Both public and direct range extraction preserve nested saved-result
wrappers, including shadowed names and both let flags. No implementation or proof
revision was needed for this capability after its initial patch.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1286 declarations.
