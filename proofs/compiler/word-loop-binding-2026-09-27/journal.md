# Bindings around word-result conditional loops

The conditional increment passed the complete source-to-WASM proof, nineteen axiom audits and 609 native/WASM comparisons, with eighteen prior modules byte-identical. This increment extends WordRange with pure word/Boolean setup, exact standard Id binds and saved word computation results followed by pure tails.

The existing scalar/range/Boolean-to-word component priorities remain unchanged. New Bool prefixes check the value through Bool.toUInt64 and extend the typed environment. Word bindings use the shared scalar-first/loop-value binding combinator. A source value may contain a conditional loop only when its tail is pure; two-loop computations remain rejected.

The source constructors and totality proof were adapted from the already proved Boolean-to-word bindings. Acceptance keeps any successful earlier component and otherwise uses the new binding case. Functional induction now varies locals; the preservation proof generalizes native values so captures are checked against every fresh loop store. Source totality, acceptance, support recovery, preservation, invariants and public WASM admission all passed on the first applied check.

All ten native examples pass 240 comparisons, including mixed setup, standard do binds, nested conditions, saved results, show, early exit, continue, strides and nested Id annotations. Syntax tests pass 129,024 native/public/direct-plan comparisons, 73,728 invalid-input checks and 6,144 controls. They compare ordinary lets with Id binds and unsaved computations, check invalid unused values and wrong scalar kinds, verify exact domains/instances/universes, and reject both ordinary and monadic sequential loops. All focused tests passed on their first execution.

Local helper declarations outside word conditionals, multiple loops, broader helper/proposition bodies and full-dialect correctness remain open.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1357 declarations.
