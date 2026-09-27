# Outer UInt64-result conditionals

The preceding Boolean-to-word helper increment passed the full source-to-WASM proof, nineteen axiom audits, and 609 native/WASM comparisons, with eighteen prior modules byte-identical. This increment adds a general WordRange layer while retaining that proved component and the original scalar/range/Boolean-result dispatch priorities.

The source language independently admits pure expressions, existing word loops, Boolean-to-word loops, word-result choices and exact standard Id/metadata wrappers. Source evaluation follows the selected arm; support and extraction check both arms. The new extractor tries the three proved components before recursively compiling choices. Pure arms use zero-iteration plans. The existing plan choice theorem proves stable captured conditions select the same branch throughout loop execution.

Source totality and initial extraction passed. Initial acceptance proofs used the function equation name, which selected a source-specific generated equation and introduced impossible disjointness obligations for arbitrary component source. Rewriting with the complete eq_def equation preserves all earlier component alternatives and fixes this without restricting the language. The failed acceptance log is retained. Acceptance, support recovery, preservation, invariant inheritance and public admission then passed.

Ten native examples pass 240 comparisons. They cover two loops, scalar/loop mixtures, nested conditions, Boolean-derived word branches, early exit, continue, strides, helper declarations inside branches and Id wrappers. Raw syntax tests pass 258,048 native/public/direct-plan comparisons, 129,024 invalid-input tests and 9,216 wrapper controls. Conditions include all eight admitted word comparisons, Boolean truth/negation and constant true/false. Both argument orders, all binder kinds, zero/two Id result layers, overflow values, regular/early-exit/continue steps, and word versus Boolean-derived loop branches are covered. Invalid unselected branches, custom evidence/heads, wrong universes and wrong scalar kinds are rejected.

Setup and helper declarations outside a loop-containing word conditional, composition of loops, broader helper/proposition bodies and full-dialect compiler correctness remain open. Each path still executes at most one dynamic loop.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1347 declarations.
