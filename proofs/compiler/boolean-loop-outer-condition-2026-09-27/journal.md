# Outer conditions selecting Boolean-result loops

Ordinary if expressions can now choose between two admitted Boolean-result loop
bodies. The result type retains standard Id annotations. The condition is checked
as Bool.toUInt64 of its exact Decidable.decide expression, reusing the source
semantics and evidence checks already proved for scalar expressions. Both arms
are checked, including an arm excluded by a constant condition.

The source choice constructor evaluates only the selected arm. Extraction merges
the five plan fields with the same captured condition. A small shared lemma
proves that this condition stays constant for every accumulator/index/stop/exit
flag store, so the chosen plan's count, initial value, step, exit flag and final
result preserve its source behavior. This reuses the chosen loop's iteration
witnesses and needs no new loop-iteration theorem or WASM lowering.

The first source build required an explicit Bool.toUInt64 call to infer the
condition flag type. After that correction, extraction acceptance/soundness, the
plan-selection lemma, whole-loop correctness and structural invariants pass.
Public extraction and WASM admission also pass.

Ten native fixtures pass 240 comparisons across word and Boolean conditions,
captured predicates, distinct bounds/initial values, nested outer conditions,
break/continue, strides, Id results and captured setup values. Raw syntax tests
pass 16,128 comparisons, 11,520 invalid-input checks and 1,152 wrapper controls.
They cover twelve condition forms, both public parameter orders, four binder
forms, result annotations and loop forms. The raw fixture initially had an
indentation error and used BooleanLocalGuard for closed comparisons and literals;
that descriptor requires an extended Boolean value. Using Step.branch for closed
step comparisons and direct condition/evidence expressions for outer decisions
corrects the fixture. Failed files and logs are retained. Execution comparisons
and invalid-input checks then pass.

Selected preceding Unit-helper, multiple-argument and input-annotation tests are
rerun. The complete compiler proof and native Lean/V8 checks follow this candidate.
Mixed scalar/loop arms, local continuations containing loops, broader helper and
proposition bodies, general loop compositions and full-dialect correctness remain
open. Extend mixed arms next using separately proved zero-iteration plans for
scalar Boolean results.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 609 inputs across 28 declarations, including twenty-three ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1226 declarations.
