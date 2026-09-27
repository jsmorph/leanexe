# Boolean helper composition journal

The previous word-loop helper candidate passed the complete proof, nineteen axiom
audits and 609 native Lean/V8 comparisons. Its evidence was pushed as 0f1c9508.

Restoring the saved public Boolean fixtures confirms three failures: nested
captured helpers, repeated calls in a junction, and pure-wrapped compound calls.
The equivalent UInt64 result with conversion after helper declarations succeeds.
The existing helper checker is therefore sufficient; Boolean program composition
needs a scalar terminal case. Adding that case reuses the independent scalar
semantics and its proved compiler, with zero iterations in the shared plan.

The source constructor and totality passed on the first Lean check. An initial
scratch generator split a theorem annotation incorrectly and stopped before
writing the extractor; correcting its anchored split produced the intended edit.
The first extractor check exposed unreduced generic equations in the fallback
lemmas and the expected shifted functional-induction cases. The next check used
the generated source equations. Remaining equation premises needed the same
explicit source-shape unfolding as their conclusions. A sequential text edit also
renumbered repeated contradiction cases twice; a single-pass replacement fixed it.

All extractor acceptance and support proofs, evaluation preservation and IR
invariants now pass. Wrapper equations use the generic defining equation to avoid
unnecessary exclusions from generated equations. The public extractor builds;
a requested WASM target name did not exist, so the complete proof gate will build
the actual public admission modules. The ten native fixtures passed 140 checks.
The raw test initially omitted the literal constructor's negation argument; after
fixing that test syntax, all 17,920 comparisons, 12,160 invalid-input checks and
1,280 controls passed. The unused native fixture now contains an actually unused
helper; it is being rerun with adjacent tests.

The prior Boolean-to-word helper suite passed 209,664 comparisons, 112,896
invalid-input checks and 14,976 controls. The result-binding suite had an explicit
assertion that a scalar Boolean terminal must be rejected by the plan interface.
That expectation conflicts with the intended extension. The preserved failure
is replaced with a stronger positive check: count, initial, step and done must
all be zero, and the plan result must exactly equal the scalar compiler result.
All native/IR comparisons and malformed-input cases remain in that suite.

The complete compiler proof and all nineteen axiom audits passed for candidate
1c7a0e3f. The engine driver built every module and passed admission, exports and
native-result checks, then rejected the new group because its scalar declarations
were absent from the engine's separate scalar allowlist. The new names were added
to that list. No production Lean or fixture changed; the V8 check is rerun against
the already-built modules instead of rebuilding the compiler or proof.

The complete compiler proof and nineteen axiom audits pass. Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1377 declarations.
