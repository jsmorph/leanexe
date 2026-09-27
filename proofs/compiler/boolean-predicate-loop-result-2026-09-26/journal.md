# Direct Boolean helper results across loop scopes

Both helper parameter kinds now use complete converted Boolean bodies in step
and outer-loop declarations. Source totality obtains the native Boolean through
booleanConversion_result; correctness reuses scalar closure matching. Outer-loop
matching preserves captured values under accumulator/index/stop/done changes.
The separately terminating scalar extractor avoids changing either loop measure.
Acceptance, soundness and structural invariants reuse scalar body proofs.
All focused proof modules pass in the first aggregate build.

The first native fixture needed explicit Id.run around two Id Bool conditions
for Lean's Prop coercion. A subsequent admission failure came from Nat.toUInt64,
the elaborated spelling of i.toUInt64, which is outside the current grammar.
The fixture now uses the existing UInt64.ofNat form. Proving Nat.toUInt64 support
is the next increment; the original failures and elaborated expression are kept.

The corrected native examples pass 192 comparisons. Step/outer syntax matrices
pass 24,576 comparisons, 9,216 rejection checks and 1,024 admission controls.
Both parameter kinds, result annotations, negation, pure/run/metadata wrappers,
used/unused bodies, captures and mismatched types or binding kinds are checked.

Prior predicate, scalar-result and loop-bind tests pass 18,580 native/IR comparisons, 11,792 invalid-input checks and 720 admission controls.

The full proof build reached a step invariant module outside the focused target's
imports and found a local name shadowing its scalar-invariant theorem. Renaming
the Boolean syntax variable fixed both helper cases. Focused verification now
includes both step and outer invariant modules explicitly. The failed full-build
log is retained.
The outer invariant also needed a Boolean binding extension rather than the
word-specific extension helper, and removal of obsolete guard proof lines.

The engine driver rejected the native corpus stream because Lean's unused-variable
warning preceded its JSON results. Naming the intentionally unused helper _unused
suppresses that warning and retains the unused-body test. The failed engine and
native-output logs are preserved; compiler and proof code are unchanged.

The general compiler theorem and eighteen audits pass. Native Lean/V8 agree on 521 inputs across 26 declarations, including seventeen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 936 declarations.
