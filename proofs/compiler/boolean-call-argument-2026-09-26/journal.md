# Boolean calls as helper arguments

The Bool-input annotation tests exposed a direct nested call that failed:
`g (f flag)`, with f returning Bool and g returning UInt64. The old application
path used a Boolean environment that represented UInt64-to-Bool predicates only.
It now extracts Bool.toUInt64 of the complete argument using the existing scalar
Boolean conversion path. Step-returning Bool helpers use the same argument path.
Function lookup, typed closure bindings and capture semantics remain checked.

The source application rule describes argument evaluation to flag.toUInt64,
then applies the source Bool function to flag. Source support requires the
converted argument; totality derives its Boolean encoding from the independently
proved booleanConversion_result theorem. This removes the duplicate application
argument semantics and lowering, without adding a binding kind or an unchecked
conversion. Scalar extraction still strictly decreases its source-size measure.

Source execution/support/totality, scalar extraction, loop-step and outer-loop
correctness and invariants passed on their first focused builds. The exact
previously failing nested native shape now passes, with additional examples for
word predicates, choices, bindings, decisions, capture, shadowing, loop updates,
continue and step results. All 180 native/IR comparisons pass.

The raw syntax matrix varies binder annotations, input/result Id layers, argument
values, use/unused declarations, scalar/step/outer scopes and nested calls or
choices. It also checks Bool-to-Bool applications alongside the new word and step
applications. Invalid cases include bad inner arguments, unsupported helpers,
missing captures, function/value confusion and malformed annotations. A final
explicit unused-branch case supplements the first successful matrix.

The unused-branch fixture initially used the extended-local guard structure for
a closed literal condition, which Lean correctly rejected. It now uses the exact
Boolean equality choice syntax for True=True. A matching all-supported choice
is admitted as a control, so the negative test checks the unsupported branch.
The final matrix records 56,832 native/IR comparisons, 48,384 invalid-input checks
and 2,688 controls; its final check passes. The focused prior suite passed
63,666 native/IR comparisons, 33,359 rejection checks and 1,920 controls.

The general compiler theorem and eighteen audits pass. Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1056 declarations.
