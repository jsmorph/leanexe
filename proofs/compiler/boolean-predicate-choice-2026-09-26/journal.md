# Boolean-valued choices containing Boolean-input predicate calls

The initial design compiled a newly constructed Boolean decision for the whole
condition. Its recursive size bound is false: kernel reduction gives size 3387
for the smallest original choice and 4173 for the constructed decision. #eval
cannot execute Lean.Expr's kernel size instance, so #reduce supplied these
values. These failed proofs and reductions are retained. The compiler's measure
is unchanged. The adopted design compiles the four actual Boolean children of
the existing choice syntax; their size bounds pass, including proof-lambda
lifting for dependent branches.

A source form preserves ordinary versus dependent choice syntax and the exact
proof-binder names/annotations. The new source rule evaluates both condition
operands and only the selected branch. Source support and extraction check both
branches. The shared result uses the proved encoded-word comparison, conditional
execution and negation. The initial helper proof needed simp only to keep its
whole Boolean decision available for the branch equality; that local correction
passed. The aggregate extraction proof passed on its first attempt.

The retained Id-result example needed an explicit Bool equality condition because
Lean does not coerce Id (Id Bool) directly to a proposition. Giving Bool explicitly
to Eq and Bool.toUInt64 preserves the intended conditional source form. No source
or compiler behavior was changed to accommodate the example.

Examples cover direct Bool conditions, Eq/Ne conditions, ordinary/dependent
branches, nested choices, calls in arguments and helper bodies, captures, Id
computations, loop bounds, break/continue and final values. Twelve controls and
108 extra tests check both active/inactive invalid branches and proof-binder use.
Focused tests pass 16,052 native/IR comparisons and 11,628 invalid-input checks.
Prior tests pass 16,660 comparisons and 11,694 invalid-input checks, with twelve
admission controls in each group. The independent engine group contains 32 new
and relevant prior declarations; its eighteen shared modules will be compared
with the equality archive. The full theorem, audits and engine gate are next.

The general compiler theorem and all eighteen axiom audits pass. Native Lean/V8
agree on 575 inputs across 32 selected declarations, including 14 ranges. All
eighteen modules shared with the equality archive retain identical bytes. The
full native corpus contains 844 declarations.
