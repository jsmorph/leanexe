# Local predicate function bindings inside propositions

The fixed compound probe elaborates with a UInt64-to-Bool let inside the And
proposition. The existing guard let parser recognizes only word and Boolean value
bindings, so it rejected the condition before checking either branch. The helper
and the substituted decision evidence are preserved exactly.

GuardLetType now retains bare UInt64/Bool predicate inputs, the forall binder and
all admitted Bool/Id result annotations. Each predicate contributes a checked
scalar operand: its original let wrapped around canonical UInt64 zero. This
validates even an unused helper body. Each actual guard operand keeps the same
let wrapper, so helper captures retain their lexical meaning. The existing guard
semantics and compiler proofs apply unchanged.

The validation operand needs an overhead of 615 instead of 557. Kernel-checked
constant inequalities establish this allowance and retain every existing ite,
dite and decide bound. The global extraction measure is unchanged. The focused
source and parser proofs passed on their first run (19 build targets).

The first public compiler dependency build reached its 180-second limit after
187 of 191 scheduled targets. It reported no failed proof. Following the runner
instructions, the remaining word-range and public targets are checked separately
instead of rerunning the unchanged aggregate target.

The separate word-range target and the public compiler target passed. All eight
original probes now pass unchanged: the compound condition was restored and the
other seven retained their behavior. Native tests pass 180 comparisons. Combined
scalar/step syntax tests pass 72,576 comparisons, 75,568 invalid-input checks and
576 controls. Both native and syntax tests passed on their first runs; a final
syntax run adds and verifies exact count assertions.

The adjacent tests pass 118,452 comparisons, 106,392 invalid-input checks and
1,920 controls. A next-capability probe initially had a Lean indentation error
in its proposition-let example; that input is retained separately and corrected
before recording admission results. No compiler change was made for it.

The general compiler proof and nineteen axiom audits pass (3377 build targets). Passed 993 native Lean / independent Wasm engine comparisons across 54 declarations.
44 prior modules retain identical bytes; 0 changed. The full native corpus contains 1497 declarations. Prior tests pass 118452 comparisons, 106392 invalid-input checks and 1920 controls.
