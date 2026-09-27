# Boolean-valued choices with helper scopes

Ten valid native probes fail extraction before this extension. BooleanSelectionSyntax
preserves the result's Bool/Id annotation, the Boolean truth condition, standard
evidence and optional dependent proof binder names/annotations. BooleanSelected
records the syntactic complement of BooleanLocal. Its parser uses the existing
checked proof-binder drop/lift functions, proves exact reconstruction and all
child-size bounds, and excludes preceding helper/wrapper/operation shapes.

The parser and source/scalar proofs pass on their first checks. One redundant
simp argument in the new parser was removed after its linter diagnostic. Source
evaluation first obtains the Boolean condition and then evaluates the selected
branch. The support rule checks both branches. The existing wordGuard and IR
conditional rules prove execution and preserve invariants, including loop-step
value and exit projections through the established Boolean scope conversion.

Tests place helpers in the condition, true branch, false branch or all three,
with word/Boolean inputs, Id result annotations, wrappers, ordinary/dependent
branches, unused helpers and break/continue. Invalid inactive branches, operands,
result annotations, decisions and proof domains are checked. Tests also reject
proof binders used as Boolean values. The engine group retains 44 previous
cases and adds ten, keeping 25 range declarations.

The public build passes 192 targets and all ten original probes now pass.
New tests pass 25,268 comparisons, 34,048 invalid-input checks and 512 controls.
Six adjacent tests pass 53,684 comparisons, 56,320 invalid-input checks and 1,280
controls. The composite probe now admits choices; nested helper bodies and Id
inputs remain rejected. Additional propositional probes reject word comparisons,
Boolean relations/equality to false and compound propositions. Two simpler
negation/proposition-let probes already pass; retain them as positive controls
when measuring the next capability.

The general compiler proof and nineteen axiom audits pass (3373 build targets). Passed 993 native Lean / independent Wasm engine comparisons across 54 declarations.
44 prior modules retain identical bytes; 0 changed. The full native corpus contains 1467 declarations.
