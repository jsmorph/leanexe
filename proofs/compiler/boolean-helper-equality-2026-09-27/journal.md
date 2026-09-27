# Equality and inequality around Boolean helper scopes

All ten new native declarations elaborate and fail extraction before this change.
The independent BooleanRelationSyntax preserves exact standard BEq/bne syntax
or a decision of Boolean Eq/Ne, including its evidence. BooleanRelated adds the
syntactic complement of BooleanLocal. The parser checks heads, universes, Boolean
types, the default comparison instance, and structural identity of decision
evidence. It proves acceptance, soundness, non-overlap and both strict child-size
bounds. The parser and scalar proofs pass on their first checks.

Source evaluation recursively evaluates both operands' Boolean conversions and
uses native equality/inequality or decide. Extraction reuses booleanWordEquality 0
and its existing execution/invariant theorems. The existing scope condition and
step proofs need no changes. Tests vary operands on the left/right/both, all four
comparison forms, captures, wrappers, negation, helper result annotations, unused
helpers, dependent conditions and loop exits. Reflexive comparisons still check
both operands. Invalid comparison instances, evidence, universes, domains and
word operands are explicitly tested.

The registration script initially used the previous family's Word suffix for the
junction anchor; that lookup failed before writing any file. Using the actual
Left anchor registered all ten declarations. The selected engine group retains
44 prior declarations and adds ten new ones, with 25 range declarations.

The public proof build passes 190 targets. The original ten probes pass unchanged.
New tests pass 37,812 comparisons, 45,312 invalid-input checks and 768 controls.
Six adjacent tests pass 34,868 comparisons, 29,824 invalid-input checks and 896
controls. The broader composite probe now admits equality; choices, nested
helper bodies and Id inputs remain rejected. No proof or test diagnostic required
a production correction in this increment.

The general compiler proof and nineteen axiom audits pass (3371 build targets). Passed 993 native Lean / independent Wasm engine comparisons across 54 declarations.
44 prior modules retain identical bytes; 0 changed. The full native corpus contains 1457 declarations.
