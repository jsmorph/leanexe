# Boolean-valued choices with general helper scopes

The original choice probe is still rejected after equality support. Admit
ordinary/dependent Boolean-valued conditionals whose condition tests a Boolean
against true, including helpers in the condition, either branch or all three.
Preserve standard Eq evidence, the result's Bool/Id annotations and dependent
proof binder names/annotations. Use the existing checked proof-binder lift/drop
functions. Both branches must compile; source evaluation selects one.

Introduce an independent BooleanSelectionSyntax and its complement of
BooleanLocal. Prove parser acceptance/soundness, all child-size bounds and
non-overlap. Recursively compile the condition and both Boolean conversions,
then reuse the existing wordGuard and IR conditional proofs. Check scalar,
dependent and loop-step cases, including inactive unsupported branches and
incorrect proof domains. Propositional conditions beyond Boolean truth remain
a separate capability. Finish the general source-to-WASM theorem and independent
engine checks before continuing to those conditions or broader helper bodies.
