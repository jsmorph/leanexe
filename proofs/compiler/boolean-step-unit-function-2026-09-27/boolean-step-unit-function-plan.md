# Unit-prefixed Boolean step continuations

Preserve the branch-command example with its generated Unit-to-Bool-to-Boolean-
step continuation. Direct and environment compilation reject it. Six additional
native probes cover Unit, PUnit, retained Id annotations, captures, nested calls
and unused bodies. Run them before making changes.

Add a distinct unitBooleanFunction kind, indexed by UnitSyntax, to Boolean-step
source values and IR bindings. Its result contains both the flag and done/yield
state. Keep the Unit and PUnit domains distinct at typed lookup. Extend totality,
matching and IR invariants, including scalar projections that retain the binding
position without exposing the function as a scalar value.

In Source/ScalarBooleanStep, define an exact helper shape with both unit and
Boolean type/value binders, input BooleanType, output step BooleanType, body,
continuation and nondependency bit. Source evaluation binds the Boolean argument
at index zero and unit at index one. Support validates the helper body even when
unused. Calls initially accept the exact Unit.unit/PUnit.unit constructor
matching the function kind, with an independently checked Boolean argument.

In Extract/ScalarBooleanStep, recognize matching unit type/lambda domains,
matching Bool/Id Bool type/lambda domains and Boolean step outputs. Prove parser
acceptance, soundness and size bounds. Try the helper after the existing function
paths and binary predicate recognizer reject. Compile the body with zero/Unit
placeholders for admission, then close over the current environment. Add an exact
two-argument call case before unary calls. Prove the two extraction equations,
evaluation correctness, complete admission, source reconstruction and IR invariants.

Test native generated and explicit continuations; both unit spellings, Id layers,
captures, early exit, unused bodies, empty ranges, domain mismatches, wrong function
kind, missing/extra arguments, unsupported arguments and invalid unused bodies.
Register native/V8 fixtures. Run focused prior tests, complete source-to-WASM proof
and axiom gates, archive logs and hashes, update task.md and push before advancing.
Binary Boolean helpers around complete word-result loops remain a later increment;
their six native probes are kept separately.
