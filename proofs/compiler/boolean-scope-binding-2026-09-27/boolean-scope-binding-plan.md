# Scalar bindings around general Boolean scopes

Six fixed probes reject after the Id helper-input capability: word and Bool lets,
retained Id annotations on those bindings, an unused word let, and nested word/Bool
lets. The original Id-input capture probe remains unchanged; a corresponding bare
input program also rejects, locating the gap in the surrounding binding.

Add a source-only syntax certificate for an ordinary scalar let whose continuation
is a general Boolean expression. Keep the exact annotation, name and nondep flag.
Reuse PublicArgument.Domain to distinguish UInt64 and Bool with standard Id layers.
Require exclusion from the existing BooleanLocal grammar so admitted direct cases
keep their current path. Bound values and continuations are both checked, including
unused values. Preserve lexical positions and nested captures.

Extend source evaluation and support with word- and Boolean-binding cases. Compile
the bound value recursively (converting a Bool value to its word encoding), then
compile the converted body with the corresponding lexical binding. Prove source
totality, reconstruction, acceptance, evaluation and IR invariants. Keep the new
parser after existing Boolean helper/wrapper/selection paths where possible to
minimize changes to established equations, while proving its necessary exclusions.

Test the fixed probes, exact annotation/universe/variable rejection, nesting,
captures, unused bindings and scalar/loop scopes. Finish the complete source-to-WASM
proof gate and focused native/V8 comparisons, archive source/module hashes and
push before widening to monadic or applied binding forms.
