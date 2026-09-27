# Monadic bindings around general Boolean scopes

Preserve the six native bind probes before implementing admission. Extend the
ordinary BooleanScopeBinding syntax with a separate standard Id bind form that
retains the continuation binder information and exact Boolean result annotation.
The form must render the complete standard Bind instance, exact universe levels,
input type, bound value and continuation. Keep ordinary let syntax unchanged.

Reuse the existing PublicArgument.Domain certificate for UInt64 or Bool inputs
under standard Id layers. Require the continuation lambda domain to equal the
declared bind input type. Check the Boolean output annotation and all bound values
and bodies, including unused values. Reject altered/custom instances, universes,
unsupported domains and wrong lambda annotations.

The current source evaluation/support rules, extractor body, IR invariants and
WASM backend should apply to either checked form. Prove new syntax recognition,
exclusion from earlier dispatch paths and recursive size bounds before rebuilding
those general proofs. Avoid admitting unrelated application or named-call forms
in this increment.

Complete fixed native probes, nested and conditional binds, malformed syntax
checks, the complete source-to-WASM theorem, and selected independent V8 execution.
Update task.md, archive verified source/module hashes, commit and push, then
continue compiler coverage.
