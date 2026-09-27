# Monadic scalar bindings around general Boolean scopes

The six fixed source probes all reject before this change. A separate binding
form retains the standard Id bind call, input domain, exact continuation binder
and Boolean result annotation. The source binding evaluation and support rules
already express the needed semantics for either form. The native standard Id
bind equation is proved by reduction and has a dedicated zero-axiom audit.

Recognition, exact reconstruction, acceptance, kind exclusion, dispatch exclusion
and recursive size bounds pass 84 targets. Two attempts at the other-kind parser
proof left a proof-dependent result-type match unreduced. Explicitly splitting
that remaining match proves both branches. The scalar expression integration
passes 140 targets without changing its evaluation, acceptance, reconstruction
or IR invariant proofs. Both bound values and continuations remain checked.

The source definition of the form excludes applied-lambda and named-call forms.
Those forms remain separate coverage work. Three new audits check native Id bind
behavior and both directions of the exact binding recognizer.

Loop integration was built in two bounded dependency groups, with 195 targets
through Boolean word ranges and 207 through scalar functions. Both pass. All six
fixed source probes compile. Ten native fixtures pass 180 native/IR comparisons.
The syntax matrix initially used the reserved keyword `instance` as a local name;
renaming it fixes parsing. It passes 16128 comparisons, 31104 invalid-input checks
and 384 admission controls. The checks cover exact monad/instance/universe/type
annotations, result types, lambda domains, unsupported bound values and bodies,
and used/unused values. The same fixtures are registered for strict compiler and
independent V8 checks.

The complete source-to-WASM gate passes 3393 targets and all 32 audits. Passed 1389 native Lean / independent Wasm engine comparisons across 73 declarations.
63 prior modules retain identical bytes; 0 changed. All six fixed monadic scope probes compile. Prior tests pass 62580 comparisons, 73152 invalid-input checks and 1152 admission controls. Six fixed applied-binding probes reject and define the next increment.
