# Boolean wrappers around inner helper scopes

The original probe now accepts direct helper conditions but still rejects its
Id.run form. Five additional unchanged probes reject Id.run, pure, nested
wrappers, direct conditions and loop exits. This establishes the missing wrapper
path independently of the implementation.

BooleanWrapped describes a BooleanWrapper and a raw body outside BooleanLocal's
syntax. The independent source rule evaluates the body as a Boolean conversion
and applies BooleanWrapper.denote, whose identity law is already proved against
native Id.run/pure semantics. The parser checks exact standard wrapper heads,
universes, result annotations and canonical pure instances. Metadata is retained
as its own wrapper. The converter recursively checks the unwrapped body, after
the existing local-expression and helper parsers reject the outer syntax.

Parser acceptance required splitting the dependent match and identifying its
returned wrapper/body pair with the accepts theorem. Direct rewriting failed
because the result carries a source-exclusion proof. The helper non-overlap
lemma first eliminates the known failed BooleanLocal test, then cases on the
wrapper. Unfolding the expression before that elimination had left a mismatched
Decidable instance under the simplifier's transparency setting. Both diagnostic
failures are retained. The final source totality, parser, scalar acceptance,
correctness and IR-invariant proofs pass without new axioms.

The existing BooleanScopeGuard and loop-step proofs require no changes. Their
condition semantics already use the recursively checked Boolean conversion.
Native fixtures and raw tests cover word/Boolean helper inputs, captures,
discarded helpers, result Id layers, nested wrapper chains, conditions and loop
exits. Invalid wrapper types, universes, instances, bodies, decisions and proof
domains remain rejection cases.

The general compiler proof and nineteen axiom audits pass (3365 build targets). Passed 993 native Lean / independent Wasm engine comparisons across 54 declarations.
44 prior modules retain identical bytes; 0 changed. The full native corpus contains 1427 declarations.
