# General Boolean bodies inside converted local helpers

The fixed native probes reject nested and wrapped helper bodies, including an
unused nested helper. The source rules and scalar compiler already recursively
validate and evaluate the Boolean conversion of each body. Their proofs do not
need the body to belong to the smaller BooleanLocal syntax family. The parser
imposed that restriction before the recursive check could run.

BooleanHelper now retains the raw Lean expression for its body. The parser keeps
its exact domain, result, lambda and let annotations, along with the existing
exclusion of the earlier BooleanLocal parser. The compiler validates the body
at a zero input before creating the closure, then checks each application with
its supplied argument. The same source, acceptance, correctness, totality and
invariant proof arguments now refer to the raw body. Unsupported bodies remain
rejected even when the continuation does not use the helper.

The ordinary word-continuation helper parser and Id input domains are separate
recorded gaps; this capability changes only helpers inside Boolean conversions.

The focused source/parser target passes (65 build targets). The source, scalar
compiler, acceptance, support and invariant target also passes on its first run
(137 targets). No proof redesign was required: each body already had a recursive
Boolean conversion argument. The public compiler dependencies are next.

The next ordinary word-continuation path is recorded separately. Its source
rules also use recursive Boolean conversion, but retain a BooleanLocal body
parameter and matching parser check. Broadening the converted path alone does
not claim those lets or Id input domains.

The public compiler target passes (196 targets). The three original converted
helper probes now pass unchanged; the ordinary proposition-let and Id-input
probes remain rejected. All ten native declarations pass 180 comparisons. Raw
scalar tests pass 16,128 comparisons and 19,584 invalid-input checks; step tests
pass 21,504 comparisons and 14,208 invalid-input checks. Each syntax file checks
384 parser controls. All tests passed on their first run; final runs add exact
count assertions.

Prior tests pass 76,252 comparisons, 77,744 invalid-input checks and 640 controls.

The general compiler proof and nineteen axiom audits pass (3377 build targets). Passed 993 native Lean / independent Wasm engine comparisons across 54 declarations.
44 prior modules retain identical bytes; 0 changed. The full native corpus contains 1507 declarations. Prior tests pass 76252 comparisons, 77744 invalid-input checks and 640 controls.
