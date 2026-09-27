# Public Boolean results

The public signature now records whether its result is UInt64 or Bool. All
parameters remain UInt64. Boolean bodies compile through Bool.toUInt64; word
bodies retain existing scalar/range/early-exit paths. A Boolean signature cannot
enter the range fallbacks. Exact signature syntax and metadata remain checked.

The independent source contract now includes the result kind and body encoding.
A new Boolean application terminal requires evaluation to flag.toUInt64, and
collection lemmas retain the original elaborated lambda term. The explicit
extractScalarFunc_boolean_correct theorem proves a source flag and matching IR
result for every argument list of the declared arity. It joins the axiom audit.

Source application, extraction cases/acceptance/correctness and result encoding
passed their first focused builds. The emitted-instruction, body-byte and module
function-validation proofs retain their scalar/range structure; pure bodies use
the selected result encoding and range cases prove a word result. All three
focused WASM proof targets pass. Native fixtures pass 140 comparisons, covering
literals, arithmetic comparisons, choices, decisions, word/Boolean lets, do
bindings, immediate/captured helpers and wrappers.

The syntax matrix passes 16,512 native/IR comparisons, 7,872 invalid-input checks
and 768 controls. It covers arities zero through three, all binder infos, type
and value metadata, negation, junctions and lexical bindings. Each public Bool
function produces exactly the same IR as its explicit UInt64 conversion.
Unsupported result types, wrong argument kinds, invalid or incomplete bodies,
free variables and extra/missing lambda binders are rejected. Public Bool inputs,
Id result annotations and Boolean loop results remain later capabilities.

The focused prior suite passes 120,678 native/IR comparisons, 81,743 rejection
checks and 4,608 controls across fourteen files. This includes the preceding
nested-helper argument capability and its annotation/type checks. The public
error message and README now describe Boolean results; the detailed grammar
states the current result and parameter restrictions.

The general compiler theorem and nineteen audits pass. Native Lean/V8 agree on 469 inputs across 28 declarations, including nine ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1066 declarations.
