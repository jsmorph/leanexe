# Boolean relations directly under proposition lets

Follow the compound-relation milestone after its gates/archive are complete.
First confirm native elaborated examples: `if (let b := x == y; b = (x == 0)) ...`
and a retained let in `decide`, ordinary/dependent Boolean choices and loop guards.

A bare relation plus the existing guardOperandOverhead cannot cover each converted
operand. That is a conservative proof-bound issue, not a runtime need to change
conversion. The old budget (315) includes True's large syntax although relations
need only Eq/Ne's smaller head. A generalized budget derived from the actual
Bool/Ne conversion heads should be around 560. Prove the exact bound in scratch
before editing production. All guard consumers have syntax beyond the condition:
decide has a sufficiently large head; ite/dite have both the head and a checked
scalar result annotation. A sharper caller lemma can account for that annotation
instead of requiring the whole allowance to fit inside the ite string alone.

Investigate a helper in Extract for parsed scalarResultType? giving a bound from
ResultType.word_size. The dependent/plain scalar parser matches type but currently
does not explicitly name the match equation. Lean may already retain it in the
termination context; use that if possible, otherwise name it. Update only the
two termination branches using guardOperandOverhead, and the BooleanLocal operand
proofs which already have a literal Bool result annotation. Generalize Guard's
letSaved and related CompoundGuard/GuardDecision/GuardCondition fields to the new
leaf; parse with booleanPropositionLeaf?; compile using its checked list callback.
Acceptance, evaluation and choice proofs should then mirror generic letGuard.
Source semantics retains each original let and checks even unused bindings.

This revises the earlier conservative choice to keep the size allowance unchanged.
It must remain a kernel-proved structural decrease at every call site, with no
fuel limits, axioms, synthetic syntax substitution, or parser premises in source
support. If exact bounds do not check, choose another representation; don't assume
it works. Production/test sources stay frozen until the active evidence archive.
