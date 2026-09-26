# Compound decision proof journal

`GuardDecision` describes standard decision evidence independently of extraction.
Comparison leaves use the proved arithmetic reannotation relation. Junctions
retain their actual standard instance, both original propositions, both child
decisions, and any enclosing negations. Propositional literals and Boolean
compound subguards retain canonical evidence.

The checked recognizer locates candidate child decisions and checks the entire
reconstructed enclosing expression. Soundness and acceptance are proved by
induction over the source guard or evidence witness. A canonical-witness theorem
retains every existing guard form.

`ReannotatedGuard` pairs a source guard tree with its checked noncanonical
decision syntax. Ordinary compound admission first checks canonical evidence and
then checks this relation. Both forms lower the original guard tree through the
same compiler. Boolean-local guard exclusion uses the proved absence of a closed
guard, which excludes both admission paths.

The first source proof needed explicit unfolding of `Guard.evidence`. The
integration acceptance proof initially left dependent record inequalities opaque;
a local copy of the inequality allowed simplification without changing the
record. The failed proof diagnostics are preserved. A 60-second aggregate source
build reached its limit while rebuilding dependencies. The remaining step
acceptance/correctness modules were built separately before finishing the
function target and running tests.

Focused tests compare six native scalar examples and two range examples, plus
constructed guard trees containing literal and Boolean subguards. Invalid tests
check swapped child propositions, swapped decision expressions, wrong connective
instances, custom child decisions and whole-evidence metadata. Previous atomic
annotation tests are rerun to check their admission and rejection boundaries.

This increment concerns ordinary scalar and loop-step guards. Differently
annotated decision operands in dependent branches and saved decisions remain
subsequent work. Full LeanExe dialect compiler correctness remains unfinished.
