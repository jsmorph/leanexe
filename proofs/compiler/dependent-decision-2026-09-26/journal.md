# Dependent conditional decision proof journal

Dependent scalar and loop-step guards now retain a `DecidedGuard`: the original
guard tree, original decision expression, and independent `GuardDecision`
witness. The source guard shape remains the input to the existing guard lowering.
A coercion from the checked record to its tree lets the existing semantic proofs
use exactly that shape; no compiler-result premise is added to source evaluation.

The recognizer first checks standard decision evidence, including proved
equivalent arithmetic operands, and then checks the two proof-lambda domains
exactly. Source branch evaluation and typing still add the erased proof binder
to their lexical contexts. The original canonical syntax helper remains an
abbreviation through a canonical witness.

The recognizer, scalar extraction proof, step acceptance/correctness proofs, and
source reannotation evaluation theorem all checked without proof repair beyond
the changed guard type and syntax helper. Targeted builds preceded the general
compiler gate. New native examples cover atomic and compound conditions,
nested proof binders, helper captures, Id actions and range exits.

Constructed syntax tests keep both proof binders in place and select variables
outside those binders, exercising de Bruijn scope preservation. Invalid tests
reject mismatched decision expressions, swapped propositions and child evidence,
wrong standard connective instances, custom decisions, and incorrect proof-lambda
domains. The preceding dependent-if and compound syntax fixtures are rerun.

Saved `decide` values and Boolean-result proposition choices still require exact
condition/decision operands; extending their checked guard representation is next.
Full LeanExe dialect compiler correctness remains unfinished.
