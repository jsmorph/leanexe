# Proposition-let proof work

Native elaboration retains a proposition-valued let around equality-to-true but
substitutes its bound value into the standard decision expression. The parser now
preserves the let and reconstructs that evidence with Expr.instantiate1. Source
evaluation uses the original let around each operand, so it preserves lexical
scope without relying on an unproved substitution evaluation rule. A separate
bound-value operand checks unused values, including bodies that are just True
or False. Boolean and word annotations remain distinct.

The initial strict operand-size proposal was false: Expr.sizeOf includes names,
and the Bool.toUInt64 wrapper exceeds a minimal Boolean proposition let. A
checked constant overhead accounts for that wrapper. The ite, dite and decide
headers provably exceed the overhead, keeping all recursive extraction calls
strictly decreasing. The first foundation builds exposed simplifier context and
induction-generalization issues; these were repaired with explicit bounds and
operand generalization. The parser round-trip and soundness proofs then passed.

Guard lowering checks the bound value before compiling the let-wrapped operands.
Its correctness induction generalizes the native operand evaluator, since a
nested let composes that evaluator with the original wrapper. The first lowering
build found a list-membership witness and a dependent-condition abbreviation that
needed to be explicit. Both are repaired; scalar extraction correctness passes.
Loop invariants and focused tests are in progress.

The scalar function, loop-step and loop-exit invariant targets pass. Native
elaboration exposed a distinct remaining form: a junction decision may reduce
unused proposition lets in its type arguments. The original failing fixture and
raw inspection are preserved. This candidate checks exact enclosing arguments;
the unused-value native example instead exercises nested lets at the root. The
next increment will prove the additional type-argument reduction.

All ten native examples pass 180 comparisons. The raw syntax matrix passes
24,192 comparisons, 16,152 rejection checks and 576 controls, including nested
scope, shadowing, standard Id annotations, dependency flags, literal bodies,
ordinary/dependent branches and saved decisions. One initial rejection fixture
used instDecidableTrue on an actually True condition; replacing it with evidence
for a different Boolean operand made the intended negative case valid. Prior
tests pass 78,964 comparisons, 47,817 rejections and 1,792 controls. Full theorem,
axiom and native/V8 checks follow the candidate commit.

The general compiler theorem and eighteen audits pass. Native Lean/V8 agree on 509 inputs across 28 declarations, including thirteen ranges. Eighteen shared modules retain identical bytes. The full native corpus has 1016 declarations.
