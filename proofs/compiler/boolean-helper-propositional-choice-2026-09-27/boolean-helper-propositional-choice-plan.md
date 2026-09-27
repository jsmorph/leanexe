# General propositional conditions for Boolean choices

After finishing the Boolean-truth conditional milestone, probe Eq/Ne Boolean
relations (including equality to false), word comparisons, compound propositions,
negation and proposition lets with general helper scopes in either branch.

A source shape can preserve raw condition and evidence and recursively evaluate
Bool.toUInt64 (Decidable.decide condition evidence) to obtain the native decision.
That reuses the already checked Boolean relation/guard parser and evaluation
rules rather than adding a second interpretation of evidence. Branches use the
same recursive Boolean conversion. Preserve result Bool/Id types and dependent
proof lift/drop as in BooleanSelectionSyntax. Prove the wrapped decision is
strictly smaller than the complete conditional, accounting for the constant-name
size overhead explicitly if needed.

Keep the existing Boolean truth path first. A syntactic non-truth condition
property (condition differs from Eq Bool value true for every value) can make the
new general source family disjoint. Exclude BooleanLocal as usual. The parser
preserves exact raw condition/evidence; recursively compiling the wrapped decision
must validate that evidence before either branch is admitted. Do not claim the
raw shape parser independently validates evidence if that is delegated to the
checked recursive conversion. This should handle general supported propositions
without duplicating Guard semantics. Confirm with measured probes before editing.

The wrapped-decision approach fails the current termination measure: kernel
reduction gives size 1560 for the smallest constructed decide expression versus
774 for the corresponding bare Boolean conditional (the Bool type alone has
size 420). The initial #eval could not execute Lean.Expr's sizeOf instance; the
preserved #reduce run supplies the actual counterexample. Do not try to prove
that false size inequality or change the global extraction measure for this step.

Reuse PropositionGuard and extractGuard directly instead. They already carry
native proposition semantics and checked evidence, plus operand size bounds
with guardOperandOverhead_ite/dite. Introduce BooleanGuardedSelectionSyntax with
type, optional proof shape, PropositionGuard and raw yes/no branches. The existing
guard operand induction and booleanWordConditional_correct/holds prove the
condition. Its non-Boolean condition theorem separates it from the truth-choice
parser. This covers supported word comparisons, compound propositions, negation
and proposition lets. Direct Boolean Eq/Ne conditions remain a separate next
capability. The extended probe adds repeated-call bodies to the two previously
positive cases: these now reject, while the original positive controls stay put.
