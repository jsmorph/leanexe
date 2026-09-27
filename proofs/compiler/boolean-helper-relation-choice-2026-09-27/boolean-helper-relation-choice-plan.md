# Boolean Eq/Ne conditions with general helper scopes

After the propositional-choice gate, the unchanged relation and equality-to-false
probes still reject. Introduce BooleanRelationSelectionSyntax with BooleanType,
optional BooleanProofBranch, unequal flag, raw left/right/yes/no, and the syntactic
nontruth property (equal implies right is not Bool.true). The direct Eq Bool _ true
path is already handled by BooleanSelectionSyntax and stays first.

Exact source condition/evidence use booleanRelationCondition/booleanRelationEvidence.
Recursively convert both operands and both branches. Source evaluation uses native
booleanRelationDecision and evaluates only the selected branch. Reuse
booleanWordChoice 0 and its correctness/invariant theorems. Both branches compile,
even if the comparison outcome is constant. Bound all four children by the full
conditional's raw syntax; no synthetic decision recursion is needed.

Parse exact Eq/Ne heads/universes/Bool type, standard evidence, Bool/Id result
annotations and dependent proof domains/binders. A parts parser can share
booleanRelationSyntax? on the constructed Decidable.decide condition/evidence,
but must prove exact reconstruction and no right-true equality. This is a parser
call, not a recursive scalar call, so it does not have the failed size issue.
Alternatively match Eq/Ne directly and validate evidence with ExprEquality.same.
Use PropositionGuard.not_boolean_equal/unequal to exclude the preceding
BooleanGuardedSelection parser; Boolean-truth exclusion separates BooleanSelected.
Keep BooleanLocal first and add its usual independent syntactic complement.

Tests: Eq/Ne; helpers on left/right/both and either/both branches; right false,
right true for Ne and existing Eq-true path; ordinary/dependent cases; Id types;
negation/wrappers; break/continue/final results; invalid evidence, proof use,
universes, types and inactive branches. Preserve the original probes. After this,
function-typed proposition lets and broader helper bodies/Id inputs remain.
