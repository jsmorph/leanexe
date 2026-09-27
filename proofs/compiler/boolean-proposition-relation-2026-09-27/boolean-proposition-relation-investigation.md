# Next saved Boolean proposition gap

The saved publicFlagsDecision fixture was changed from
`pure (pure (decide (left = right ∨ ¬ left)))` to plain equality in the original
public Boolean parameter work. Restore the original compound form under a fresh
name and probe it after the current wrapped-helper gates finish.

Current architecture:
- BooleanLocal parses direct Boolean equality/inequality and truth guards.
- PropositionGuard depends on the closed Guard tree, before BooleanLocal exists.
- Guard joins recognize closed children, then SavedBooleanGuard leaves for
  Boolean expressions beyond closed comparisons.
- SavedBooleanGuard is currently a truth proposition only: `value = true`.
  Its single scalar operand is Bool.toUInt64 value; lowering tests that operand
  against one. This covers captures and helper calls through recursive scalar
  extraction but cannot represent `left = right` as a leaf in a compound guard.
- Direct BooleanLocalGuard proofs intentionally establish that those standalone
  Eq/Ne conditions are absent from guardOperands?. Adding general Boolean Eq
  directly to guardOperands? would invalidate those disjointness proofs.

Possible bounded extension (not implemented): introduce a local proposition leaf
that contains either the existing saved truth guard or a Boolean Eq/Ne relation.
A relation has two scalar operands, Bool.toUInt64 left and Bool.toUInt64 right,
and lowers to word equality/inequality. Keep the existing standalone guard parser
priority; use the new leaf only at the same compound/not/let fallback positions.
Generalize saved-left/right/both and saved-let/negation to this leaf with a checked
lowering helper, preserving old source constructors via coercion if practical.
The source grammar must retain exact Eq/Ne conditions and evidence. Exclude Eq
with literal true on the right from the relation form so it keeps the existing
truth route. Check both operands recursively as Boolean conversions.

Before implementing, prove size bounds for both converted operands against the
original relation condition plus guardOperandOverhead. That overhead is small
(see Source/ScalarGuardLet.lean), so do not assume it can absorb an expanded
BEq/Decidable expression. Using two operands avoids duplication of raw source and
evidence. Review GuardDecision, GuardCondition and savedBooleanGuard_not_guard
before choosing the final representation. Do not introduce a parser premise into
independent source support or claim the full compiler is proved.

The baseline probe confirms both the saved nested-Id decision and a UInt64
conditional using `left ≠ right ∧ left` are rejected. The first size-bound proof
left sizes of constant strings opaque to omega. It is being sharpened with a
small closed arithmetic fact about those string sizes; this is a proof issue,
not evidence that the proposed bound is false. The current probe is in
boolean-proposition-relation-probe.lean and must wait until the running WASM
execution gate releases the serial Lean lock.

A concrete representation to consider is `BooleanPropositionLeaf` with constructors
`truth (SavedBooleanGuard)` and `relation (unequal : Bool) (left right : Lean.Expr)
(nontruth : unequal = false → right ≠ Bool.true-expression)`. Keep the existing
SavedBooleanGuard type and parser unchanged. Supply a coercion from it to the
new leaf so existing source/test constructors remain usable. Define condition,
evidence, operands, and denote for the new leaf, and prove minimum/operand sizes.
A new parser first tries savedBooleanGuard?, then exact Bool Eq/Ne heads; it
requires right != true for Eq and exact standard evidence through the enclosing
guard decision checker. No bare relation is added to guardOperands?.

Change the savedLeft/right/both, letSaved and localNegation Guard fields to the
new leaf. Their operands become concatenated leaf operand lists rather than a
single saved operand. Extract a leaf with a small generic helper over compiled
operands; prove its accepts/correct/invariant properties once and use them in
extractGuard. Existing GuardCondition/GuardDecision saved constructors likewise
carry the new leaf, with otherwise identical proof structure. The new leaf parser
and `not_guard` lemma replace the old truth-only fallback sites in GuardSyntax.
The leaf module can import GuardLet for guardOperandOverhead; Guard then imports
that module. Keep SavedBooleanGuard and GuardLet independent to avoid a cycle.

The raw converted-operand bound against a bare relation plus the existing
overhead is false: a bvar conversion has size 1176, while Eq Bool bvar bvar has
size 626 and guardOperandOverhead is 315. Do not enlarge the global overhead or
assert the false bound. Relations enter only under junctions or negation, whose
syntax supplies sufficient extra size. Prove leaf operand bounds against
`Not leaf.condition` plus the existing overhead. Junctions have another guard
condition, whose minimum size exceeds the Not head. Keep Guard.letSaved and its
parser fallback truth-only for this increment; changing it would cancel the
extra enclosing syntax in wrapped operands. Compound relation bodies under lets
still use ordinary letGuard. This is the selected bounded implementation plan.
