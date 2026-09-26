# Equality and decisions over Boolean-input predicate calls

A source form distinguishes Boolean BEq/bne from a decision of Eq/Ne while
preserving exact source syntax and native Boolean meaning. Each new source rule
requires separately admitted Boolean conversions for both children and a typed
Boolean-input function witness. The result uses the existing proved word
comparison followed by encoded negation. Existing Boolean equality without the
new function kind retains its previous lowering.

The helper proof initially used the reserved word local unqualified inside a
simp list; qualifying the source constructor resolved that syntax error. The
extractor termination proof needed the source form unfolded before applying its
child-size bounds. The soundness cases similarly needed an explicit, unfolded
source-form equation: merely supplying all rewrite arguments did not allow rw
to see through the source-form definition. These failures and the successful
focused checks are retained. Source totality, correctness, acceptance, soundness
and structural invariants pass.

The retained Id-result example first lacked an expected Bool type for equality
instance resolution. A show-ascription elaborated to an intermediate Boolean let,
which is still outside the direct-call grammar. An explicit inferInstance term
also adds an evidence wrapper outside this exact-instance grammar. The example
now supplies Bool and its actual standard BEq instance explicitly, and uses an
explicit Bool Eq type for the decision. The ordinary inferred-type examples
remain alongside this annotation case. An elaborated-body inspection records
both distinctions; direct Boolean lets and inferInstance wrappers remain open.
The extra raw rejection test also required explicit Nat types on its counters.

Examples cover BEq/bne, decided Eq/Ne, repeated negation, junctions, mixed
word/Boolean predicates, compound arguments, captures, Id computations and all
three declaration scopes. Additional raw checks reject wrong evidence, evidence
for different conditions, wrong universes and wrong operand types, with twelve
positive controls. Focused tests pass 16,052 native/IR comparisons and 11,574
invalid-input checks. Prior junction/equality tests pass 16,356 comparisons and
11,540 invalid-input checks. The compiler theorem, audits and engine gate are next.

The general compiler theorem and all eighteen axiom audits pass. Native Lean/V8
agree on 2,161 inputs across 116 declarations, including 55 ranges. All 106 prior
modules retain identical bytes. The full native corpus contains 834 declarations.
