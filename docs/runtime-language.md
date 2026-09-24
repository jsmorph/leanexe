# Strict runtime language and relevance profile

Track 1 specifies and proves an independent runtime language. This milestone
keeps the checked strict semantics and defines a stricter admission profile for
machine-written programs. It introduces no deferred evaluation or thunk store.
The namespace remains `LeanExe.TypeSafety`.

This is a normative language definition. The existing LeanExe compiler does not
yet enforce this profile, and the profile does not itself prove correspondence
with current compiler behavior. Compiler correctness is a separate obligation,
not a prerequisite for the language theorem. The full-language coverage below
remains explicit.

## Design decisions

Machine-written source makes explicit forms and annotations practical. The
standard for each extension is a small syntax with independently stated typing
and execution rules, explicit binding and failure behavior, and checked
metatheory. Compiler acceptance is not the definition of well-typedness. An
implementation convenience or a shorter generated program is not evidence that
a language rule is correct.

Evaluation is strict and ordered. A let-bound expression evaluates before its
body, constructor fields evaluate left to right, and function arguments evaluate
in list order. A conditional evaluates its condition and selected branch. A sum
eliminator evaluates its scrutinee, including its payload, before entering the
selected branch. A missing binding or wrong eliminator shape is stuck, not an
implicit permitted failure.

Every introduction of a variable in the profile must have a syntactic use in
its scope. This includes let bindings, function parameters, both product-pattern
bindings, and each sum-pattern payload binding. Repeated uses are permitted.
The rule is relevance, not linearity, and is not an ownership discipline.

Product fields are eliminated by a complete two-field pattern, not an
unrestricted projection. The raw calculus retains `fst` and `snd` for its existing
results; the profile rejects them everywhere. Unit has a zero-field eliminator,
so consuming a Unit does not require inventing a meaningless payload binding.

The profile deliberately rejects some programs that the current compiler
accepts. It does not introduce lazy evaluation to accommodate unused expressions.
However, syntactic relevance alone does not prove that strict evaluation agrees
with the existing demand-based implementation; evaluation and failure order
still belong to a separate correspondence question.

## Exact binding rules

Variables are de Bruijn indices. The latest single binder occupies index zero.
Function parameters are bound in argument order: index zero is the first
parameter, index one the second. A call starts in exactly its parameter
environment, without implicit capture of caller locals.

| Form | Typing and evaluation | Profile requirement |
|------|-----------------------|---------------------|
| `letE bound body` | Evaluate bound, prepend its value, then evaluate body. | Index zero must occur free relative to body's local binders. Both subexpressions must be admissible. |
| `split product body` | Evaluate product; for a pair, prepend left then right. Body context is `α :: β :: Γ`. | Both indices zero and one must occur in body; subexpressions must be admissible. |
| `unitCase scrutinee body` | Evaluate a Unit scrutinee, then evaluate body in the original environment. No new binder. | Both subexpressions must be admissible. |
| `sumCase scrutinee left right` | Evaluate the sum, then prepend its payload to the selected branch's environment. | Each branch must use its own index-zero payload binder; all subexpressions must be admissible. |
| `natCase scrutinee zeroBody succBody` | Evaluate a Nat64 scrutinee once; zero uses the original environment, successor prepends its predecessor. | Both arms must be admissible; the successor arm must use its index-zero predecessor. |
| Function declaration | Type body in exactly its declared parameter context. | Every parameter index must occur in body; body must be admissible. |
| `fst`, `snd` | Still defined in the raw strict calculus. | Rejected by the profile, including when nested. |

The occurrence check shifts its searched index under binders: one position for
let and sum arms, two for a product-pattern body, and none for Unit elimination.
Occurrences under an inner binder must not be confused with the outer variable.

## What the restriction does and does not establish

`uses i e` answers whether variable index `i` occurs syntactically in expression
`e`, accounting for intervening binders. `admissible e` recursively checks the
binding rules above. `programAdmissible` checks bodies, parameter occurrences,
and exact alignment with the signature list.

Admission also requires the ordinary typing judgments. The occurrence check is
not a type checker: a syntactically relevant expression can still be ill typed.
`ProfileTyped` and `ProfileProgramTyped` combine the two obligations.

This rule does not mean that every binding is read on every execution path.
For example, a binding used only in one conditional branch has a syntactic use.
It also does not mean that every computation changes the final answer. Deciding
semantic necessity for arbitrary recursive programs is not the purpose of this
local check. Mandatory use of pattern bindings is not a whole-program analysis
of whether every declared field ultimately affects an observation.

Admission is checked on program syntax. Runtime states retain the existing
configuration-typing judgment; no preservation of source-level relevance across
individual machine steps is assumed or claimed.

## Checked profile results

The raw language includes `split` and `unitCase`. Their environment and
continuation rules preserve typing. Progress, preservation, reachable-state
safety, returned-value typing, and overflow justification have been kernel-checked
with these cases included.

The profile theorem then uses the ordinary typing component of its admission
premises. It states that every reachable runtime state remains typed and cannot
be stuck. Restricting source admission does not require a second execution
relation or a compiler theorem.

The maintained gate checks 758 semantic examples and audits all 438 declared
theorems across the twenty-one development modules, including helper proofs. It
passed with the pinned Lean version; each audited theorem depends on no axioms
or only `propext`. See [the proof reference](type-safety.md) for
the exact theorem boundary and verification command.

The bounded-natural primitive family below is checked. Operands and successful
results are below `2^64`; an overflow terminal records bounded operands whose
tagged sum/product is at least `2^64`. This does not claim overflow-freedom or
termination. The signature and natural-bound premises remain substantive.

## Decision evidence

The repository's maintained examples include `unusedScalarLetSkipsTrap`,
`ignoredCallArgSkipsTrap`, `productHelperParamSkipsTrap`, and
`statusSkipsUnusedPayloadTrap` in
[Correctness.lean](../LeanExe/Examples/Correctness.lean), with expected successful
results in [core_correctness.js](../test/core_correctness.js). `Binding.thunk`,
inline-call selection, and materialization definitions explain why the present
implementation distinguishes deferred and strict cases. Those files were
inspected; their compiler test suite was not rerun for this language review.

The user then explicitly authorized stricter language design and emphasized
machine-written source. The design therefore chooses strict semantics and
rejects unused binding introductions rather than adding deferred machinery.
The abandoned deferred-calculus proposal created no Lean definitions or proofs.
Existing compiler behavior is evidence of a compatibility boundary, not a rule
that this independent language must reproduce.

## Full-language coverage

The profile applies to the scalar/product/sum/call calculus, complete product
and Unit elimination, the six array forms below, and monomorphic nominal recursive
data. The [coverage ledger](type-safety-coverage.md) records every documented family.
The following work remains separately tracked:

| Language family | Required definition and proof |
|-----------------|-------------------------------|
| U8/U32/U64 operations | Arithmetic, comparisons, conversions, bitwise operations, complement, and masked shifts are checked. Raw binary64 is tracked separately below. |
| Structural equality | Strict equality is checked for the independent EqTy domain, including acyclic compound/nominal types. Bytes and arbitrary source BEq implementations remain separate. |
| Option/Except combinators | Sum/data elimination supplies ingredients; map/bind/default/filter/tests/fallback and conversion APIs still need proved expansions. |
| Additional array operations | Empty, size, checked get/set/push/append are proved. Replication, slicing, search, and other collection forms remain to be specified and proved or derived. |
| Bytes and byte operations | Define byte bounds, copying, slicing, endian conversion, and operation-specific failures. |
| Data generalizations | Monomorphic nominal tables, constructors, exhaustive matches, and recursive value typing are proved. Dependent indexed families and any further type-level features require separate rules. |
| Collection binders, folds, loops, recursion forms | Replace schematic families with complete rules or justified derived forms, including captured lexical environments and early exits. |
| Raw-word binary64 primitives | Define permitted results and prove preservation for every allowed result. |
| Generic traps and bang wrappers | Absent. Only justified arithmetic overflow is a machine failure; checked array failures are ordinary data. Any added traps need explicit rules. |
| Counter reads and explicit release | Define abstract state and a declarative admissibility/ownership discipline. Ordinary relevance does not discharge this obligation. |
| Algorithmic type checking | Exact inference/admission correspondence and expression type uniqueness are proved for the current calculus. Every future extension must preserve these results. |

Abstract array lengths must be representable by the specified `Nat64` size
operation. Growing operations must preserve the length bound or have a precisely
specified failure. That language-level obligation requires no physical allocator
proof. Conversely, a full language claim including explicit release needs rules
for permission and subsequent uses; a pure value theorem cannot silently cover it.

## Persistent array semantics

The following six forms are implemented in the independent calculus and covered
by its checked core and profile safety theorems.

`array α` contains a finite sequence of values of type `α`. Its mathematical
length must be strictly below `2^64`. This bound belongs to value typing and makes
the size result representable. Arrays are persistent abstract values: an update
returns a new value and cannot mutate an earlier one. This definition says
nothing about physical storage, sharing, allocation, or release.

| Expression | Result type | Behavior after operands evaluate |
|------------|-------------|----------------------------------|
| `arrayEmpty α` | `array α` | Empty sequence; the element type is explicit. |
| `arraySize a` | `nat64` | Mathematical sequence length. |
| `arrayGet? a i` | `sum unit α` | `inr` selected element if `i < length`; otherwise `inl unit`. |
| `arraySet? a i x` | `sum unit (array α)` | `inr` sequence with index `i` replaced if in bounds; otherwise `inl unit`. |
| `arrayPush? a x` | `sum unit (array α)` | `inr` sequence with `x` appended if the new length is below `2^64`; otherwise `inl unit`. |
| `arrayAppend? a b` | `sum unit (array α)` | `inr` concatenation if the combined length is below `2^64`; otherwise `inl unit`. |

Every operand evaluates strictly in its written order. In particular an invalid
set index does not skip the replacement expression: if that expression overflows,
the machine reaches arithmetic overflow before it can return the index failure.
Checked array failure is ordinary typed data, not a new machine terminal.

These forms introduce no binders. Relevance recursively checks every operand
under the same context. A sum branch can consume a failed operation's Unit payload
using `unitCase`. Array size and lookup observe only part of a value; mandatory
binder occurrence does not prohibit every operation that discards information.

Checked operation laws establish exact failure conditions, length preservation
for set, read-after-set, unchanged reads at other indices, and lengths and reads
after push and append. Universal failure and length-bound proofs cover growth
failure; the result does not rely on constructing huge arrays in tests. The
machine extension preserves the existing safety results for nested arrays,
calls, lexical environments, and continuations.

## Nominal recursive data

The declaration, typing, runtime, and relevance rules in this section are now
covered by the checked safety result reported above.

A declaration table maps each nominal datatype index to a finite ordered list
of constructors; each constructor has a finite ordered list of field types.
Types gain a nominal reference `data i`. Formation requires every reference,
including references under products, sums, and arrays, to name an entry in the
table. Every field of every constructor is checked. Function signatures and
local typing contexts also require well-formed types.

Recursive references are names, not instructions to unfold declarations during
checking. Self-recursion and mutual recursion are allowed. The first-order field
grammar contains only positive type constructors; there are no function domains
or type-level computations in which to hide a negative occurrence. Values remain
finite inductive trees. This is not a representation of cyclic mutable heaps.
These declarations are monomorphic; source specialization and dependent indexed
families are separate questions.

Zero-constructor declarations are allowed. A recursively declared type may have
no finite inhabitants. Neither property is a type error, and declaration validity
does not assert inhabitance or program termination.

`dataCtor dataId ctorId fields` supplies exactly the declared field list. Field
expressions evaluate left to right. `dataCase dataId resultTy scrutinee branches`
has one branch for every constructor, in declaration order. Each branch carries
its field arity explicitly; typing checks the annotation against the declaration.
There is no wildcard branch. The selected branch receives the constructor fields
followed by its captured lexical environment, with the first field at index zero.
Runtime matching checks both nominal identity and the selected branch's arity;
malformed matches remain stuck rather than becoming a permitted failure.

All branches are type checked, including branches not selected by an execution.
Every pattern field must occur syntactically in its branch under the relevance
profile. Outer-variable occurrence checking shifts by the explicit branch arity.
Zero-field branches introduce no variables and require no artificial Unit field.

Formation must hold inside derivations, not just for the final result type.
Sum introductions must validate the unselected summand, and empty arrays must
validate their element type. Otherwise malformed types could disappear beneath
eliminators. A zero-branch match must validate its explicit result type, since
there is no branch from which to derive its formation.

The checked results include: declaration-checker soundness and completeness;
formation of expression, argument, value, and environment types; exact constructor
and branch lookup; nominal canonical forms; and extensions of preservation,
progress, and reachable-state safety. Program typing includes well-formed
declarations and signatures as well as checked bodies. This adds formation
premises to the language judgments, never an assumption of safe execution.

Runtime result types must also be formed. The empty continuation and overflow
typing rules carry result-formation evidence, and formation transfers through
frames and continuations. `StateTyped.wellFormed` establishes the result for every
state typed under an admitted program. Arithmetic overflow cannot be used to
assign an undeclared nominal result type.

## Explicit sums and algorithmic typing

Sum introductions are `inl otherTy payload` and `inr otherTy payload`. The other
alternative is explicit in the expression and must be well formed. Values still
store only their tag and payload. Expression types are proved unique.

Raw structural inference corresponds exactly to the declarative expression
judgment. Argument checking enforces exact arity and types; branch checking
enforces exact constructor coverage, field arities, and a common result.
These total checks recurse over finite syntax. They do not execute recursive
functions or unfold recursive declarations.

Public admission additionally validates every declaration, signature, and
context type, including unused entries. Raw inference alone is insufficient:
the raw variable rule can refer to a malformed type in an unvalidated context.
`infer_eq_some_iff` includes formed ambient inputs; `programWellTyped_iff`
agrees with the complete `ProgramTyped` judgment. The profile checker
characterizations additionally require the syntactic relevance checks.

The checked results include raw inference soundness and completeness, expression
type uniqueness, exact public expression/program admission characterizations, and
reachable-state safety for checker-accepted programs and closed entries. These
results concern the independently specified language, not compiler acceptance.
General recursive programs can pass these checks; termination and absence of
specified arithmetic failure are separate properties.

## Bounded-natural operations

The following operations and their metatheory are checked. This covers the
documented bounded-natural primitive family; it does not claim every operation
on Lean's unbounded `Nat`.

All operands evaluate once, strictly from left to right. `natBin op a b` takes
two `nat64` operands and returns `nat64` on success. `natCmp op a b` takes two
`nat64` operands and returns `bool`.

| Operation | Mathematical behavior |
|-----------|-----------------------|
| add | Sum if below `2^64`; otherwise addition overflow. |
| mul | Product if below `2^64`; otherwise multiplication overflow. |
| sub | Saturating natural subtraction. |
| div | Natural quotient; divisor zero gives zero. |
| mod | Natural remainder; divisor zero returns the dividend. |
| min, max | Lesser or greater operand, respectively. |
| eq, lt, le | Boolean equality, strict order, or non-strict order. |

Overflow records an addition/multiplication tag and both operands. A permitted
failure requires bounded operands and the tagged mathematical result to be at
least `2^64`; malformed error records do not count as terminal outcomes. The
runtime typing rule also preserves the original result type's formation.
No underflow or division-by-zero failure is introduced.

Successor and predecessor are transparent add/sub-by-one expressions. Boolean
to natural conversion is `ifE b (nat 1) (nat 0)`. These definitions evaluate their
argument once and introduce no hidden bindings. Source extraction equivalence is
not implied by these definitions. Natural pattern matching is specified below.
Fixed-width word operations are also specified separately.

Checked primitive laws characterize exact success/failure, bounded outcomes,
saturation, division/remainder by zero, and comparison results. Machine safety,
relevance, and algorithmic typing proofs include all these forms. Derived helpers
have typing theorems and executable inference/step equations. Primitive definitions
take raw operands; their bounded-outcome theorem separately requires bounded inputs.


## Word arithmetic and conversions

This section is included in the checked coverage above. Word widths are exactly
8, 32, and 64 bits. Write `M = 2^w` for
a width's modulus. A word literal carries its width and a natural value strictly
below `M`. Oversized literals are rejected, rather than implicitly normalized.
Runtime word values retain their width tag.

`wordBin width operation left right` requires both operands to have that exact
word type. Arithmetic operations are add, sub, mul, div, mod, min, and max.
`wordCmp width comparison left right` similarly requires matching widths and
returns Bool using unsigned equality, strict order, or non-strict order.
These operations evaluate both operands once, left to right. They introduce no
new permitted machine failure. A wrong runtime width is a malformed state.

Addition and multiplication return the mathematical result modulo `M`.
Subtraction is modular, not saturating: on represented operands it returns
`a-b` when `b ≤ a`, and `M-(b-a)` otherwise. The raw total definition normalizes
both inputs before subtracting: `(a % M + M - b % M) % M`. Division by zero
returns zero; remainder by zero returns the dividend. Other division/remainder
results are the ordinary unsigned quotient/remainder. Min and max select the
corresponding operand using unsigned order.

`wordOfNat target e` accepts a bounded natural and reduces it modulo the target
modulus. `wordToNat source e` accepts a word of the stated source width and
preserves its value; every supported width fits in Nat64. `wordCast source target e`
checks the source width and reduces modulo the target modulus. Widening preserves
the value; narrowing may lose information. A same-width cast is the identity on
represented values. Conversions evaluate their operand before converting: they
cannot hide an overflow from a bounded-natural operand expression.

Raw normalization needs only the target width. The source width belongs to the
cast's typing and execution checks and the premises of widening/round-trip laws;
an ignored source argument is not added to the arithmetic helper.

Checked results include representable outcomes, exact arithmetic formulas,
both subtraction branches, zero-divisor behavior, quotient/remainder reconstruction,
min/max selection, normalization identity/idempotence, widening, and widening-then-
narrowing round trips. Comparisons use the same proved unsigned mathematical
relations as bounded naturals. Formation, canonical forms, machine safety, relevance,
and exact algorithmic admission include every new form. Bitwise operations,
complement, and shifts are specified next. Raw binary64 remains outside the
checked language.


## Bitwise operations and masked shifts

This section is included in the checked coverage above. It adds
`bitAnd`, `bitOr`, `bitXor`, `shiftLeft`, and `shiftRight` to the existing word
binary-operation family. Both operands, including a shift count, must have the
stated word width. Existing strict evaluation and width checks apply.

For every bit position below width `w`, AND/OR/XOR apply the corresponding Boolean
operation to the two input bits. Results are representable words, with no bits
at or above `w`. This pointwise specification is independent of a host-library
bitwise implementation. The bit at position `i` of a natural value is determined
by `(value / 2^i) % 2`. The structural `bitwiseBits` definition recurses over the
finite width.
`bitwiseBits_bitAt` proves the universal per-bit characterization, and
`bitwiseBits_bounded` proves its result bound, including for unbounded raw inputs.
`eq_of_bitAt_eq` proves equality of bounded numbers from their in-range bits.
These results do not assume equality to the host-library bitwise implementation.

Let `k = count % w` and `M = 2^w`. Left shift returns `(value * 2^k) % M`;
right shift returns `value / 2^k`. Thus shifting by the width is the identity,
not a zero result. Right shift is logical/unsigned. The checked shift-count laws
establish positive widths, a reduced count below
`w`, and periodicity under addition of any multiple of the width. Exact shift
formulas and zero/width shift identities are proved.

`wordNot width value` is a transparent XOR with the represented mask `M-1`.
It introduces no new expression constructor or runtime frame and evaluates its
operand once. Its derived typing, inference, step, and relevance equations are checked,
along with zero/self/mask identities, XOR cancellation, and complement involution.
The existing generic word rules cover these operations in all safety and typing
results; no extra failure outcome is introduced.


## Natural-number pattern matching

`natCase scrutinee zeroBody succBody` is checked. Its scrutinee has type Nat64.
The zero arm has result type `τ` in the current context; the successor arm has
that same result type under `nat64 :: Γ`. Every arm is checked even if a known
scrutinee will not select it. No result annotation is needed because the zero
arm supplies a candidate type checked against the successor arm.

The machine evaluates the scrutinee once and captures the branch environment.
Zero enters its arm in that environment. A value `n+1` enters the successor arm
with `n` prepended at index zero. The predecessor is representable because the
scrutinee was representable. Wrong-shaped scrutinees remain stuck.

Relevance checks both arms and requires a syntactic use of the successor binder.
Outer-variable occurrence shifts by one only in the successor arm. The checked
step equations and occurrence/admission characterizations record these exact
rules; all safety, formation, and algorithmic typing results include the form.
This does not assert termination of recursive calls or correctness of a source
recursion recognizer.


## Checked Boolean source expansions

`boolNot e` expands to `ifE e false true`. Binary `boolAnd`, `boolOr`,
`boolXor`, and `boolEq` construct a strict pair of their operands and split it
into a closed two-field Boolean body. Both operands must have Boolean type and
evaluate once, left to right, even when the left Boolean determines the result.
Use `ifE` for conditional evaluation. These definitions introduce no machine
forms and make no compiler-recognition claim.

Checked laws cover typing, exact raw inference, relevance, evaluation stages,
and truth-table execution for supplied Boolean values in arbitrary environments
and continuations. Both generated fields occur syntactically; caller variables
remain in the original operand scopes. Boolean equality does not cover compound
structural equality.


## Structural comparison and source admission

The checked comparison of finite raw `Value` trees is independent of typing.
Its proved specification is exact: the Boolean result is true if
and only if the two values are propositionally equal. Arrays compare length,
order, and all elements; nominal values compare type identity, constructor, and
all fields. Scalar tags, word widths, and sum tags are significant.

The raw comparison is defined on malformed values and finite recursive values
without admitting their types for source equality. The documented `EqTy` domain
excludes recursive variants. `EqualityTypes.lean` now provides the independent
judgment and exact executable check for that boundary. Bytes are not yet
represented in the calculus. Arbitrary user-selected `BEq` implementations remain separate.


### Checked equality admission

The independent equality domain is the inductive closure judgment `EqTy`.
The checker is proved equivalent to that separate specification. Unit, Bool,
bounded naturals, and words qualify. Products, sums, and arrays require qualifying components. A
nominal type requires a valid declaration lookup and qualifying fields in every
constructor. This least inductive closure excludes reachable recursive cycles,
including cycles beneath arrays or alternatives with a nullary constructor.
An empty declaration qualifies without implying that it has a value.

The checked algorithm starts with a false flag for each declaration and
repeatedly checks all constructor fields against the previous flags. Its bound
is the number of declarations. Monotonicity, strict increase in the count of true
flags when a round changes the table, and the table length bound now prove
generic stabilization in `EqualityFlags.lean`. The equality-specific checker
and correspondence are proved in `EqualityTypes.lean`. Soundness uses induction
on rounds; completeness uses induction on the independent judgment against the resulting fixed table.
`equalitySupported_iff` has no unproved fuel-adequacy or acyclicity premise.
The strict source expression described below uses this proved domain.

This is a local property of the queried type. An unrelated recursive declaration
does not reject an acyclic query. Global declaration formation is still required
by the public source admission check; local equality admission cannot replace it.


### Checked source structural equality

`structEq left right` requires both operands to have the same type `τ` and
a derivation of `EqTy declarations τ`. It evaluates the left operand first,
then the right, and returns the Boolean computed by `valueEq`. The operation
introduces no failure outcome. Failure while evaluating an operand propagates
through the existing machine rules. Every source field is evaluated before its
constructed value participates in comparison.

The raw transition is total on two returned values, including malformed values.
That behavior does not admit heterogeneous or malformed source expressions.
Static inference must check operand type equality and the independent equality
domain; public admission must retain the ambient formation checks. Relevance
checks both operand expressions. Formation, exact inference, type uniqueness,
progress, preservation, finite-execution safety, and profile safety include this
form. Exact final-step laws connect returned true/false to raw value equality
and inequality, respectively.


## Checked hygienic renaming and typing transport

The checked renaming library supports inserting bindings around code that
refers to its original context. Renaming maps only free variable indices. A
lifted map fixes the newly bound prefix and maps the remaining indices beyond
that prefix. Let and sum arms lift by one, complete product elimination by two,
natural successor arms by one, and nominal arms by their explicit field count.
Natural zero arms introduce no binder. Types and declaration/function identities
are not variable indices and remain unchanged.

The checked results are total syntax traversal, pointwise congruence,
identity/composition laws on expressions, context lookup preservation under
lifting, and typing preservation/weakening. These are binding and static typing
results. They do not establish evaluation equivalence, public checker equivalence
under arbitrary maps, or relevance of newly inserted function parameters. Public
admission still requires formation of the entire ambient context.

Occurrence/admissibility preservation and operational correspondence are checked
below under their respective hypotheses. Noninjective renaming may merge free
variables; a forward type-context map can turn an originally out-of-range raw
variable into a valid one. It alone does not establish runtime correspondence.

### Checked relevance preservation under renaming

For arbitrary, possibly noninjective maps, the proved exact occurrence law is:
`uses target (Expr.rename mapping expr) = true` iff there exists a source index
that maps to `target` and occurs in `expr`. A claim comparing only the occurrence
of one chosen source index would be false when multiple indices merge.

Lifting gives each protected local index exactly itself as a preimage. The
proofs establish exact Boolean equality of `admissible` before and after renaming,
and `parametersUsed` equality only for an explicitly preserved prefix. This does
not make newly inserted parameters used. `ProfileTyped.rename` and `.weaken`
combine relevance invariance with raw typing transport. Runtime correspondence
uses the separate exact environment relation below.


### Checked environment and execution correspondence

`EnvCorresponds mapping source target` compares every lookup, including absence:
`lookup target (mapping index) = lookup source index`. Its identity, empty,
composition, one-binding lift, common-prefix lift, and insertion laws are proved.
`renameBranches_lookup` preserves missing branches and the selected branch's
explicit arity while renaming its body beneath that arity.

This relation does not assume injectivity. Merging equal source values can satisfy
it; merging different values or mapping an absent source index to an available
target index cannot. Raw runtime values do not determine unique type contexts,
so environment correspondence and `RenamingTyped` remain separate relations.

`FrameCorresponds` gives each captured environment its own variable map, keeping
stored values and metadata identical. Related states take related steps or both
lack a successor. Calls enter the unchanged program body with identical fresh
arguments under the identity map. Finite traces transfer in both directions;
reflection does not require an inverse map.

For expressions under corresponding environments and initially empty
continuations, `rename_returns_iff`, `rename_overflows_iff`, and
`rename_reaches_stuck_iff` preserve and reflect each exact returned value, each
exact overflow record, and finite stuck reachability. There are no typing
premises. The original `Terminal` predicate still requires mathematical overflow;
a forged record remains stuck. These are same-program finite-execution laws,
not termination or compiler-correctness results.


## Checked continuation sequencing

`State.appendKont` appends pending frames to an evaluation or return state;
overflow has already discarded its stack. `ReturnBoundary` means precisely
`ret value []`. Away from this boundary, extending a state commutes with its
actual optional step, including missing steps. At the boundary an appended
frame can enable a new transition, so no unconditional optional-step equation
is claimed. Successful steps and arbitrary finite traces do extend.

`steps_appendKont_decompose` proves that every finite combined execution either
has not crossed a value-return boundary, or factors through the source's return
and a subsequent continuation execution. Its corollaries give exact equivalences:

- A final returned value requires a source return followed by that continuation
  result, and those two executions suffice.
- An exact overflow record is reached either in the source computation or after
  a source return in the continuation. The record's validity remains governed
  by the unchanged mathematical overflow predicate.
- A stuck state is reached either in the source computation or after a source
  return in the continuation. It is never reclassified as permitted failure.

These statements concern arbitrary raw states and a fixed program; they require
neither typing nor termination. They supply sequencing laws for future derived
forms. They do not themselves establish any Option/Except API.


`Execution` additionally proves first-step decomposition and inversion for a
fixed no-successor endpoint. This endpoint premise matters: a zero-step trace
back to an active initial state need not exist after taking its first step.
`sequence_returns_iff`, `sequence_overflows_iff`, and
`sequence_reaches_stuck_iff` combine a known first operand transition with the
continuation laws. No-successor endpoints still include stuck states; they are
not all declared permitted terminal outcomes.


## Checked core sum and Unit execution laws

`SumExecution` gives exact return, overflow-record, and stuck-reachability laws
for arbitrary operand expressions in both injections, Unit elimination, and
sum elimination. Injections return exactly a wrapped operand value and preserve
the operand's overflow/stuck outcomes. Unit elimination runs its body in the
original environment only after a Unit result. Sum elimination runs only the
selected body with its payload prepended to the captured environment.

The elimination laws distinguish scrutinee failures from selected-body failures.
A wrong raw scrutinee shape yields stuckness, not a return or permitted fault.
These statements need neither typing nor termination, and hold with the same
program on both sides. They establish reusable behavior laws for existing core
forms; the individual Option/Except expansions remain the next proof increment.
