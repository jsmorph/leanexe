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

The maintained gate checks 235 semantic examples and audits all 120 declared
theorems across the seven development modules, including helper proofs. It
passed with the pinned Lean version; each audited theorem depends on no axioms
or only `propext`. See [the proof reference](type-safety.md) for
the exact theorem boundary and verification command.

Checked addition is still the bounded-natural operation: operands and successful
results are below `2^64`, and an overflow terminal records bounded operands whose
sum is at least `2^64`. This milestone does not claim overflow-freedom or
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
data. The following work remains separately tracked:

| Language family | Required definition and proof |
|-----------------|-------------------------------|
| Remaining natural arithmetic and U8/U32/U64 operations | Define each bounded/modular operation and prove its primitive safety. |
| Additional array operations | Empty, size, checked get/set/push/append are proved. Replication, slicing, search, and other collection forms remain to be specified and proved or derived. |
| Bytes and byte operations | Define byte bounds, copying, slicing, endian conversion, and operation-specific failures. |
| Data generalizations | Monomorphic nominal tables, constructors, exhaustive matches, and recursive value typing are proved. Dependent indexed families and any further type-level features require separate rules. |
| Collection binders, folds, loops, recursion forms | Replace schematic families with complete rules or justified derived forms, including captured lexical environments and early exits. |
| Raw-word binary64 primitives | Define permitted results and prove preservation for every allowed result. |
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

## Bounded-natural extension in progress

The following is the next specified increment, not yet part of the checked
coverage reported above. It completes the documented bounded-natural primitive
family; it does not claim every operation on Lean's unbounded `Nat`.

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
runtime typing rule must also preserve the original result type's formation.
No underflow or division-by-zero failure is introduced.

Successor and predecessor are transparent add/sub-by-one expressions. Boolean
to natural conversion is `ifE b (nat 1) (nat 0)`. These definitions evaluate their
argument once and introduce no hidden bindings. Source extraction equivalence is
not implied by these definitions. Natural pattern matching remains a separate
form to define or derive with proof. Fixed-width words and their modular,
bitwise, shift, and conversion operations remain outside this increment.

Acceptance requires exact primitive success/failure and bound laws, comparison
characterizations, and updated machine safety, relevance, and algorithmic typing
proofs. The primitive definitions themselves must not depend on a safety premise.
