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

The maintained gate checks 113 semantic examples and audits seven core results,
all 13 profile theorems, and all 32 array operation and list-typing theorems. It
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
and Unit elimination, and the six array forms below. The following work remains
separately tracked:

| Language family | Required definition and proof |
|-----------------|-------------------------------|
| Remaining natural arithmetic and U8/U32/U64 operations | Define each bounded/modular operation and prove its primitive safety. |
| Additional array operations | Empty, size, checked get/set/push/append are proved. Replication, slicing, search, and other collection forms remain to be specified and proved or derived. |
| Bytes and byte operations | Define byte bounds, copying, slicing, endian conversion, and operation-specific failures. |
| Nominal structures, variants, recursive families | Define declaration well-formedness, constructor fields, tags, matches, and recursive value typing. Extend the chosen pattern-binding discipline explicitly. |
| Collection binders, folds, loops, recursion forms | Replace schematic families with complete rules or justified derived forms, including captured lexical environments and early exits. |
| Raw-word binary64 primitives | Define permitted results and prove preservation for every allowed result. |
| Counter reads and explicit release | Define abstract state and a declarative admissibility/ownership discipline. Ordinary relevance does not discharge this obligation. |
| Algorithmic type checking | Prove agreement with the declarative typing rules. The occurrence checker alone does not discharge this obligation. |

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
