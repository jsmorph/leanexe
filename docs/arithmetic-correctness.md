# Scalar and bounded-loop compiler correctness

The `compile-arithmetic` command admits a restricted source language covered by
a general compiler theorem. Every successful admission inherits that theorem;
users do not supply a separate proof for each program. The normal `compile`
command accepts more of the LeanExe dialect, but that broader language is not
yet covered by this theorem.

## Accepted source

A declaration must be safe, total, have an executable body, take zero or more
`UInt64` arguments and return `UInt64`. Its body may read arguments, contain
UInt64 literals, metadata, UInt64 `let` bindings, conditionals and pure `Id`
operations, with arbitrary
nesting of supported expressions:

| Source operation | Meaning |
| --- | --- |
| `+`, `-`, `*` | Arithmetic modulo 2^64 |
| `/`, `%` | Unsigned quotient/remainder; zero divisor gives zero/dividend |
| `&&&`, `|||`, `^^^` | Bitwise and/or/xor |
| `~~~` | Bitwise complement of all 64 bits |
| `Bool.toUInt64` | Convert an admitted Boolean value to zero or one |
| `min`, `max` | Smaller/larger UInt64 operand using unsigned order |
| `<<<`, `>>>` | Left/logical right shift; count masked to six bits |
| `if … then … else …` | Branch on `=`, `≠`, `<`, `≤`, `>`, `≥`, `==`, or `!=` between UInt64 expressions, optionally negated with `¬`; Boolean `==`/`!=` guards admit `&&`, `||` and repeated `!`; propositional `∧` and `∨` combine admitted guards; `true`, `false`, `True` and `False` may appear at any guard leaf |

Both direct UInt64 primitives and canonical overloaded operators with the
standard UInt64 instances are admitted. Both `UInt64.complement x` and standard
`~~~x` are admitted, including in helper bodies, comparison operands and range
bounds. Complement lowers to XOR with the full 64-bit mask, with a checked
identity to Lean's native operation. Custom Complement instances are rejected,
including in unused bodies. Literals reduce modulo 2^64. Standard UInt64 numeral
instances also admit inert let, lambda/application and metadata wrappers. The
checker tracks unapplied arguments and requires the same numeral at the exact
standard instance leaf. Unknown instance variables, custom instance values,
unapplied lambdas and extra applications are rejected. This handles elaborator
wrappers introduced inside captured-helper and dependent-proof scopes. Standard
Nat numeral expressions are accepted as arguments to `UInt64.ofNat` and in the
numeric positions of UInt64 OfNat values and instances. The Nat type and value
may carry metadata, including borrowedness. The source grammar retains that
syntax and checks the exact standard Nat instance and its matching number.
Conversions reduce modulo 2^64; this does not add general Nat arithmetic or
public Nat parameters/results. Custom
instances, top-level helper calls, recursion, general runtime Nat,
heap values, imports, and floats are excluded from the current theorem.
Comparisons use the standard UInt64 instances and exact standard decision
procedures. Propositional `=`, `≠`, `<`, `≤`, `>` and `≥` also accept finite `Id`
layers on their UInt64 type argument. The source syntax retains these annotations.
Ordinary and dependent scalar and loop-step `if` comparisons also accept condition and decision
operands that differ through standard arithmetic type annotations and numeral
instances. A checked source relation proves that the corresponding operands
have exactly the same source evaluations. It covers the ten binary UInt64
operations, standard numeral encodings, and corresponding metadata wrappers;
custom arithmetic/numeral instances and different runtime operands are rejected.
The entire decision expression is still checked. Propositional `∧`, `∨` and negation also compose these checked comparison
leaves, retaining exact enclosing propositions and standard decision instances.
The same proved operand equivalence covers saved `decide` values and ordinary
or dependent Boolean-result choices over propositional guards. Boolean `&&`/`||`
subguards retain their exact standard decision evidence. Boolean `==` and `!=` heads still require an unannotated UInt64
type argument.
`>` and `≥` have their own elaborated heads, using the standard `<` and `≤`
decision procedures with reversed operands. `≠` preserves standard inequality
evidence. `¬` can wrap any admitted comparison, including another negation,
and its exact standard decision evidence is checked recursively. The emitted
condition preserves unsigned comparison semantics. Nested
conditionals may appear in comparison operands, arithmetic operands, and let
bindings. Both branches must belong to the supported grammar and satisfy static
local bounds, even when one branch is never executed. Boolean parameters and results are not yet
admitted by this source grammar. Boolean `!` may wrap standard UInt64 `==` and
`!=` expressions, including repeated `!`. These guards retain their Boolean
syntax and exact standard equality-decision evidence. Lowering computes their
polarity and emits the corresponding equality or its negation; it does not
evaluate or omit either UInt64 operand. Propositional `¬` can wrap these guards
as well. Custom BEq and decision evidence remain rejected.

Propositional `∧` and `∨` may nest around admitted comparison leaves. The
extractor checks the whole tree's exact standard decision evidence and every
scalar operand. Guards lower to Boolean words combined by the existing AND/OR
operations, then tested against one. Both sides can be evaluated because all
admitted operands are pure and total, including division by zero. Source/IR
proofs cover scalar results and paired loop-step results without changing the
backend. Propositional `¬` can also wrap whole compounds, repeat, and appear at
any nesting level. The syntax retains each standard Not decision wrapper, and
proved lowering tests each preceding Boolean word against zero.

Boolean `&&` and `||` guards may nest over standard UInt64 `==`/`!=` leaves,
with repeated `!` at any level. The separate source syntax converts to the
shared guard representation with proved preservation of operands and native
Boolean results. The complete standard Bool-equals-true decision evidence is
checked. These guards work in scalar results and loop steps through the same
lowering. Compound Boolean guards can also appear inside propositional `∧`,
`∨` and `¬`, including nested mixtures and repeated negation. Separate wrapper
counts retain Bool.not and propositional Not, with their exact decision evidence.
Every Boolean subtree and compared scalar operand is checked. Custom BEq and
decision instances, including in unused helper bodies, remain rejected.

Literal `true`/`false` Boolean guards and `True`/`False` propositional guards are
admitted as whole conditions and inside mixed guard trees. Repeated `!` and `¬`
retain their exact source syntax and standard decision evidence. Their known
Boolean results lower through word equality. Both branches and all nested
operands remain checked even when a literal determines the result; unsupported
inactive branches, custom decisions and unsupported unused helper bodies are
rejected. This does not add general Boolean parameters or results.

Ordinary Boolean local bindings admit `let flag := x == y`, aliases, literals,
standard UInt64 `==`/`!=`, and Boolean `!`, `&&`, and `||`. Boolean and UInt64
bindings have distinct kinds. Both ordinary `if` and dependent `if h : ...`
may read a saved Boolean or a
Boolean expression combining saved values with admitted comparison/literal
leaves. These bindings work in scalar expressions, helper captures, loop steps
and before a loop. Captures preserve the original flag across later shadowing
or accumulator updates. Every right-hand side and operand is checked even when
unused or short-circuited. Boolean values use proved zero/one words internally.
This covers ordinary lets and Boolean conditions, including dependent
conditions with exact proof domains and erased binder scope. Standard Id
monadic bindings (`let flag ← pure (...)`) use the same typed Boolean storage in
scalar do-blocks, helper bodies, loop steps and before/after a loop. Their input
and lambda-domain types must be exactly Bool. Actions may contain direct Boolean
values, standard Id.pure/Id.run wrappers with Boolean or nested Id annotations,
and metadata. Each action preserves its leaf value and all operands are checked,
including unused binds. Custom Id instances and wrong binder/action types are
rejected. Boolean-valued conditionals over Boolean guards also use this representation:
`let flag := if x == y then x != 0 else y == 0`. Conditions and both branches
may contain saved flags, comparisons, literals, junctions and nested choices.
Choices can also appear directly as scalar or step conditions without a saved
flag. Their complete standard decision evidence is checked, and both branches
must be supported, including inactive or unused ones. The shared parser and
lowering proofs cover choices in ordinary/monadic bindings and helper captures.
Boolean-valued choices also admit propositional guards: UInt64 `=`, `≠`, `<`,
`≤`, `>`, `≥`, `True`/`False`, and the existing closed `¬`, `∧`, and `∨` trees,
including their Boolean comparison/literal leaves. Saved Boolean values may
appear in either result branch. Nested Boolean and propositional choices share
the same proved lowering. Propositional choices check their entire standard
decision evidence, including proved-equivalent arithmetic operands, and preserve
the existing Boolean-choice path.
Boolean-result choices also admit Boolean Eq/Ne directly, including saved flags,
nested Boolean choices and decisions in either condition input or result branch.
The exact standard evidence is checked. A proved literal-true specialization
preserves the original condition for ordinary Boolean choices. These results
compose through Id binds, captures, helper calls, loop steps and surrounding
scalar computations. Dependent Boolean-result choices also compose in these
contexts. Exact proof-lambda domains and names are preserved; structural binder
insertion/removal proves reconstruction and preserves captures through nested
scopes. Branches that use the proof as an executable value are rejected.
Boolean expressions also admit exact Bool-typed lets, including nesting,
shadowing, unused values and captures. Body scalar operands retain their original
Boolean let scope, while direct flag references distinguish the new flag from
external captures. Both the bound value and body are checked. Pure computations
may repeat in generated expressions.
UInt64 bindings inside Boolean results use the same scope-preserving approach.
Word and flag bindings can mix and nest. The source type condition recursively
forbids direct Boolean reads of word slots, and successful extraction proves that
condition; scalar operands retain their original word binding context.
These Boolean/word let annotations also admit standard Id layers. Original
annotations remain in the exact source syntax; derived scalar operands use the
underlying binder type, preserving value and scope. Checked type-size and
annotation-independent evaluation rules justify that representation.

Immediate Boolean-producing lambda applications accept UInt64 or Bool arguments,
including standard Id type annotations. The exact binder and argument are
retained. Nested applications, captures, unused arguments, negation and choices
use the same typed lexical evaluation as Boolean/word bindings. Arguments and
bodies are checked even when unused. Applications compose through Boolean
conversions, scalar and loop-step conditions, Id actions and loop exits.

Unary Bool-parameter local helpers may return UInt64 or ForInStep UInt64,
including nested Id result annotations. This admits the shared continuations
Lean generates for `let flag ← if … then pure … else pure …`, in scalar code,
loop steps and scalar computations after a loop. Native Bool arguments have a
separate binding kind and a proved zero/one compiled representation. Helpers
preserve captures and shadowing, and all unused bodies and call arguments are
checked. Pure scalar Boolean helpers may surround a loop and supply its bounds,
initial value and final computation. A conditional Boolean bind before a loop
can generate a loop-containing helper; that case remains outside this grammar.
Public Boolean parameters/results, named Boolean-returning helpers, mixed Bool/word
parameter lists, loops inside helper bodies and propositional combinations
containing saved Boolean locals remain separate capabilities.

Explicit `decide` and implicit Prop-to-Bool conversions admit the existing
closed guard grammar, including all UInt64 comparisons, propositional literals,
negation and junctions, and closed Boolean guards. The parser requires the exact
Decidable.decide head and the whole standard decision expression. Standard
arithmetic operands may carry different accepted annotations in the proposition
and its decision evidence, justified by the source equivalence proof. Converted
values compose with Boolean negation, junctions and choices, helper arguments,
ordinary/Id bindings, loop steps and surrounding scalar code. Unsupported
operands are rejected even when unused or under an inactive decision. Decisions
also admit Boolean equality and inequality whose operands are admitted Boolean
expressions, including saved flags and nested decisions. This includes explicit
truth coercions (`decide flag`) and implicit Prop-to-Bool conversion. A native
decide lemma connects the exact Eq/Ne source form to shared Boolean equality
lowering. Broader propositional combinations containing saved flags remain a
later extension.

Bool-valued equality and inequality (`a == b`, `a != b`, and explicit BEq.beq/bne
calls) admit the exact standard Bool equality instance. Both inputs may contain
saved flags, literals, comparisons, decisions, negation, junctions, choices and
nested equality. These results work in bindings, conditions, helper captures,
Id actions and loop computations. Both sides are checked, including unused
expressions; custom instances, wrong operand types and unsupported Boolean
inputs remain rejected.

Propositional Boolean equality and inequality (`a = b`, `a ≠ b`) select UInt64
or step results in ordinary and dependent conditions. Both operands may contain
admitted Boolean expressions, including saved flags and choices. Exact Eq/Ne
syntax and decision evidence are preserved and connected to the proved Boolean
equality meaning; the literal-true right side keeps its existing truth path.
Dependent branches check both proof-lambda domains and preserve captures under
erased proof binders. All operands and branches must be supported, including
inactive branches. This composes through helpers, joined Id updates, loop
break/continue, bounds and surrounding scalar code. Ordinary Boolean-result
choices, including dependent Boolean results, also admit these propositions.

Bool.toUInt64 and equivalent dot notation convert admitted Boolean values to
UInt64. Inputs may be literals, saved flags, comparisons, decisions, negations,
junctions or nested choices, including those in helpers and loop contexts.
The source rule preserves the distinct Boolean input type and native conversion;
the lowering uses the proved zero/one representation. Converted words may be
used in arithmetic, comparison operands, bindings, bounds, step results and
post-loop computations. Every operand is checked even when unused. Free
variables, wrong input kinds, extra universe arguments and unsupported Boolean
forms are rejected. Public arguments/results remain UInt64.

Dependent `if h : condition then … else …` admits the same guard trees and
scalar/step result annotations. The extractor checks the whole standard decision
expression, allowing proved-equivalent arithmetic operands, and checks both
proof-lambda domains exactly. Each branch keeps an erased binder in its
lexical context, preserving references to outer values and helper captures.
Both branch bodies and every guard operand must be supported, including inactive
branches. Proofs cannot be read as executable scalar values. Nested dependent
conditions, do-block joins, helper bodies, loop steps and scalar computations
around loops use the same checked rule. This does not admit additional
proof-dependent runtime operations.

Standard UInt64 `min` and `max` lower to unsigned `≤` followed by selection.
The extractor checks their exact standard Min/Max instance. Both operands are
pure and total, so their repeated evaluation in emitted code preserves results.
Custom instances, including in unused function bodies, remain rejected. These
operations may appear in guards, helper bodies, loop steps and range bounds.

Pure `Id.run do` blocks admit `return`/`pure` and monadic UInt64 bindings
(`let x ← …`) with the exact standard Id instance. Straight-line `let mut`
updates become ordinary shadowing lets. Nested blocks, branch-local bindings,
and early returns are supported. Conditionals may carry a `UInt64` result annotation with any finite number of
retained `Id` layers. Branches that join a following computation can elaborate to local continuation
functions; unary UInt64 continuations are admitted as local functions. General monads, effects and custom Id instance expressions remain
outside this increment.

The standard `Id.run`, `pure`, and bind operations also retain these scalar
annotations. Bind inputs, outputs and lambda parameter types are checked;
the input and parameter annotations must match exactly. The shared source
semantics still carries UInt64 values because these Id types are definitionally
UInt64. Scalar helpers, loop steps and computations surrounding a loop use the
same proved wrapper rules. Custom Pure/Bind expressions and unsupported unused
helper bodies remain rejected. This extends monadic and result annotations;
ordinary scalar lets and function argument declarations still use their existing
concrete UInt64 syntax.

Local functions with any finite positive number of UInt64 arguments and a UInt64 result with retained Id layers are
supported when their bodies belong to this same grammar. They capture bindings
where they are defined, so later shadowing does not change the captured values.
Functions may call previously bound functions or introduce further local
functions. Every function body is checked even when the function is unused.
Compilation substitutes the arguments into a closure over compiled expressions;
this may repeat computation and expand output, as scalar let substitution does.
The compiler also admits `Unit → UInt64 → UInt64` continuation (also with retained Id result layers)
functions and calls with the literal `Unit.unit`, as generated by updates after
a branch. The equivalent `PUnit.{1} → UInt64 → result` form and
`PUnit.unit.{1}` calls are admitted too, including in scalar helpers, yielding
steps, early-exit steps and helpers surrounding loops. Both concrete spellings
share the same unit-binding semantics and proofs. Function types and lambda
domains retain their exact admitted spelling; higher PUnit universes remain
excluded. Bodies are checked even when unused. These have a distinct binding
kind from ordinary unary functions.
Calls must supply exactly the declared number of arguments, in source order.
All arguments are checked and evaluated, including ones unused by the body.
Partial applications, function-valued parameters/results and
top-level helper calls remain separate capabilities.

A function may also contain one ascending `for i in [first:count.toNat]` loop
with one UInt64 accumulator. Both endpoints may be standard Nat literals
smaller than 2^64 or supported UInt64 expressions followed by `.toNat`. Omitting
the start means zero. The step defaults to one and may be any positive standard
Nat literal smaller than 2^64, as in `[first:stop:2]`. Steps may yield or finish early with `break`.
The source index retains its Nat type, including Lean borrowing metadata on
that type, and may be converted explicitly with `UInt64.ofNat i`. Pure UInt64
bindings and arithmetic may precede and follow the loop. Local scalar helpers
may also be defined before the loop, using arbitrary finite UInt64 parameter
lists and the supported Unit-prefixed argument forms. Their calls may appear in endpoints, the initial
accumulator, loop steps and the final result. They retain their lexical captures
across later shadowing and accumulator updates. Nested/chained helpers and
standard Id bodies are supported; unused bodies are checked. An ordinary UInt64
`let` may also bind the result of the range computation before a pure scalar
continuation. Nested lets, aliases and captured helpers can use that result;
unused loop values are still checked. This follows the same evaluation order
already supported for a monadic bind of the loop result. The step supports
UInt64 bindings and updates, direct supported local-function bindings, and
supported scalar expressions on their right hand sides. Functions can capture
the current index and accumulator; scalar helpers of any finite positive arity
are supported directly in a step. Updating the accumulator later in the step
does not change an earlier capture. Unused function bodies are still checked.
Standard Id monadic UInt64 bindings (`let x ← …`) are also supported in the
step, including nested pure do computations and unused bound values. The
complete standard Bind instance expression is checked; custom Bind instances
remain excluded. Conditional monadic values, nested scalar branches, branch
updates followed by further computation, and `continue` are supported when
their elaborated continuations belong to the scalar grammar. The source
relation converts yielding continuation result types and bodies together,
preserving input domains, binder positions and captured values. Both branches
and every continuation body are checked, including unused continuations.
`continue` yields the current accumulator and advances the range index.
`break` returns the current accumulator, including updates made before it.
The early-exit path also accepts explicit standard `pure (ForInStep.done …)`
and `pure (ForInStep.yield …)` results, direct `.done`/`.yield` constructors,
and local functions returning them. Functions returning step results may take
any finite positive number of UInt64 arguments, one UInt64 argument with a Unit
prefix, or one complete step result. Functions preserve argument order and captured
values, including through nested/chained calls and standard Id result wrappers. Scalar and step-valued
functions have distinct binding kinds; both
compiled projections describe the same native step result. Step-result bindings
also admit ordinary lets, aliases, lexical capture and straight-line standard
Id monadic binds. `Id.run` and `pure` can wrap a computed step, and the exact
result annotations may contain any number of standard Id layers. A bound
`done` value exits only if it becomes the callback result; ignoring it does not
exit the loop. All bound computations are checked even when unused. Local functions may take a complete step result and return a step result,
including continuations generated by branching monadic binds. These functions
can capture earlier bindings, call prior functions and ignore their argument.
Their bodies are checked even when unused, and their argument and result types
may retain standard Id layers. Inspecting a step with pattern matching remains
a separate capability. Additional accumulators, multiple/nested loops and dynamic steps remain
separate capabilities. Standard Nat literal bounds such as `[:8]` are also
admitted when the literal is smaller than 2^64. The count retains its exact
natural value; larger literals and custom Nat literal instances are rejected.
Dynamic bounds still use a supported UInt64 expression followed by `.toNat`.
Starts may be nonzero, including `[3:8]`, `[1:count.toNat]` and
`[first.toNat:stop.toNat]`. An empty
interval preserves the initial accumulator when the start equals or exceeds the
stop. Internally the loop counts from zero to the ceiling of the natural
truncated distance divided by the step; each source index is the start plus the
step times that counter. The count uses `(distance - 1) / step + 1` for nonempty
ranges, avoiding overflow from adding the step to a large word. Checked distance and index
lemmas connect this representation to native strided interval iteration.
Unit-step ranges keep their preceding output bytes. Computed starts retain their original
captured values throughout iteration, including when the accumulator supplies
the initial start and is later updated. Re-evaluation of compiled pure endpoint
expressions preserves those values. Arbitrary Nat arithmetic in endpoints and
unsupported helper calls remain excluded. Stride positivity is checked
numerically. The original erased proof expression is retained, allowing the
generated proof declarations Lean creates for explicit steps; it cannot bypass
the positive-literal or size checks.

Compilation reserves locals for the accumulator, index and stop and emits an
ordinary Wasm block/loop with a conditional exit and back edge. The early-exit
path adds a fourth local for the exit decision. It evaluates that decision
before updating the accumulator, then moves the index to the stop on done.
Both value and decision expressions are read-only and checked for every prior
flag value; neither can observe an intermediate accumulator update. Compiling
the two projections can duplicate pure computations, subject to the existing
numeric output limits. The proof ties native ascending range iteration to the emitted loop using the remaining
iteration count, and covers setup, final result, exact byte parsing and module
validation. Zero iterations preserve the initial accumulator. All bounds up to
the maximum UInt64 stop are covered by the theorem, regardless of practical
execution time; the execution tests use small counts.

The requested export name must avoid all ten runtime exports. Admission checks
explicit limits below 2^32 on parameter/result counts, UTF-8 export-name bytes,
locals plus scratch space, and actual body/type/export/code payload sizes.
`LeanExe/Wasm/ArithmeticBounds.lean` defines these limits using the same encoded
payloads as the production emitter. The resulting module includes the normal
allocator, reset, retain, and release bodies and all runtime exports.

For example, `def f (x y : UInt64) : UInt64 := (x + 17) * (y - 3)` is accepted.
`def f (x : UInt64) : UInt64 := let y := x + 1; y * y` is accepted. Nested bindings, shadowing, and unused UInt64 bindings are supported.
The extractor substitutes these pure, total expressions; it may duplicate their
computation or omit an unused binding's computation. Source evaluation remains
strict in the proof, and substitution preserves its result because these
expressions have no effects or divergence. Repeated bindings can expand emitted
code; the same numeric output limits apply. Other binding types follow the local-function and loop-step rules above.
For example, `if x < y then x + 1 else y / x` is now admitted. Calls to a
separate user helper remain excluded even when the normal compiler supports them.

## Compile and check

Use the pinned toolchain and runner configuration in [DEVELOPING](../DEVELOPING.md).
Build the source module before compiling its entry:

```sh
tools/leanrun --timeout 60 lake build MyModule
tools/leanrun --timeout 60 lake env .lake/build/bin/lean-wasm compile-arithmetic \
  --module MyModule --entry MyModule.f --out build/f.wasm
```

The execution driver builds the real compiler, checks source admission and
reserved export names, obtains native Lean results, and compiles the selected
declarations through `compile-arithmetic`. Node/V8 executes those emitted bytes
and compares the results. It does not use the extractor's IR evaluator as its
execution reference. Wasmtime runs the broader runtime suite.

| Command | Scope |
|---------|-------|
| `tools/arithmetic-check.js proof` | Build the general theorem and check all fourteen declared axiom dependencies. |
| `tools/arithmetic-check.js subset-engine <group>` | Compile and execute the fixed group from [the group registry](../test/arithmetic-engine-groups.json). |
| `tools/arithmetic-check.js range-engine` | Check the [registered range declarations](../test/arithmetic-range-cases.json). |
| `tools/arithmetic-check.js engine` | Check the complete [native/execution fixture](../test/ArithmeticMilestone.lean). |
| `tools/arithmetic-check.js all` | Run the general proof and complete execution comparison. |

The fixtures cover supported syntax combinations and arithmetic edge cases,
including wrapping, zero divisors, high bits, shift counts, branch choices,
captures, shadowing, and loop exits. Each execution mode retains the source
admission and reserved-export checks. The driver reports the actual declaration
and comparison counts for the chosen scope.

For a focused increment, add its fixtures to a registered group, run that group
and the general proof, and record the checked scope. Use the full or range modes
when the affected behavior requires broader coverage. Run `tools/type-safety.js check`
when changing the independent core's types, semantics or proofs; that check has
its own `propext`-only axiom rule.

Execution checks require pinned Node 24.13.0. Proof checks need Python 3, Git,
and the pinned dependencies in `proofs/talos/lean/lake-manifest.json`. Drivers
invoke Lean serially through `tools/leanrun`; do not wrap them in another runner.
Lake reuses unchanged dependencies. Logs, native results and emitted modules are
written under `.lake/arithmetic-check`, with separate `range` and `subsets/<group>`
directories for the focused modes.

## The theorem

`Project.Compiler.ArithmeticModule.Correct` in
`proofs/talos/lean/Project/Compiler/SourceCorrectness.lean` states that the exact
emitted bytes decode, the entire decoded module validates, the requested export
resolves to the user function, and every correctly sized UInt64 input list
executes to the source result in the pinned interpreter. This holds for every
host and initial store, leaves the store unchanged, and succeeds for all
sufficiently large interpreter fuel values. The proof accounts for the actual
argument-stack order and local-variable ABI.

`compileEnvironment_correct` proves admission and correctness from independent
source support, safe/total declaration lookup, export availability, and numeric
format limits. `compileEnvironment_sound` proves correctness from successful
arithmetic compilation alone. `extracted_correct` connects successful extraction
to the production `CoreWasm.moduleBytes` emitter. The final theorem is universally
quantified over admitted source programs, not restricted to the test examples.

The complete audit is `Project.Compiler.ArithmeticCompilerAudit`. All fourteen
reported declarations must have only the allowed dependencies. The runtime
retain/alloc/release proofs use only `propext`; the other audited compiler
results and the five source-equivalence/recognition results allow `propext`,
`Classical.choice`, and `Quot.sound`.

The trusted boundary includes Lean's kernel, those standard axioms, the source
semantics tied to native UInt64 operations, and the pinned Wasm decoder,
validator and interpreter definitions. It does not prove all Lean evaluation,
CLI IO/environment loading, hardware, or equivalence of every Wasm engine to
that model. The execution comparisons check those integration paths empirically.

## Independent source package

Create the general proof's source import closure and a source-only archive:

```sh
python3 tools/arithmetic-package.py create build/arithmetic-proof build/arithmetic-proof.tar.gz
```

The package contains the actual LeanExe/Project/Interpreter sources, pinned
configuration, runner (including its Mac helper), verifier, and attribution.
The manifest records source hashes, the originating commit/tree, exact target
and dependencies. It is an integrity inventory, not a signature. Record the
archive hash separately when distributing it.

Extract the archive into another directory and run its bundled verifier there:

```sh
mkdir build/arithmetic-proof-check
tar -xzf build/arithmetic-proof.tar.gz -C build/arithmetic-proof-check
cd build/arithmetic-proof-check/arithmetic-proof
python3 tools/arithmetic-package.py verify .
```

Verification checks the inventory and pins before building the bundled general
proof and auditing all fourteen results. It runs no compiler CLI or generator and
requires its own `.lake/build` to be absent. It may fetch pinned third-party
packages, or reuse them with `--dependencies /absolute/path/to/dependencies`.
Only those third-party libraries may reuse build products; all bundled proof
sources are rebuilt inside this package. `verification.log` and
`verification-result.json` record the result. A C compiler is needed by the
runner on macOS. Local execution uses the same explicit authorization and
runner environment as normal development.

## Evidence

[Compiler evidence packages](../proofs/compiler) retain checked source revisions,
theorem audit logs, native expected results, emitted modules, hashes, and the
execution scope for each recorded check. The [active task](../task.md) identifies
the checks relevant to current work. A package's results apply to its recorded
sources and bytes; its manifest identifies that boundary.
