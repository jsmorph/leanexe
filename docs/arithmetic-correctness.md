# Arithmetic compiler correctness

The `compile-arithmetic` command admits a restricted source language covered by
a general compiler theorem. Every successful admission inherits that theorem;
users do not supply a separate proof for each program. The normal `compile`
command accepts more of the leanexe dialect, but that broader language is not
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
procedures. `>` and `≥` have their own elaborated heads, using the standard `<` and `≤`
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
conditions with exact proof domains and erased binder scope. Monadic Boolean
binds, Boolean parameters/results, and propositional combinations containing
saved Boolean locals remain separate capabilities.

Dependent `if h : condition then … else …` admits the same guard trees and
scalar/step result annotations. The extractor checks the standard decision and
both proof-lambda domains exactly. Each branch keeps an erased binder in its
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

Use the pinned Lean toolchain and the runner setup in [DEVELOPING](../DEVELOPING.md).
For an already compiled source module:

```sh
tools/leanrun --timeout 60 lake env .lake/build/bin/lean-wasm compile-arithmetic \
  --module MyModule --entry MyModule.f --out build/f.wasm
```

The repeatable execution check builds the real compiler, checks source admission
and all reserved names, compiles 143 fresh declarations with that command,
and runs their exact output modules with Node/V8:

```sh
tools/arithmetic-check.js engine
```

It is configured to compare 2,850 results against native Lean evaluation, including overflow, zero
divisors, high-bit values, shift counts 63/64/65/max and asymmetric arguments. Five declarations exercise plain, shadowed, nested,
unused, and zero-argument let bindings. Eight more cover the comparison forms,
both branches, nested choices, branch-local bindings, and conditionals inside
comparison operands. Seven further declarations cover pure return, monadic
bindings, sequential updates, early returns, nested blocks, branch-local binds
and a constant do block. Seven more cover local functions, captured values
across shadowing, calls to prior functions, nested and unused functions, joined
branches and updates after a branch.
Seven range declarations add zero/nonzero counts, indexed and index-free steps,
wrapping accumulators, in-loop bindings, conditional updates, captured values,
computations before/after the loop, and a zero-argument loop function.
Three more range declarations cover direct local-function bindings, chained
calls, accumulator capture across later updates, and unused local functions.
Three further range declarations cover monadic step bindings, nested do
computations and unused monadic values.
Four further range declarations cover joined monadic branches, mutable branch
updates followed by computation, continue, and nested branch continuations.
Nine more declarations cover breaks, updates before breaks, joined binds,
captured local functions, branch updates, continue mixed with break, both
step-valued function shapes and unused done-returning functions.
Three further declarations use direct step constructors in a callback and both
local continuation shapes, mixing yielding steps with updated done values.
Five more cover standard Nat literal bounds: zero, one, a small loop with break,
a direct callback, and the maximum representable bound with an immediate exit.
Eight further declarations cover nested step-valued Id computations, computed
pure values, result aliases, lexical captures, monadic result binds, Id-typed
lets, unused done values and multiply wrapped Id annotations.
Six more exercise a joined monadic step-result branch, functions receiving step
results, chained calls, captured values across shadowing, ignored arguments,
unused function bodies and nested Id annotations on these function types.
Nine additional scalar declarations cover inequality, negation of every
comparison family, repeated negation and negated comparisons in functions and
monadic bindings. Three more range declarations exercise break, continue and
step-result branch joins with negated conditions. Eleven further declarations
cover nonzero literal starts, dynamic and literal stops, equal/reversed bounds,
break/continue, captured helpers, joined result binds, high indices and immediate
exit from a huge interval. Eleven more cover dynamic starts: computed and
conditional endpoints, captured initial accumulators, high indices, equal and
reversed bounds, huge intervals with immediate exits, continue and result joins.
Twelve further declarations exercise literal strides: uneven distances, dynamic
endpoints, captured initial accumulators, high indices, empty ranges, maximal
steps, immediate exits, continue, result joins and an explicit unit step.
Nine new pure declarations check two-argument local functions with argument
order, captures/shadowing, chained/nested helpers, unused bodies, monadic results,
conditionals and computed arguments. Six further range declarations use these
helpers in steps with captured indices/accumulators, Id results, break/continue,
nested and unused helpers.
Expected values come from `test/ArithmeticMilestone.lean`, independently of the
extractor and IR evaluator. This check requires the repository's pinned Node
24.13.0. Wasmtime continues to run the existing runtime suite; the V8 comparison
is a separate check of the arithmetic theorem's integration with the actual CLI.

For changes confined to range loops, `tools/arithmetic-check.js range-engine`
checks the fixed range fixture group: 2,161 results across ninety-one declarations,
including local functions, monadic bindings, branch continuations and breaks. It retains admission and reserved-export
checks and saves its output under `.lake/arithmetic-check/range`. The full engine
check remains available when a change affects the broader scalar grammar.

For a narrow capability increment, `tools/arithmetic-check.js subset-engine
<checked-group>` runs the fixed declarations listed in
`test/arithmetic-engine-groups.json`. The driver and independent comparator use
the same checked membership, retain admission and reserved-export checks, and
save outputs under `.lake/arithmetic-check/subsets/<checked-group>`. Each new
capability adds its fixtures to a fixed group of relevant existing cases. The
initial `guard-core` group passed 295 comparisons across seventeen declarations.
General compiler proofs and type validation still run for each increment; evidence
records the actual execution group and counts rather than claiming a full-corpus
rerun. Broader changes can use the existing full and range modes.

Check the general proofs and all nine printed axiom dependencies with:

```sh
tools/arithmetic-check.js proof
tools/type-safety.js check
```

The proof check needs Python 3, Git and the pinned dependencies in
`proofs/talos/lean/lake-manifest.json`. Use `tools/arithmetic-check.js all` when
both proof and execution checks are affected. Commands run Lean serially through
`tools/leanrun`; do not wrap these drivers in a second runner. Lake reuses
unchanged dependencies. Logs and emitted modules are in `.lake/arithmetic-check`.
The independent type-safety check retains its `propext`-only axiom rule.

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

The complete audit is `Project.Compiler.ArithmeticCompilerAudit`. All nine
reported declarations must have only the allowed dependencies. The runtime
retain/alloc/release proofs use only `propext`; the other audited compiler
results allow `propext`, `Classical.choice`, and `Quot.sound`.

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
proof and auditing all nine results. It runs no compiler CLI or generator and
requires its own `.lake/build` to be absent. It may fetch pinned third-party
packages, or reuse them with `--dependencies /absolute/path/to/dependencies`.
Only those third-party libraries may reuse build products; all bundled proof
sources are rebuilt inside this package. `verification.log` and
`verification-result.json` record the result. A C compiler is needed by the
runner on macOS. Local execution uses the same explicit authorization and
runner environment as normal development.

Subsequent language extensions will be completed individually through source
support, production compilation, proofs and execution tests. Checks should
follow the affected dependencies, without repeating unrelated full suites.

The [2026-09-24 arithmetic checkpoint](../proofs/compiler/arithmetic-2026-09-24/README.md)
retains the completed proof, execution and type-safety checks plus the independently
verified source archive and its hash. It is a fixed arithmetic milestone; later
language extensions are tracked separately in `task.md`.

The [let-binding increment](../proofs/compiler/let-2026-09-24/README.md) extends the
general theorem and execution check to pure UInt64 bindings, with 142 matching
results over twelve declarations. It retains focused evidence without rebuilding
the fixed arithmetic distribution package.

The [conditional increment](../proofs/compiler/conditionals-2026-09-25/README.md)
adds the seven comparison forms and nested branches, with the general proof,
all nine audits, and 254 matching results across twenty declarations.

The [pure do increment](../proofs/compiler/do-2026-09-25/README.md) adds standard
Id operations, sequential updates and early returns, with all nine audits and
339 matching results across twenty-seven declarations.

The [local-function increment](../proofs/compiler/local-functions-2026-09-25/README.md)
adds lexical captures and branch continuations, with all nine audits and 437
matching results across thirty-four declarations.

The [range-loop increment](../proofs/compiler/range-2026-09-25/README.md) adds one
bounded yielding range loop, with all nine audits and 582 matching results
across forty-one declarations.

The [local functions in loop steps increment](../proofs/compiler/range-local-functions-2026-09-25/README.md)
adds direct function bindings in the yielding body, with all nine audits and
217 matching results across the focused ten-declaration range group.

The [monadic loop-step increment](../proofs/compiler/range-do-2026-09-25/README.md)
adds straight-line Id monadic bindings in the yielding body, with all nine
audits and 289 matching results across thirteen range declarations.

The [branching loop-step increment](../proofs/compiler/range-branches-2026-09-25/README.md)
adds yielding branch continuations and continue, with all nine audits and 385
matching results across seventeen range declarations.


The [early-exit range increment](../proofs/compiler/range-break-2026-09-25/README.md)
adds break and done-returning continuations, with all nine audits and 601
matching results across twenty-six range declarations. It preserves the initial
borrowed-Nat metadata failure and the checked correction. This increment ran the focused range group; the larger full suite was not rerun.


The [direct step-constructor increment](../proofs/compiler/range-direct-2026-09-25/README.md)
adds unwrapped done/yield expressions and continuations returning them, with
all nine audits and 673 matching results across twenty-nine range declarations.
All twenty-six prior range modules retained identical bytes. The 1,110-result
full suite is configured but was not rerun for this focused increment.


The [literal range-count increment](../proofs/compiler/range-count-2026-09-25/README.md)
adds bounded standard Nat literal stops, with all nine audits and 793 matching
results across thirty-four range declarations. All twenty-nine prior range
modules retained identical bytes. The full 1,230-case suite is configured;
this increment ran the focused range group.


The [step-result binding increment](../proofs/compiler/step-results-2026-09-25/README.md)
adds nested Id computations, result lets, captures and straight-line monadic
bindings, with all nine audits and 985 matching results across forty-two range
declarations. All thirty-four prior range modules retained identical bytes.
The focused source/IR test also passed 192 comparisons. The full 1,422-result
suite remains configured; this increment ran the focused range group.


The [step-result function increment](../proofs/compiler/result-functions-2026-09-25/README.md)
adds functions taking complete loop-step results and the associated branching
monadic continuations, with all nine audits and 1,129 matching results across
forty-eight range declarations. All forty-two prior modules retained identical
bytes. The focused source/IR test also passed 144 comparisons. The full
1,566-result suite remains configured; this increment ran the focused range group.


The [negative-condition increment](../proofs/compiler/negative-conditions-2026-09-25/README.md)
adds UInt64 inequality and repeated propositional negation, with all nine audits
and 1,764 matching results across the full ninety-four-declaration engine group.
All eighty-two prior modules retained identical bytes. The focused source/IR
test passed 198 comparisons. This increment used the full execution group because
the shared comparison model affects scalar expressions and range loops.


The [literal-start interval increment](../proofs/compiler/range-interval-2026-09-25/README.md)
adds nonzero starts with all nine audits and 1,465 matching results across
sixty-two range declarations. All fifty-one earlier range modules retained
identical bytes, and all 264 focused native Lean/IR comparisons passed. This
increment ran the range group; the full 2,028-result group remains configured.


The [dynamic-start increment](../proofs/compiler/range-dynamic-2026-09-25/README.md)
adds UInt64-expression starts with all nine audits and 1,729 matching results
across seventy-three range declarations. All sixty-two prior range modules
retained identical bytes; all 264 focused native Lean/IR comparisons passed.
This increment ran the range group, with the full 2,292-result group configured.


The [literal-stride increment](../proofs/compiler/range-stride-2026-09-25/README.md)
adds positive literal steps with all nine audits and 2,017 matching results
across eighty-five range declarations. All seventy-three prior range modules
retained identical bytes; all 288 focused native Lean/IR comparisons passed.
This increment ran the range group, with the full 2,580-result group configured.


The [two-argument function increment](../proofs/compiler/binary-functions-2026-09-25/README.md)
adds local scalar helpers in pure expressions and range steps, with all nine
audits and 2,850 matching results across the full 143-declaration group.
All 128 prior modules retained identical bytes. The focused tests passed 270
native Lean/IR comparisons and six rejection tests.


The [two-argument step function increment](../proofs/compiler/binary-step-functions-2026-09-25/README.md)
adds helpers returning done/yield with standard Id wrappers. All nine audits,
2,401 native Lean/V8 comparisons across 101 range declarations, 240 focused
native Lean/IR comparisons and five rejection tests passed. All 91 preceding
range modules retained identical bytes.


The [Boolean negation increment](../proofs/compiler/boolean-not-2026-09-25/README.md)
adds repeated `!` guards with checked recognition, semantics, lowering, encoding
and type validation. All nine audits, 3,298 native Lean/V8 comparisons across
165 declarations, 208 focused native Lean/IR comparisons and three rejection
tests passed. All 153 preceding modules retained identical bytes.


The [helpers surrounding ranges increment](../proofs/compiler/range-outer-functions-2026-09-25/README.md)
adds captured local functions defined before loops. All nine audits, 2,737
native Lean/V8 comparisons across 115 range declarations, 240 focused native
Lean/IR comparisons and four rejection tests passed. All 105 preceding range
modules retained identical bytes.


The [ordinary lets of loop results increment](../proofs/compiler/range-let-results-2026-09-25/README.md)
adds pure continuations after a loop-valued UInt64 binding. All nine audits,
2,977 native Lean/V8 comparisons across 125 range declarations, 240 focused
native Lean/IR comparisons and three rejection tests passed. All 115 preceding
range modules retained identical bytes.


The [UInt64 complement increment](../proofs/compiler/complement-2026-09-25/README.md)
adds direct and standard overloaded bitwise complement with proved XOR lowering.
All nine audits, 3,986 native Lean/V8 comparisons across 197 declarations,
208 focused native Lean/IR comparisons and three rejection tests passed.
All 185 preceding modules retained identical bytes.


The [compound guard increment](../proofs/compiler/compound-guards-2026-09-25/README.md)
adds nested propositional conjunction and disjunction over admitted comparisons.
All nine audits, 4,242 native Lean/V8 comparisons across 211 declarations,
256 focused native Lean/IR comparisons and three rejection tests passed.
All 197 preceding modules retained identical bytes.


The [compound negation increment](../proofs/compiler/compound-negation-2026-09-25/README.md)
adds repeated propositional Not at any level of a compound guard.
All nine audits, 4,450 native Lean/V8 comparisons across 223 declarations,
208 focused native Lean/IR comparisons and three rejection tests passed.
All 211 preceding modules retained identical bytes.


The [Boolean compound increment](../proofs/compiler/boolean-compound-2026-09-25/README.md)
adds Boolean &&/|| over UInt64 comparisons, with repeated ! at any nesting level.
All nine audits, 4,658 native Lean/V8 comparisons across 235 declarations,
208 focused native Lean/IR comparisons and three rejection tests passed.
All 223 preceding modules retained identical bytes.


The [mixed guard increment](../proofs/compiler/mixed-guards-2026-09-25/README.md)
allows compound Boolean subtrees inside propositional conjunction, disjunction
and negation. All nine audits, 4,866 native Lean/V8 comparisons across 247
declarations, 208 focused native Lean/IR comparisons and three rejection tests
passed. All 235 preceding modules retained identical bytes.


The [UInt64 min/max increment](../proofs/compiler/extrema-2026-09-25/README.md)
adds standard minimum and maximum with proved unsigned comparison/selection.
All nine audits, 5,074 native Lean/V8 comparisons across 259 declarations,
208 focused native Lean/IR comparisons and three rejection tests passed.
All 247 preceding modules retained identical bytes.


The [literal-guard increment](../proofs/compiler/literal-guards-2026-09-25/README.md)
adds Boolean and propositional literals throughout mixed guards. All nine audits,
503 native Lean/V8 comparisons in the fixed 29-declaration group, 208 focused
native Lean/IR comparisons and three rejection tests passed. The seventeen
selected preceding modules retained identical bytes. The full corpus contains
271 declarations; the preceding full execution checkpoint covers 259.


The [PUnit continuation increment](../proofs/compiler/punit-continuations-2026-09-25/README.md)
adds the unit spelling used by further generated do joins. All nine audits,
453 native Lean/V8 comparisons in the fixed 24-declaration group, 228 focused
native Lean/IR comparisons and three rejection tests passed. The twelve selected
preceding modules retained identical bytes. The full corpus contains 283
declarations; the preceding full execution checkpoint covers 259.


The [scalar Id annotation increment](../proofs/compiler/id-annotations-2026-09-25/README.md)
adds retained nested Id types to results and standard run/pure/bind operations.
All nine audits, 471 native Lean/V8 comparisons in the fixed 26-declaration group,
208 focused native Lean/IR comparisons and three rejection tests passed. The
fourteen selected preceding modules retained identical bytes. The full corpus
contains 295 declarations; the preceding full execution checkpoint covers 259.


The [finite-arity helper increment](../proofs/compiler/finite-arity-2026-09-25/README.md)
removes the two-argument limit on local scalar helpers with shared checked
parameter, application and closure rules. All nine compiler audits and all 571
native Lean/V8 comparisons across the fixed 31-declaration group passed. All 256
new native Lean/IR comparisons, four declaration rejection tests and two raw
arity rejection tests passed; the preceding helper test passes 140 comparisons
and three rejection tests after moving its three-argument case into positive
coverage. The preceding outer-helper test passes 264 comparisons and three
rejection tests after moving its equivalent case into positive coverage.
The seventeen selected prior modules retained identical bytes. The
full corpus contains 309 declarations; this was a focused execution run. Step-result
helper arities were completed in the following increment.


The [finite-arity step-helper increment](../proofs/compiler/step-finite-arity-2026-09-25/README.md)
removes the corresponding argument limit for helpers returning complete loop
results. Shared parsing and argument rules retain separate scalar/step closure
kinds and prove both the value and stop flag. All nine compiler audits and all
609 native Lean/V8 comparisons in the fixed 28-declaration group passed. All
240 new native Lean/IR comparisons, four declaration rejection tests and two
raw arity rejection tests passed. The preceding step-helper test passed 264
comparisons and four rejection tests after its three-argument case became
positive. Eighteen selected prior modules kept identical bytes. The full corpus
contains 319 declarations; this was a focused execution run.


The [dependent-conditional increment](../proofs/compiler/dependent-if-2026-09-25/README.md)
adds `if h : condition then … else …` with exact decisions and proof-lambda
domains, retaining the erased binder in each branch. All nine compiler audits
and all 623 native Lean/V8 comparisons in the fixed 34-declaration group passed.
All 304 focused native Lean/IR comparisons, four declaration rejection tests
and four proof-domain rejection tests passed. The eighteen selected preceding
modules kept identical bytes. The full corpus contains 335 declarations; this
was a focused execution run.


The [Boolean-local increment](../proofs/compiler/boolean-locals-2026-09-25/README.md)
adds ordinary Boolean lets and Boolean conditions over saved flags, keeping
Boolean and UInt64 binding kinds distinct. Scalar code, helper captures, loop
steps and outer loop bindings have checked source and extraction rules. All
nine compiler audits and all 623 native Lean/V8 comparisons in the fixed
34-declaration group passed. All 304 focused native Lean/IR comparisons, four
declaration rejection tests and four binding-kind rejection tests passed.
Eighteen selected preceding modules kept identical bytes. The full corpus
contains 351 declarations; this was a focused execution run.

The [dependent Boolean-local increment](../proofs/compiler/boolean-dependent-2026-09-25/README.md)
combines saved Boolean flags with dependent conditionals in scalar expressions,
helper captures and loop steps. All nine audits and 623 native Lean/V8
comparisons passed across a fixed 34-declaration group. The focused source test
passed 304 native/IR comparisons and ten rejection checks for unsupported
bodies, custom decisions, wrong proof domains and reads of erased binders.
Eighteen selected preceding modules kept identical bytes. The full corpus
contains 367 declarations. The retained first failure identifies a separate
literal-instance wrapper elaboration, which remains outside this checkpoint.

The [literal-instance increment](../proofs/compiler/literal-instances-2026-09-25/README.md)
handles standard numeral instances behind constant let/lambda/application and
metadata wrappers. The original captured-helper failure now passes unchanged.
All nine audits and 537 native Lean/V8 comparisons passed across a fixed
30-declaration group, with 208 focused native/IR comparisons, nine rejection
tests and one metadata check. Eighteen selected preceding modules kept identical
bytes. The full corpus contains 379 declarations. Standard Nat numeral
expressions in explicit instance arguments remain a separate next capability.
