# Early-exit range loops

Candidate `f22803ce` completes break support in the general scalar compiler
path. One bounded zero-start/unit-step range may yield, continue, or return
an updated accumulator with done. The step grammar checks scalar and step-valued
local functions separately, including both unary and Unit-prefixed shapes,
captures, joined branches, monadic bindings and unused function bodies.

Both final commands exited 0 with pinned Lean 4.34.0-rc2
(`6a10ac8c22beadecabdbb0919c2b50214762f91d`), Node 24.13.0 and authorized
local serial `tools/leanrun` execution:

- `tools/arithmetic-check.js proof`: general source-to-exact-module correctness,
  complete validation and exported invocation, with all nine axiom audits.
- `tools/arithmetic-check.js range-engine`: admission, reserved exports, and
  601 matching native Lean/V8 results across twenty-six range declarations.

The nine added declarations exercise break, update-before-break, joined binds,
captured helpers, branch updates, continue mixed with break, both step-valued
continuation shapes, and unused done-returning functions. All twenty-six exact
modules and their native expected results are retained; `verification.json`
records module sizes and hashes. Counts include zero, one and multiple iterations;
seeds include zero, one, the high bit and the maximum word.

The compiler derives value and exit-decision expressions for the same native
step outcome. It stores the decision before updating the accumulator, then
advances the index or moves it directly to the stop. Both expressions are
proved read-only for every prior flag. The four-local layout is connected to
native early-exit iteration, the actual annotated emitter, typed instructions,
complete function bytes, whole-module validation and exported execution. The
termination rank is the remaining index count; done reduces it directly to zero.
Only the permitted `propext`, `Classical.choice` and `Quot.sound` dependencies
occur in the general results; the runtime validator audits use only `propext`.

The first engine run at `3420b2f2` exposed borrowed Nat metadata on the explicit
Unit-prefixed continuation fixture. It failed before step extraction at the
strict range-head match. The retained failure, source inspection and focused
fix check record this boundary. The independent source grammar and recognizer
now preserve that annotation and check that removing only metadata yields Nat;
full ForIn instance evidence and the matching binder type remain checked.
The fixture also now exercises a yielding step before done. Unsupported unused
function bodies and custom instance evidence remain rejection tests.

The retained 120 step-level and 144 whole-function native/IR comparisons are
preparatory checks; the final gate above uses the real public compiler and V8.
The full sixty-declaration suite is configured for 1,038 results, but was not
rerun for this increment. The fixed arithmetic source archive and unrelated
independent runtime/type-safety suite were not rebuilt. Affected compiler proof
dependencies, including full type validation, were checked using cached imports.
