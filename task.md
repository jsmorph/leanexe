# Scalar compiler correctness: arithmetic complete; expanding coverage

## Current instructions and status — local continuation, 2026-09-24

The user explicitly resumed work on `correct` here and authorized running Lean
locally, with frequent commits and pushes. This section supersedes the stopped
handoff below. The user removed both the separate clean-checkout requirement
and deliberate compiler/package/harness breakage checks. Do not reinstate them.
The false-equality control is also omitted from the current driver. Type-safety
checks remain explicitly requested. Continue the ordinary proof build, actual
compiler execution comparisons, standalone source proof package, and docs.

The arithmetic milestone is complete. The real compiler and Node/V8 passed all
85 comparisons across seven declarations, including source admission and all
reserved-export checks. The general proof passed all nine axiom audits. The
independent type-safety check passed its 19 behavior-test files and 438 theorem
audits. The standalone archive rebuilt all 133 bundled source modules and passed
all nine audits (3164 Lake jobs). These results use candidate `878cfd1e` and are
preserved in `proofs/compiler/arithmetic-2026-09-24/`, including the exact archive,
emitted modules, native expected results, logs and verification metadata.

Completed next increment: pure UInt64 `let` bindings, including nested bindings,
shadowing, unused bindings and zero-argument declarations. Candidate `d777caf2`
passed the full general source-to-byte compiler theorem and all nine axiom
audits, plus all 142 native Lean/Wasm comparisons over twelve declarations.
Source admission and all reserved exports also passed. The increment's evidence
is in `proofs/compiler/let-2026-09-24/`. The extractor substitutes only pure total
arithmetic expressions; this preserves source results but can expand emitted
code/repeat computations. No type-safety implementation changed, so its prior
438-theorem audit was not repeated.

Completed next increment: UInt64-valued conditionals over `=`, `<`, `≤`, `>`,
`≥`, `==`, and `!=`, with exact standard instance and decision evidence.
Candidate `b06b8e12` passed the general proof and all nine axiom audits, plus
254 native Lean/Wasm comparisons over twenty declarations. Static bounds cover
both branches; nested choices and branch-local bindings are included. The first
execution attempt exposed distinct `GT.gt`/`GE.ge` heads, which were then added
and proved before repeating the checks. Evidence is retained in
`proofs/compiler/conditionals-2026-09-25/`.

Completed next increment: standard pure `Id.run do` operations, UInt64 monadic
bindings, straight-line updates, early returns, nested blocks and branch-local
binds. Candidate `140ce818` passed all nine general compiler axiom audits and
339 native Lean/Wasm comparisons across twenty-seven declarations. Evidence is
retained in `proofs/compiler/do-2026-09-25/`. Complete standard Id instance
expressions are checked; no backend emission changes were needed.

Completed next increment: local UInt64 functions, lexical captures and the
continuations introduced by joined `do` branches and branch updates. Candidate
`d73e047d` passed all nine general compiler axiom audits and 437 native Lean/Wasm
comparisons across thirty-four declarations. Evidence is retained in
`proofs/compiler/local-functions-2026-09-25/`. The source model distinguishes
word/Unit/function bindings internally while preserving the public scalar ABI.
All function bodies are checked, including unused ones. Plain unary functions
and the `Unit → UInt64 → result` update-continuation form have distinct binding
kinds. Other arities and top-level helpers remain outside this increment.

Completed next increment: one bounded `[:count.toNat]` range loop with a UInt64
accumulator and yielding steps. Candidate `f4ffe0e0` (proof sources from
`d1fbcaf7`) passed all nine general compiler axiom audits and 582 native Lean/V8
comparisons across forty-one declarations. Source admission and reserved-export
checks passed. Evidence is retained in `proofs/compiler/range-2026-09-25/`.
The proof connects native ascending range iteration to source extraction,
ordinary scalar IR, the actual annotated emitter, exact complete module bytes,
validation and exported execution. It covers zero iterations, explicit
UInt64.ofNat index conversion, wrapping accumulators, step bindings and scalar
conditional updates, captures and pure computations before/after the loop.
The loop uses three fresh locals and the remaining iteration count as a
termination measure. Constant bounds currently use a UInt64 value followed by
.toNat. Breaks, continue, other range starts/steps, multiple accumulators and
multiple/nested loops remain outside this increment. Focused dependency builds
and cached general checks were used; the fixed arithmetic archive and unrelated
438-theorem type-safety suite were not rebuilt.

Completed next increment: direct local-function bindings in the yielding loop
body. Candidate `430802eb` passed all nine general compiler axiom audits and
217 native Lean/V8 comparisons across ten range declarations, with source
admission and reserved-export checks. Evidence is retained in
`proofs/compiler/range-local-functions-2026-09-25/`. The yield wrapper preserves
binding types and order; the scalar extractor checks all bodies, including
unused functions. Captures retain the accumulator value from the binding point
even across later updates. Unsupported bodies and arities remain rejected.
The fixed range test group avoids recompiling unchanged arithmetic fixtures.

Completed next increment: standard Id monadic UInt64 bindings (`let x ← …`)
inside yielding loop steps. Candidate `728098c4` passed all nine general compiler
axiom audits and 289 native Lean/V8 comparisons across thirteen range declarations,
with source admission and reserved-export checks. Evidence is retained in
`proofs/compiler/range-do-2026-09-25/`. The source relation preserves the exact
standard Bind evidence; the scalar grammar checks each bound value and
continuation. Nested do computations and unused monadic values are included.
The first execution attempt exposed a distinct branching-continuation form;
that failure is retained. Conditional scalar values inside pure are supported,
while custom Bind evidence and breaks after a bind remain rejected.

Completed next increment: yielding branch continuations in range steps.
Candidate `1cfb4228` passed all nine general compiler axiom audits and 385
native Lean/V8 comparisons across seventeen range declarations, including
source admission and reserved-export checks. Evidence is retained in
`proofs/compiler/range-branches-2026-09-25/`. The independent YieldType relation
preserves function domains and binder information while removing the yielding
result wrapper. Syntax conversion handles continuation types/bodies and both
branches together, while the scalar extractor checks the full result. Joined
monadic branches, mutable branch updates followed by computation, nested
branches and continue now work end-to-end. The previously rejected monadic join
is an explicit passing fixture. Breaks, unused done-returning functions, and
custom comparison evidence remain rejected.

In progress: break in range loops. `Source/ScalarRangeExit.lean` proves bounded
early-exit iteration agrees with native List/range ForIn behavior, including
the accumulator produced by done. The existing yielding iteration is proved
to be a special case. `IR/ScalarIterationExit.lean` proves finite while
execution for either advancing the index or moving it directly to the bound
after done. Both focused targets pass. Source extraction, the actual local-slot
layout, emitted control flow, general proofs and execution tests remain pending;
the public compiler still rejects break while this capability is developed.
The concrete four-local layout now has checked reads/writes, decision staging,
accumulator updates, index advance/exit and complete IR loop execution in
`IR/ScalarRangeExitSlots.lean`. The exit decision is evaluated before changing
the accumulator; done moves the index to the stop, and yield increments it.
The focused target passes, including zero iterations and the returned done
accumulator in the universally quantified statement.

Current checkout: `/Users/jamiestephens/Documents/Codex/2026-09-24/get/leanexe`.
Local Lean is the pinned 4.34.0-rc2 toolchain; Node is 24.13.0. All Lean commands
continue through `tools/leanrun`, with local mode and a shared serial lock.
The old Linux recovery paths below are historical. After this arithmetic milestone, the user requests incremental expansion to
full leanexe dialect coverage: one capability working through compilation,
proofs, and execution tests before starting the next. Begin with strict `let`,
then conditionals, `do`, and loops as their dependencies permit. Report, commit,
and push each useful step frequently. Type definitions and proofs may change
where needed; preserve their justified guarantees, not their incidental shape.
Use focused checks and Lake's dependency rebuilds, avoiding repeated full builds.
Keep the arithmetic source archive as a fixed milestone. Do not regenerate it
or rerun unrelated full runtime suites for each subsequent feature; check the
changed source/compiler/proof dependencies and that feature's execution cases.

---

# Scalar compiler correctness: INCOMPLETE — work stopped by user

## Authoritative handoff — 2026-09-25 UTC / 2026-09-24 America/Chicago

The user's last instruction is to finish this handoff, commit and push, and do
nothing else. **Do not resume implementation, dependency installation, builds,
or tests without a new instruction to resume.** Only documentation and its
commit/push are authorized at this stopping point. This section supersedes
historical status and next-step statements in the journal below. Preserve the
journal as history; its earlier statements that particular results are missing
are not descriptions of the current code.

### What exists and what does not

Repository: `jsmorph/leanexe`. Working branch: `correct`, originally based on
`typesafety` at `834ba204d84720e00deef9b4ce476d4a04e55ff4`. Do not change `main`
or `typesafety`. The separate backend/manual-certificate implementation was
removed earlier (commit `7243e727`); do not restore it as a substitute for this
task. Every admitted source program must inherit the same general theorem.

**Checked and pushed:** the general arithmetic source-to-exact-Wasm-module
compiler theorem, source acceptance theorem, successful-admission soundness
theorem, full module validation, and axiom audit. Their commit is
`5dfcd8f5d42ab945258970f605c7f22e096fa7df` (tree
`9e4ceb98a54c79de6244aceab0fb29109c4c6e79`). The proof build finished successfully
with 3166 jobs before the latest workspace loss. The final general compiler
theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

**Not complete:** the arithmetic milestone's final executable/reproducibility
gates and documentation. The larger scalar language agenda is also incomplete.
Do not say the milestone or the whole compiler is certified/completed on the
strength of the checked theorem alone. Use the exact scope and pending gates
below in status reports.

This handoff commit also preserves three gate files already reconstructed and
locally checkpointed before the stop instruction:

- `tools/arithmetic-check.js`: proof/audit/negative-control and CLI/engine driver.
- `test/ArithmeticMilestone.lean`: fresh source declarations and native Lean
  expected results.
- `test/arithmetic_engine.mjs`: independent Node/V8 WebAssembly comparator.

**These reconstructed gate files have not completed a verification run.** A
previous, subsequently lost version passed its proof/audit and kernel-negative
steps. Its native CLI build was still running at the last observed output;
there is no confirmed CLI/engine result. The standalone package script and draft
archive were not pushed before maintenance and are lost. Recreate that script
from the requirements below; do not claim an existing verified package.

### Exact arithmetic contract

The input is the original elaborated `Lean.Expr` body and type of an environment
declaration, not hand-written IR or a program-specific proof certificate. The
declaration must have an executable body, be safe and total, and use an export
name outside the ten reserved runtime names. Independent source support covers:

- Zero or more `UInt64` arguments and one `UInt64` result.
- Argument reads, metadata, literals (including literals reduced modulo 2^64),
  and arbitrary finite nesting of addition, subtraction, multiplication,
  unsigned division/remainder, bitwise and/or/xor, and left/right shifts.
- Direct UInt64 primitive heads and canonical elaborated overloaded heads with
  their exact standard instance evidence, including canonical UInt64 `OfNat`.
- Native UInt64 semantics: modular arithmetic, division by zero returns zero,
  remainder by zero returns the dividend, and shift counts are masked.

Source lets, branches, helper calls, recursion/loops, custom typeclass instances,
runtime Nat, heap values, allocation, imports, mutable globals, and floats are
outside arithmetic admission. Some compile through the general compiler; that
does not put them under the arithmetic theorem. The production output still
contains its actual allocator/reset/retain/release functions and ten runtime
exports; their validation is included. Do not replace the output with a smaller
module to avoid proving these obligations.

Admission checks explicit numeric WebAssembly format limits. In
`LeanExe/Wasm/ArithmeticBounds.lean`, `Fits func entry` bounds by 2^32 the parameter
count, result count, UTF-8 export-name length, locals plus scratch count, actual
encoded user-body payload length, and actual type/export/code payload lengths.
These are executable size checks, not assumptions that generated code is
correct. The body payload includes local declarations, actual emitted user
instructions, and the final end byte. The shared payload definitions are used
by both admission and the layout proofs.

### Public theorem and implementation map

Proof paths in this paragraph are relative to `proofs/talos/lean/`.
`Project/Compiler/SourceCorrectness.lean` defines
`Project.Compiler.ArithmeticModule.Correct α source entry arity bytes`:

```lean
∃ raw, Wasm.Binary.decode bytes = .ok raw ∧
  Validator.validateRaw raw = .ok () ∧
  (Translation.module raw).findExport entry = some 0 ∧
  ∀ (args : List UInt64), args.length = arity →
    ∀ (host : Wasm.HostEnv α) (store : Wasm.Store α),
      ∃ value : UInt64, LeanExe.Source.Scalar.Apply source [] args value ∧
        ∃ N, ∀ fuel ≥ N,
          Wasm.run fuel (Translation.module raw) 0 store
            (args.map Wasm.Value.i64).reverse host = .Success [.i64 value] store
```

The module decodes and validates, the requested export resolves to function 0,
and for every input, host and store the invocation terminates with the original
source result and unchanged store. The reversed argument stack is the actual
interpreter calling convention, with source declaration order restored in locals.
Fuel is an interpreter parameter: the result holds for every sufficiently large
fuel, not merely for one selected execution bound.

The public theorems in that namespace are:

| Theorem | Premises and conclusion |
| --- | --- |
| `extracted_correct` | Successful actual scalar extraction, available export name, and `Fits` imply `Correct` for the exact production `CoreWasm.moduleBytes { funcs := #[func] }`. |
| `compileEnvironment_correct` | Original environment lookup/body, safe/total declaration, exportable name, independent `DeclarationSupported`, and explicit format limits imply both normal and arithmetic compilation succeed with the same module, and its exact bytes satisfy `Correct`. |
| `compileEnvironment_sound` | A successful `LeanExe.Extract.Arithmetic.compileEnvironment` result alone yields the original declaration/body and `Correct` for that output's exact bytes. There is no caller-supplied semantic or correspondence certificate. |

The acceptance theorem's limits premise is
`∀ func, extractScalarFunc ... = some func → Fits func entry`; it only states
the numeric bounds on the extractor's result. The admission code checks those
bounds. Source support is defined independently, not as compilation success.

| Repository path | Role |
| --- | --- |
| `LeanExe/Source/Scalar.lean`, `ScalarHead.lean`, `ScalarFunction.lean` | Independent expression/declaration syntax and source application semantics tied to native UInt64 operations. `DeclarationSupported` uses `Arrow`, lambda collection, and source `Supported`. |
| `LeanExe/Extract/ScalarPrimitive.lean`, `ScalarExpr.lean`, `ScalarFunc.lean` | Actual primitive/expression/function extraction; preservation, acceptance, and success-implies-support proofs; real result-slot ABI. |
| `LeanExe/Extract/Core.lean` | Existing normal `compileEnvironment` uses the proved scalar fast path before the general extractor; all ten reserved export names are checked. |
| `LeanExe/Extract/ScalarEntryCorrectness.lean` | `compileEnvironment_of_scalar_extraction` connects successful extraction to the actual normal compiler and its exact single-function IR module. |
| `LeanExe/Extract/Arithmetic.lean` | Strict source admission and size checks, followed by a call to the existing normal compiler. Its IO wrapper uses the existing environment loader. |
| `LeanExe/Extract/ArithmeticCorrectness.lean` | `compileEnvironment_accepts`, `compileEnvironment_success`, and supporting admission proofs. |
| `LeanExe/CLI.lean` | `compile-arithmetic --module ... --entry ... --out ...`; calls strict admission and the production module emitter. |
| `LeanExe/Wasm/Binary.lean`, `LeanExe/Wasm/Image/Emit.lean` | Actual instruction and module byte emitters; no alternate proof-only emitter. |
| `LeanExe/Wasm/ArithmeticBounds.lean` | Executable format bounds and shared actual payload definitions. |
| `proofs/talos/lean/Project/Compiler/SourceFunctionBytes.lean`, `SourceModuleBytes.lean`, `ModuleInvocation.lean`, `SourceInvocation.lean` | Generic source/IR/instruction/byte/execution composition and actual argument/local ABI. |
| `proofs/talos/lean/Project/Compiler/ArithmeticModuleBytes.lean` | Exact full six-section production module bytes and decoder connection; actual runtime bodies and exports included. |
| `proofs/talos/lean/Project/Compiler/FunctionTyping.lean`, `SourceFunctionValidation.lean`, `MetadataValidation.lean`, `ModuleValidation.lean` | User instruction/function validation, full module metadata/exports/lengths, and composed actual validator result. |
| `proofs/talos/lean/Project/Compiler/RuntimeValidation.lean`, `RuntimeRetainValidation.lean`, `RuntimeAllocValidation.lean`, `RuntimeReleaseValidation.lean` | Validation of the fixed actual runtime functions for arbitrary admitted user code and export name. |
| `proofs/talos/lean/Project/Compiler/SourceCorrectness.lean`, `ArithmeticCompilerAudit.lean` | Final compiler theorems and nine dependency audits. |

The axiom audit prints admission acceptance/success, three large runtime
validation results, full module validation, extracted correctness, and both
public compiler theorems. The final theorem whitelist is exactly the three
standard axioms above. Runtime retain/alloc/release proofs use only `propext`.
The independent `LeanExe.TypeSafety` policy remains **propext only**; never
broaden that policy to match the compiler theorem's dependencies.

The trusted boundary includes Lean's kernel and these standard axioms, the
specified source semantics and pinned Wasm interpreter/decoder/validator model.
The source rules explicitly use native Lean UInt64 operations; this is not a
proof of the whole Lean evaluator. The theorem does not kernel-prove CLI IO,
environment-file loading, Node/V8, hardware, or equivalence of the Wasm model to
every engine/specification implementation. The real CLI/engine gate checks that
integration independently. State these limits alongside the positive theorem.

### Resume procedure and environment recovery (do not execute until resumed)

The transient workspace has been removed twice during this session, including
checkout, installed Lean, unpushed gate work, and logs. GitHub commits survived.
Do not rely on a local path or a prior process still existing. Inspect current
Git state first; preserve any unpushed work. If a checkout is gone, clone into a
new directory rather than overwriting a surviving tree:

```bash
git clone --branch correct --single-branch https://github.com/jsmorph/leanexe.git leanexe-resume
cd leanexe-resume
git status --short
git rev-parse HEAD
```

At this handoff the restored checkout is
`/workspace/scratch/d899a1fad5ce/leanexe-recovered`; the older sibling `leanexe`
is a pruned remnant and must not be used. Lean was restored to
`/workspace/scratch/d899a1fad5ce/toolchains/lean-4.34.0-rc2-linux`; proof
dependencies/caches have not been restored after the latest loss. No Lean job
is running at the stop point. These paths are conveniences, not durable inputs.

Read `AGENTS.md` in the recovered checkout. All Lean/Lake/compiler execution
must go through `tools/leanrun`, serially under its shared machine lock. The
user already authorized local execution: `LEANRUN_LOCAL=1` is permitted and
does not require asking again. It retains pinning/locking/timeouts/thread
limits; it does not enforce the standard systemd memory/CPU cgroup limits.
Do not spawn agents without authorization. Provide progress updates at least
every minute while actively working and announce every successful push with
its remote SHA. Commit and push useful checkpoints before long operations,
even when the checkpoint is an explicitly labeled unverified draft.

Pinned Lean: `leanprover/lean4:v4.34.0-rc2`, compiler commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`. If missing, the Linux release archive
is at:

`https://github.com/leanprover/lean4/releases/download/v4.34.0-rc2/lean-4.34.0-rc2-linux.tar.zst`

It is approximately 553 MiB. Extract with
`tar --no-same-owner --zstd -xf <archive> -C <toolchain-parent>`; omitting
`--no-same-owner` previously caused extensive ownership errors. Use absolute
paths in the following environment variables and keep the same lock path
across original checkout, clean checkout, and standalone package runs:

```bash
export LEANRUN_LOCAL=1
export LEANRUN_TOOLCHAIN=/absolute/path/lean-4.34.0-rc2-linux
export LEANRUN_LOCKDIR=/absolute/path/shared-leanrun-lock
tools/leanrun --timeout 30 lean --version
```

Do not repurpose `HOME` or `CODEX_HOME`. Do not call raw `lean`/`lake` or wrap
runner-calling drivers in another `tools/leanrun`: nested calls deadlock on the
same non-reentrant lock and the local runner rejects them.

The proof dependencies are pinned in `proofs/talos/lean/lake-manifest.json`.
Root LeanExe has no external package dependencies. Key proof dependency pins:

| Package | Revision |
| --- | --- |
| CodeLib / talos | `87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47` (codelib subdirectory; interpreter in the same checkout) |
| iris | `e7a0a43814c4f1154ca0c8049883ca56c2288b86` |
| mathlib | `85e3a25e006c35636f0e53b0e9296caca2685bc0` |

Use the manifest for exact Qq/batteries/plausible/LeanSearchClient/importGraph/
proofwidgets/aesop/Cli pins. Let Lake fetch the pinned dependencies, or, if
recovery requires manual fetching, read each git entry's URL/revision from the
manifest, initialize `proofs/talos/lean/.lake/packages/<name>`, fetch that exact
revision with depth 1 and check out `FETCH_HEAD`. Respect each entry's subDir.
Independent Git downloads may overlap; Lean processes may not. Do not update
the manifest to newer versions to fix recovery problems.

The focused third-party cache command is:

```bash
tools/leanrun --timeout 900 lake -d proofs/talos/lean exe cache get Mathlib.Tactic Mathlib.Data.Nat.Bitwise Mathlib.Data.List.Sort
```

Earlier cache requests needed roughly 3000 files and several minutes; short
180/300-second attempts timed out after partial downloads. Split remaining
imports/cache work rather than repeatedly rerunning an unchanged timeout.
Third-party caches are allowed for release gates, but the repository's own
LeanExe/Project/Interpreter proof artifacts must be rebuilt from source in the
clean and standalone gates. Never count a download timeout as a failed proof
or a partially completed build as a successful proof.

### Remaining gate 1: actual CLI and independent engine

After a resume instruction, start with the reconstructed driver and fix any
real errors it exposes. It is currently a draft, not accepted evidence:

```bash
tools/arithmetic-check.js engine
```

The driver directly invokes `tools/leanrun` for these stages: native
`lake build lean-wasm` (600-second bound), strict admission regression,
fixture compilation, native Lean evaluation, and the real `compile-arithmetic`
CLI for every fixture entry. Then Node/V8 validates, instantiates, and invokes
the requested exports from those exact `.wasm` files and compares results to
native Lean. The driver itself must not be wrapped in `tools/leanrun`.

Expected fixture set: `constant`, `wrapping`, `quotient`, `remainder`, `shifts`,
`nested`, and `order` in `ArithmeticMilestone`. Fourteen argument pairs for
each two-argument function and one constant result yield **85 comparisons over
seven fresh, unregistered declarations**. Inputs include zero, maximal UInt64,
high-bit values, overflow, zero divisors, shifts by 63/64/65/max, and asymmetric
arguments to detect reversed ABI order. The nested fixture uses all ten
operations. Read the committed fixture for the exact pairs and expressions.
Expected results come from native Lean, not the extractor/IR evaluator.

Logs and artifacts are written under `.lake/arithmetic-check/`:
`<stage>.log`, `<stage>.stderr.log`, `expected.jsonl`, each entry's `.wasm`, and
`engine.log`. The driver captures subprocess output to files and reports stage
completion; it does not continuously print Lean output. While a long stage is
running, read its log and communicate status without launching another Lean
process. Native `Extract.Core:c.o` alone previously took roughly 56 seconds;
a cold native build is materially slower than proof elaboration.

Pass means every stage exits successfully, every module is accepted by V8,
the requested exports exist, and all 85 source/engine results match. Do not
claim a pass from only successful source evaluation or an executable build.
The admission regression in `test/arithmetic_mode.lean` previously passed:
arithmetic/bits/overflow literals match the normal compiler's exact bytes;
lets/branches/helpers/custom instances/wrong types/reserved/missing entries
are rejected; a 2^32 parameter-count check rejects before allocating a huge
type vector. Preserve this behavior and rerun it through the driver.
`test/arithmetic_reserved_exports.lean` separately checks all ten runtime
names, internal functions and ordinary entries; it also previously passed.

For a focused manual CLI diagnostic after fixture compilation, use:

```bash
tools/leanrun --timeout 60 lake env .lake/build/bin/lean-wasm compile-arithmetic --module test.ArithmeticMilestone --entry ArithmeticMilestone.nested --out /absolute/path/nested.wasm
```

### Remaining gate 2: final proof/audit and clean checkout

The focused checked target and the draft automated gate are:

```bash
tools/leanrun --timeout 900 lake -d proofs/talos/lean build Project.Compiler.ArithmeticCompilerAudit
tools/arithmetic-check.js proof
```

Use the driver for the gate, the direct command for a focused diagnostic; do
not run both unnecessarily. The driver audits both final compiler theorem
names against the three-axiom whitelist and runs
`test/negative/arithmetic_kernel.lean`. This intentionally false equality must
fail with `(kernel) declaration type mismatch`; failure caused by a missing
import, timeout, syntax error, or unrelated issue is not a valid negative
control. Audit parsing must handle whitespace/newlines inside the printed
axiom list. Review all nine printed declarations, even though the draft driver
automatically checks only the two final public theorems.

Create a new checkout of the final candidate commit. Record its SHA and clean
Git state. Use only pinned third-party caches; do not copy this repository's
`.lake/build` products. Build the proof/audit from that checkout and run the
CLI/engine gate against its own executable/source. This gate is not satisfied
merely by restoring a previously built checkout. Cold proof builds previously
took several minutes; warm final SourceCorrectness/audit builds took about
3.4/2 seconds. A timeout during many progressing dependency jobs is not proof
completion. After a timeout inspect and reduce the work boundary before retry.

### Remaining gate 3: standalone independently checkable proof package

No verified standalone arithmetic package exists yet. A draft packaging script
was lost before push; recreate it as a repository tool (suggested path
`tools/arithmetic-package.py`) and push its draft before running a long build.
The package must contain the general compiler theorem and actual definitions,
not a generated theorem for selected example programs. Verification must not
execute the compiler CLI or a proof/artifact generator.

The previously computed source import closure of
`Project.Compiler.ArithmeticCompilerAudit` contained 133 Lean source modules:
73 Project, 43 LeanExe and 17 Interpreter. Recompute, do not hardcode these
counts. Resolve imports from these three source roots:

1. Repository root for LeanExe modules.
2. `proofs/talos/lean` for Project modules.
3. `proofs/talos/lean/.lake/packages/CodeLib/interpreter` for Interpreter modules.

Copy sources by module path into a new standalone directory. Parse imports
properly, including `public import` and multiple modules if present; fail on
unresolved nonstandard dependencies. The previous closure's external roots
were `Init.Data.ByteArray.Extra`, `Init.Data.ByteArray.Lemmas`,
`Init.Data.Nat.Lemmas`, `Init.Data.String.Basic`, `Init.Omega`, `Lean`,
`Lean.Data.Json.Printer`, `Mathlib.Tactic`, and `Mathlib.Tactic.Ring`. It required
neither the CodeLib library nor iris code. Check this again against final
sources rather than silently dropping an unfamiliar import. Include dependency
license/attribution material when redistributing the Interpreter sources.

Copy the exact `lean-toolchain` and `tools/leanrun`. A minimal standalone
`lakefile.toml` can use:

```toml
name = "ArithmeticCompilerProof"
version = "0.1.0"
[[require]]
name = "mathlib"
scope = "leanprover-community"
git = "https://github.com/leanprover-community/mathlib4"
rev = "85e3a25e006c35636f0e53b0e9296caca2685bc0"
[[lean_lib]]
name = "LeanExe"
[[lean_lib]]
name = "Interpreter"
[[lean_lib]]
name = "Project"
```

Derive its `lake-manifest.json` from the pinned proof manifest: set the package
name; retain pinned git dependencies except CodeLib/iris; remove path
dependencies; set mathlib `inherited` false and its `inputRev` to the exact
revision; keep other dependencies inherited and retain their exact revisions.
Verify the resulting closure rather than accepting extraneous path references.

Add `proof-package.json` with a versioned schema, exact audit target, pinned
toolchain/dependency identities, and SHA-256 hashes of all bundled source,
configuration, runner, verifier and README files. Verify paths stay within the
package, reject missing/changed/extra executable or source inputs, and reject
unknown schemas/targets/pins. The manifest is an integrity inventory, not an
authenticated signature; record the final archive hash outside the archive.

The verifier must first validate the manifest, then require the package's own
`.lake/build` to be absent, and run:

```bash
tools/leanrun --timeout 900 lake build Project.Compiler.ArithmeticCompilerAudit
```

Capture full output in `verification.log` and perform the same final theorem
axiom audit. Ordinary kernel reduction of compiler definitions inside proofs
is expected; invoking the CLI or a generator to produce missing proof sources
is prohibited in this gate. A package may use pinned third-party caches in an
external dependency directory; it must not load original-checkout LeanExe,
Project or Interpreter source/olean files. Prefer verification in an isolated
directory where the original checkout is not a source-search dependency.

Produce a source-only `.tar.gz` with no build/cache/log files. Extract that
archive into a second new directory and verify it there. Record archive SHA-256,
originating commit, exact verification command/environment, successful output,
and axiom audit. The earlier approximately 326 KiB draft archive is lost and
was never verified; no hash or result from it counts for this gate.

### Remaining gate 4: meaningful deliberate mutations

Implement a repeatable mutation driver in isolated checkouts/copies. Never
mutate the live baseline branch in place. Require each replacement to match
the intended production occurrence exactly once, verify a passing baseline,
invalidate/rebuild affected modules and dependents, and restore the baseline
between cases. A mutation is detected only when the intended semantic,
correspondence, validation or manifest check rejects it. Missing dependencies,
timeouts and incidental syntax errors are inconclusive. Save every log and
the exact mutation diff.

Candidate concrete mutations to implement and verify against current source:

| Boundary | Deliberate change | Expected rejecting check |
| --- | --- | --- |
| Source admission | Change a fresh accepted source declaration to contain a let, branch, helper call, or custom arithmetic instance. | Real arithmetic CLI rejects unsupported source; no output is reported certified. Existing admission regressions provide the source patterns. |
| Extractor operator | In `LeanExe/Extract/ScalarPrimitive.lean`, change production `toIR` case `\| .add => .add` to subtraction. | General `denote_toIR`/`lower_correct` proof fails when building that module. |
| IR literal | In `LeanExe/Extract/ScalarExpr.lean`, change the direct `UInt64.ofNat` literal branch from `some (.u64 n)` to `some (.u64 (n + 1))`. | General extraction preservation/literal proof fails. |
| Opcode | In `LeanExe/Wasm/Image/Emit.lean`, change `.addI64` byte 124 to 125. | Actual byte/instruction correspondence (`Project.Compiler.ArithmeticEncoding` or full audit dependency) fails. |
| Runtime call | In `LeanExe/Wasm/Binary.lean`, change `let callReleaseChild := localGet childLocal ++ call releaseIndex` to call `releaseIndex + 1`. | Runtime release validation or an earlier actual-byte correspondence proof fails; index 5 is invalid in the five-function arithmetic module. |
| Export | In production `exportSection`, change `exportEntry exportName 0 item.fst` to use `item.fst + 1`. | Actual export-section/full-module correctness proof fails. |
| Argument ABI | In `extractScalarFunc`, remove `.reverse` from `extractScalarExpr (List.range arity).reverse body` without changing its specification. | General source-application/function correctness proof fails; asymmetric real-engine fixture can also expose it. |
| Package manifest | Change audit target or pinned dependency, or alter a bundled source without updating its recorded checksum. | Standalone verifier rejects before Lean runs, for the intended target/pin/hash error. |

Also corrupt one expected native result or engine input to confirm the
comparison harness rejects a mismatch; label this a harness check, not a
compiler proof. Manifest mutations must distinguish content corruption from
authentication: an attacker replacing both sources and inventory requires the
externally recorded archive hash to detect substitution.

### Remaining gates 5 and 6: policy, documentation, final evidence

Run the existing independent policy gate serially:

```bash
tools/type-safety.js check
```

It builds `LeanExe.TypeSafety`, runs its existing behavioral regressions and
audits its theorem dependencies under the original **propext-only** whitelist.
It has not been run in this continuation. Do not weaken its policy to pass a
changed implementation. Its success does not replace the arithmetic theorem
or the arithmetic gates.

Update user-facing documentation with the exact source grammar, numeric limits,
CLI examples, actual theorem statements and locations, admitted/rejected
examples, independent engine/package procedures, trust boundary, and excluded
features. Make all drivers fail clearly on errors and document prerequisites
(Git, pinned Lean/Lake, Node supporting i64 BigInt WebAssembly, Python 3 for the
planned package tool, and tar/zstd for toolchain recovery).

For each final gate record the tested commit/tree, toolchain/compiler and Node
versions where relevant, exact command, exit status, meaningful result counts,
audit output, and durable log/artifact location. Preserve evidence in Git or
another explicitly selected durable destination before relying on it; local
scratch logs have already been lost twice. Do not check in dependency caches
or large build trees. Any fix after a passing gate requires rerunning the
affected gate on the final candidate; prior results may be retained as history.

Arithmetic completion requires all of: general acceptance/soundness and full
byte/export invocation theorem; strict usable admission; successful actual CLI
and 85 independent-engine comparisons; clean-checkout proof and executable
gates; isolated package verification with recorded archive hash; meaningful
mutation rejections; unchanged TypeSafety policy passing; accurate docs and
durable evidence; all final changes committed and pushed to `correct`.
Do not ask the user to supply semantic or correspondence proofs for their
programs. The theorem is already general; examples test integration, not its
mathematical quantification.

### Known proof/performance issues already resolved

`Project/Compiler/KernelReduction.lean` defines `kernel_rfl`. It constructs an
ordinary `Eq.refl` proof for the equality target's left side and assigns it;
the declaration kernel must check definitional equality with the claimed
right side. It does not use `native_decide`, a new axiom, or unchecked declaration
insertion. `test/negative/arithmetic_kernel.lean` attempts `0 = 1` and was
rejected by the kernel with a declaration type mismatch. Keep this negative
control as an expected failure, not in a positive-only regression list.

The three large actual runtime validators use `by kernel_rfl`; the reset
validator uses `rfl`. They checked in approximately 3.5–3.7 seconds each with
only `propext`. Earlier elaborator `rfl` hit 200000 heartbeats, and broad `simp`
timed out at 90 seconds. Do not repeat those unchanged experiments or raise
limits to hide the elaboration boundary. Runtime/metadata imports were narrowed
to actual module bytes plus the binary validator, avoiding an unnecessary
SourceInvocation dependency. Root `ArithmeticBounds` payload definitions are
shared by proof layout abbreviations; some simplification needs the explicit
root definitions. These fixes are already in checked commits.

The actual runtime indices are user 0, allocator 1, reset 2, retain 3,
release 4; the free export aliases release. All ten reserved runtime exports
must be excluded for the user entry; an earlier duplicate-export bug was fixed
and checked. Do not regress to checking only a subset of reserved names.

Useful checked commit anchors:

- `cb26c4948c17ce10c0c5807badba6cd4c821e0ba`: reserved runtime export fix/regression.
- `62cb863e3d105f98d11604925c1aed8682492929`: module metadata validation.
- `1464f53b1ae83843f4172df1eadba2dda6c7c0bb`: strict admission/format limits.
- `c9e71b6c955e246ccb7d27f97e5f98f6ddccdc50`: admission proofs and arithmetic CLI.
- `a465dbf9c6f2c8ba25840de50a6d26d31aa56a3b`: shared format payloads/import reduction.
- `9caa5a6c723bb064f326640589e85cb7bfc6698b`: all runtime validation and kernel negative control.
- `5dfcd8f5d42ab945258970f605c7f22e096fa7df`: final generic arithmetic compiler theorem and audit.

The reconstructed gate files were locally checkpointed as `5d55b78d` before
this handoff; the remote handoff commit includes them. Treat their verification
status as draft regardless of their presence in Git.

### Deferred full scalar agenda after arithmetic completion

The original agreed scope remains concrete Wasm scalar values: UInt64 inputs
and results, internal Bool, modular arithmetic, unsigned comparisons, bit
operations/masked shifts, strict bindings, branches, acyclic scalar helper
calls, and explicitly supported terminating structured iteration. Runtime Nat,
heap objects, imports, mutable globals and allocation remain excluded.
Proof-level Nat and explicit source termination arguments are permitted.
The user's priority is to finish arithmetic completely before extending it.

For each extension, first define independent source syntax, typing, semantics
and termination/ABI conditions; update executable admission with explicit
unsupported-form errors; prove extraction acceptance and preservation; prove
the actual IR/lowering/encoding/validation/invocation steps used; then extend
the one general compiler theorem. Maintain source-meaning independence and
the actual normal production compiler/emitter path throughout.

1. Strict scalar bindings: correct evaluation order, scope/local indices and
   result-slot preservation through extraction and stack/local lowering.
2. Bool, unsigned comparisons and branches: source condition semantics,
   branch-local typing, result joins and actual structured Wasm control flow.
3. Acyclic scalar helpers: independent declaration graph/support, successful
   extraction of all reachable helpers, call indices/signatures, argument and
   return ABI, module layout/exports, and terminating call semantics.
4. Supported structured loops: choose and state the exact source constructs
   and termination contract before admitting them; prove loop-state semantics,
   lowering, block/branch depths, validation and total execution from that
   contract. Do not replace this with arbitrary recursion or a per-program
   Wasm behavior proof. Existing type work may be modified where appropriate.
5. Reapply clean-checkout, independent-package, real CLI/engine, mutation,
   axiom, TypeSafety and documentation gates to the expanded scope. Keep
   arithmetic as a regression. Finish only when every admitted construct is
   covered and every required gate passes on the final committed version.

The broader completion checklist below remains open wherever its full-scalar
scope is unfinished, even when the arithmetic instance of that item is proved.
Do not report broader scalar compiler correctness from the arithmetic result.

---

## Correction and authorization

The prior completion reports were false. They covered a separate backend and
five manually supplied source/IR certificates. They did not establish a usable
certified Lean-source compiler. The user has explicitly instructed removal of
that implementation and completion of the actual job. Those changes are removed
from the working tree; Git history preserves what happened. Work remains on
`correct`, with the reviewed `typesafety` source restored from
834ba204d84720e00deef9b4ce476d4a04e55ff4. Main and typesafety are untouched.

Do not mark this agenda complete because examples or backend proofs pass.
Completion requires the source-declaration compiler interface below.

## Required result

Prove the actual compiler correct once for every program in a precisely defined
scalar source subset. The general theorem must connect the original checked Lean
source declaration, the actual extraction and lowering functions, and the exact
emitted WebAssembly bytes. It must quantify over every valid input. In addition
to preservation on successful compilations, prove compilation succeeds for the
defined supported subset. Define support from source syntax and types, not from
whether an output happens to satisfy correctness.

The executable must call the functions covered by these proofs. Source meaning
must be independent of compilation and connected to Lean's operations. Each new
supported program inherits correctness from the general compiler theorem. A
separate backend, a registry of examples, or individual generated correspondence
proofs does not fulfill this task. No handwritten IR or compiler-correctness
certificate is required from the user.

The profile uses concrete WASM values: UInt64 arguments/results, internal Bool,
modular arithmetic, unsigned comparisons, bit operations and masked shifts,
strict bindings, branches, acyclic scalar helper calls, and supported terminating
structured iteration. Division by zero returns zero and remainder by zero the
dividend. Runtime Nat, heap objects, imports, mutable globals, and allocation are
excluded. Proof-level Nat and explicit termination arguments are permitted.

## Immediate milestone: arithmetic expressions end to end

The user now explicitly prioritizes a totally complete arithmetic-expression
milestone before additional language features. Finish the current independently
specified UInt64 arithmetic-expression fragment through exact emitted bytes,
full decoded module, and exported invocation for every input. No extra
source/IR or byte-correspondence certificate may be required per program.
Do not extend source bindings, branches, helpers, or loops until this milestone
is proved, pushed, audited, and demonstrated on unregistered source functions.
The larger agenda below remains deferred, not reported complete.

The arithmetic milestone is complete only when all of these hold:

- [x] Production instruction bytes decode correctly, including div/rem guards.
- [x] The complete production module decodes and validates, including runtime
      bodies, function types, locals, exports, and all section lengths.
- [x] Export lookup and invocation initialize the ABI correctly, terminate,
      and return the original source's UInt64 result for every input.
- [x] One general theorem composes original source, actual compiler entry,
      exact emitted bytes, decoded module, and exported execution. Admission
      follows source syntax and explicit format limits, with no per-program
      correspondence certificates or assumed correctness of generated code.
- [x] An explicit compiler mode rejects unsupported and oversized source
      rather than presenting compilation outside the proved subset as covered.
      Admission and wiring are checked; the native CLI/engine gate is pending.
- [ ] Clean-checkout proof build, axiom audit, independent package verification,
      and fresh real-CLI/Wasm-engine examples and edge cases all pass.

## Completion gates for the full scalar agenda (arithmetic is the first milestone)

- [x] Read and identify the actual existing extraction, IR, lowering, and emission paths.
- [ ] Define independent scalar semantics and precise source/ABI/termination contracts.
- [ ] Implement source-only certified entry admission with explicit errors.
- [ ] Prove general original-Lean-source to actual extracted-IR semantic preservation.
- [ ] Prove extraction succeeds for the defined source subset.
- [ ] Prove every scalar lowering pass used by the accepted subset.
- [ ] Compose a general theorem for the actual compiler entry point and emitted bytes.
- [ ] Cover strict bindings, branching, numeric boundaries, and acyclic helper calls.
- [ ] Cover the agreed structured-loop/termination cases without per-program WASM proofs.
- [ ] Use actual compiler emission and prove full decoded-module equality for exact bytes.
- [ ] Produce portable proof packages independently checkable without compiler/generator execution.
- [ ] Compile and certify unseen source functions with no registration, handwritten IR, or correctness certificates.
- [ ] Check deliberate source/extractor/IR/opcode/call/export/ABI/manifest mutations.
- [ ] Audit final theorem dependencies: no holes, fresh axioms, or native-evaluation shortcuts.
- [ ] Preserve the independent TypeSafety propext-only policy.
- [ ] Pass a clean-checkout gate starting from source declarations and a separate package-only gate.
- [ ] Update documentation with actual scope, exact commands, limitations, and remaining obligations.

## Work policy

Commit and push frequently; explicitly announce every successful push. Keep Lean
processes serial under the pinned toolchain. The user explicitly authorized direct
local Lean execution; tools/leanrun with LEANRUN_LOCAL=1 retains locking and
bounded execution. Split a timed-out diagnostic before retrying it. Do not spawn
other agents without authorization. No status statement can exceed its evidence.

## Journal

### Restart

Inspected the real path: LeanExe.Extract.compileEnvironment uses the existing
extractor to produce LeanExe.IR.Module; LeanExe.Wasm.Binary.CoreWasm emits it.
ScalarDescriptor and ScalarCertificate already connect parts of actual lowering
to reusable descriptor code. The typesafety base also contains the Talos
ScalarTransition proof library. The previous separate Correct/Scalar64 path,
manual-certificate CLI, bundled pilot packages, and false completion report have
been removed. The required source-only frontend is currently UNIMPLEMENTED.

### Source traversal refactor (checked)

The previous task text still allowed individual proof-producing compilation as
the final result. Corrected it to the requested general compiler theorem and
added a separate acceptance theorem to rule out vacuous success-by-rejection.

The production source traversal used opaque partial definitions for application
decomposition, lambda collection, forall collection, application reconstruction,
and a fuel-bounded beta reducer. Moved the first four into Extract.Syntax as
total functions, with reconstruction and metadata invariance proofs; made the
existing beta reducer total on its fuel. This is source traversal infrastructure,
not a source-to-IR semantics proof. No end-to-end theorem exists yet.

Validation: `lake build LeanExe.Extract.Syntax LeanExe.Extract.Types` and
`lake build LeanExe.Extract.Core` passed through tools/leanrun. The application
spine reconstruction and metadata invariance proofs were checked by Lean.

### Native scalar operations (checked)

Added independent relational semantics over the existing IR for finite locals,
strict bindings, arithmetic, branches, and short-circuit conditions. Unsupported
operators and out-of-range locals have no evaluation rule. This semantics is not
the diagnostic partial evaluator. Calls and loops still need semantic rules.

Refactored the ten direct UInt64 primitive branches in the production extractor
to call ScalarPrimitive.lower. Proved ofName_sound, ofName_name, denote_toIR, and
lower_correct against Lean's native UInt64 operations and the IR relation for
arbitrary operands. The extractor rebuild passes. This proves the primitive
lowering step only, not the enclosing opaque recursive extractor or WebAssembly.

Identified that overloaded arithmetic dispatch ignores its typeclass evidence;
checking a concrete custom-instance counterexample before changing that boundary.

### Source instance dispatch regression (checked)

Reproduced a real mismatch through compileEnvironment: a custom HAdd UInt64
instance implementing subtraction evaluated to 7 on (10,3), while extracted IR
returned 13. Removed the bypass that skipped class-evidence normalization for
arithmetic projections. The same source now extracts subtraction and returns 7.
Made the existing fuel-bounded class normalizer total. Its semantic preservation
has not yet been proved.

Added test/scalar_class_evidence.lean: 48 source-versus-extracted-IR comparisons
cover custom HAdd/HSub/HMul/OfNat, standard arithmetic, bit operations, shifts,
and branching, including zero and overflow inputs. All passed via tools/leanrun.
These are regression checks, not a substitute for the general compiler theorem.

### Recursive primitive-expression extraction (checked)

Added an independent source relation over actual Lean.Expr syntax. Its primitive
constants are explicitly paired with their native Lean definitions, separately
from the compiler's operator table. Added total extractScalarExpr and wired it
into both production extractExprFrom and extractValueFrom for materialized
scalar slots.

Proved preservation for arbitrary expression trees and inputs; support implies
compilation success; compilation success implies syntactic support; and a
combined total-correctness theorem for this extraction fragment. No examples or
per-function proof certificates occur in these proofs. Current fragment: direct
UInt64 primitives, UInt64.ofNat literals, variables, and metadata. The actual
extractor rebuild and the 48 class-evidence regression checks pass.

These theorems do NOT cover complete declarations, overloaded-source
normalization, strict bindings, branches, helpers, loops, WASM lowering, or bytes.
The full agreed subset and source-to-bytes theorem remain incomplete. Auditing
current theorem dependencies in test/scalar_expr_axioms.lean.

### Canonical elaborated scalar expressions (checked)

Extended the same production traversal and general proofs to the canonical
HAdd/HSub/HMul/HDiv/HMod/HAnd/HOr/HXor/HShiftLeft/HShiftRight applications emitted
by Lean, including exact instance evidence, and canonical OfNat UInt64 literals.
Custom instances are excluded from this proved traversal and continue through
the existing evidence-normalizing path. A class recognizer soundness theorem
connects accepted heads to the independent native-operation source relation.

The 56 regression comparisons pass. They now also assert raw-source admission
before any normalization: ordinary arithmetic, affine arithmetic with literals,
bits, shifts, and a literal above 2^64 are accepted; custom instances and the
still-unproved branch fragment are excluded. The extractor rebuild passes.

Updated axiom audit: preservation/acceptance/combined extraction theorems now
use propext, Quot.sound, and Classical.choice; recognizer soundness uses propext
and Quot.sound. These are standard Lean axioms, with no sorryAx, fresh axioms,
or native-decide shortcut. The independent TypeSafety policy is unchanged.
Declaration application and source-to-bytes composition are still unproved.

### Production entry point to IR (checked)

Added scalar function application semantics over the original elaborated lambda
term, argument-order and finite-local-slot proofs, and scalar IR statement and
single-result function semantics. Proved extractScalarFunc_correct for every
successful declaration extraction and every argument list of the declared arity,
and extractScalarFunc_accepts for the independent source support predicate.

The normal compileEnvironmentWithEntryModeDetailed now handles the proved scalar
declaration case before the general opaque recursive extractor. It uses the same
IR and result-slot ABI and continues into the existing emitter. The generic
compileEnvironment_scalar_total_correct theorem references that actual entry
point, the original environment declaration/body, syntactic source support, and
all inputs. Its endpoint is IR.Func.ScalarEval. Native scalar constants have
explicit meanings in the independent source grammar; arbitrary Lean syntax is
not included. Existing unsafe/partial and reserved-export exclusions remain.

The proof and production extractor build pass. The 56 regression checks pass
through the changed entry point. This is NOT the end-to-end compiler theorem:
WASM lowering/encoding and the rest of the agreed language features remain open.

### Production emitter transparency (checked)

Made the existing expression/condition/local-let/statement scratch calculators
and annotated statement emitter total. The nested-list termination obligation
uses element membership and structural size; their equations and emitted code
were not replaced by a separate backend. Existing ScalarCertificate proofs pass.

Proved scalarFunc_emit for the normal emitFuncInstrs function: the exact emitted
instruction list is the recognized descriptor's code followed by the actual
result-slot store/load. Added descriptor scalar evaluation and operator meaning
lemmas as preparation for the IR-to-WASM semantic proof. The descriptor evaluator
alone is not a WebAssembly execution theorem. Talos semantics, scratch bounds,
module assembly, and exact binary correspondence still need to be connected.

### IR descriptor semantic preservation (checked)

Proved Expr.ofIR_eval and Cond.ofIR_eval for the existing descriptor recognizers.
Every recognized scalar IR evaluation has the same descriptor value and leaves
source locals unchanged. The proof covers arithmetic, branches, comparisons,
negation, and short-circuit conjunction/disjunction. Strict bindings cannot be
silently discarded: this pure recognizer rejects them. The proof is generic over
IR expressions, stores, and results and passes the kernel.

Next connection is to the existing Talos ScalarTransition program theorem via
an explicit interpretation of the production Instr syntax. That bridge is being
implemented in Project.Compiler.ScalarLowering; it is not yet an established
WebAssembly correctness result.

### Emitted instruction correspondence and control annotations (checked)

Added a total interpretation of the production structured instruction syntax
into Talos instructions. Proved expression_program and condition_program for
all existing scalar descriptors and scratch indices: the actual emitter's
instruction list interprets to the existing ScalarTransition program. This
includes division/remainder guards and short-circuit/conditional control.

Separately proved that changing static block/loop/if type annotations while
preserving arities and related bodies preserves Talos execution at every fuel,
and consequently its total-correctness WP. The proof was split after an initial
timeout; it now uses bounded interpreter unfolding and checks in seconds.

Both proof modules build. The interpreter translation currently omits static
type annotations to match ScalarTransition. Connecting it to the typed binary
decoder requires the proved annotation relation; that connection is still open.
Scratch-state correspondence, allocation bounds, module assembly, and byte
roundtrips remain open. These results do not establish source-to-bytes correctness.

### Scratch bounds and emitted expression execution (checked)

Proved correspondence between native scalar descriptor evaluation and Talos's
scratch-aware scalar evaluator. The theorem covers every expression/condition,
preserves all source slots, preserves local capacity, and establishes successful
evaluation whenever the descriptor scratch width fits. Native division and
remainder at zero and masked shifts are proved to agree with Talos operations.

Proved that the production exprScratch/condScratch calculations equal recognized
descriptor widths, and that funcScratch for scalar declarations supplies exactly
that width. Proved expression_execution: the actual emitted structured expression
instructions, interpreted in Talos, terminate with the source value and unchanged
source slots. Also proved the initial parameter/local ABI state representation.
All four new proof modules build. This execution theorem is for instructions;
encoded module bytes and whole exported-function invocation remain unconnected.

### Production source entry to complete function instructions (checked)

Proved that every successful production scalar expression extraction is accepted
by the existing backend descriptor recognizer. This is derived from source
syntax; backend acceptance is not an extra per-program obligation.

Added scalar_function_execution and extracted_function_execution, including
actual zero-initialized locals, the production scratch allocation, result-slot
store/load, and all source inputs. Composed compileEnvironment_instructions for
the actual normal compiler entry: independent source support implies successful
compilation and termination of the full emitted function instructions with the
original source value. Its scope is the arithmetic declaration fragment, and its
endpoint is Talos interpretation of structured instructions, not decoded bytes.

All new modules build. Project.Compiler.AxiomAudit reports only propext,
Classical.choice, and Quot.sound for the composed theorem and backend lemmas;
no sorryAx or fresh axioms. Remaining obligations include binary encoding and
full decoded-module equality, exported invocation, explicit admission errors,
strict bindings/branches/helpers/loops at source, and the final release gates.

### Unsigned production byte encoding (checked)

Proved that the shipped UInt64-based LEB encoder emits the independent Wasm
binary grammar's U32 encoding for every value below 2^32, and its U64 encoding
for every UInt64. The proof establishes length, continuation bits, final-byte
bounds, and decoded numeric value. It connects directly to Binary.u32leb.
Added the list-view equivalence needed for the actual ByteArray.toList calls.
The proof builds; signed constants and complete module encoding are next.

A first signed-bit helper attempted bv_decide and Lean exited with code 139.
That failed attempt is not committed or counted as evidence; replacing it with
explicit bitvector/arithmetic lemmas.

### Signed encoder bit operations (checked)

Replaced the crashing automated bitvector attempt with explicit kernel-checked
lemmas. Proved that the production sar7 implements signed arithmetic division by
128 on every UInt64 bit pattern, and that the low seven bits equal the signed
remainder modulo 128. The sign-fill proof handles every bit position explicitly.
SignedLebBits builds without bv_decide, native_decide, holes, or new axioms.
This is a checked part of signed-LEB correctness; the full signed encoding and
module-byte theorem remain unfinished.

The user reiterated frequent updates, commits, and pushes. Continue pushing each
checked increment, announce the pushed SHA immediately, and provide a progress
update at least every minute during ongoing work.

### Complete production signed LEB correctness (checked)

Proved the actual s64lebU64 encoder satisfies the independent binary grammar's
S64 relation for every UInt64 bit pattern, with exactly its two's-complement
signed value. The proof covers stopping conditions, final-byte bounds,
continuation form, at most ten bytes, and numeric reconstruction, and connects
the actual ByteArray output to the grammar. SignedLebStop, SignedLebTrace, and
SignedLeb all build. There are no per-constant certificates or finite test
assumptions. Next: instruction encoding, module assembly/decoding, and exported
execution for the arithmetic-only milestone.

### Arithmetic instruction binary grammar (checked)

Proved that the actual CoreWasm.encodeInstr/encodeInstrs output satisfies the
independent Wasm instruction grammar for scalar arithmetic instructions,
UInt64 constants, bounded local indices, and the structured i64 conditionals
used by division/remainder guards. The proof uses the production signed and
unsigned encoders and exact opcode bytes, including nested instruction lists.
ArithmeticEncoding builds. The relation still needs to be derived for every
admitted source expression and connected to the decoder and module theorem.

### Production integer and atomic-instruction decoder roundtrips (checked)

Proved parser composition with arbitrary prefixes, suffixes, and section limits.
Proved the existing decoder consumes production U32 and signed I64 encodings and
returns their exact values. Proved the same roundtrip for every arithmetic
opcode, literal, and bounded local read/write emitted by the actual instruction
encoder. Parsing, LebParsing, and ArithmeticParsing all build. Structured
conditionals, full functions/modules, and source-to-byte composition remain.

### Arithmetic admission and sequence-parser lemmas; workspace recovery

Proved that successful arithmetic extraction yields an arithmetic-only backend
descriptor, and that evaluation bounds all local reads. Added the peek-and-bind,
sequence terminator, sequence cons, and instruction-prefix lemmas. These files
passed Lean before workspace maintenance removed the checkout, installed
toolchain, and unpushed files. Restored the checkout from correct at a488bc3c
and reconstructed these exact changes from the session. A fresh rebuild after
recovery is pending while the pinned toolchain and dependencies are restored.
The structured instruction roundtrip was still being repaired and is not
counted as checked. The whole arithmetic milestone remains incomplete.

### Complete arithmetic instruction-sequence decoding (checked after recovery)

StructuredParsing now proves the actual decoder roundtrips production arithmetic
instruction sequences, including nested i64 conditionals and final terminators,
at arbitrary prefixes/suffixes and section limits. ArithmeticEmission derives
binary-grammar coverage for every arithmetic descriptor with bounded local
indices and sufficient scratch-index range; it requires no per-program
correspondence certificate. Parsing, SequenceParsing, StructuredParsing,
ArithmeticAdmission, and ArithmeticEmission passed the fresh restored build.
Container parsing/encoding and translation to execution are still being checked;
complete module decoding, validation, exported invocation, and final gates remain.

### Length-prefixed containers (checked)

ContainerEncoding identifies the production byte-vector, item-vector, and
section emitters with their exact list-of-bytes encodings. ContainerParsing
proves exact consumption for bounded parsers, sized payloads, and vectors,
including the decoder's remaining-input checks. Both modules build. These are
general module/body assembly lemmas, not yet a complete module theorem.

### Decoded arithmetic instructions to execution (checked)

ArithmeticTranslation proves raw decoded arithmetic syntax translates to the
previously proved executable program, including exact signed-constant bit
reconstruction and static control annotations. ArithmeticFunctionBytes composes
this with the actual function emitter and decoder: the complete emitted
instruction bytes decode to a program that executes with the arithmetic IR's
proved value. This theorem still assumes the existing IR evaluation premise;
the earlier general source-extraction theorem supplies it, but the composed
source-byte statement is not yet added. It does not cover the enclosing module
or exported invocation. Both new modules build. Narrowed the binary translator's
import to the interpreter syntax it uses; its implementation is unchanged.

### Original arithmetic source to exact function-body bytes (checked and audited)

FunctionParsing proves decoding of the actual emitFuncBody output, including
local declarations and the size prefix. SourceFunctionBytes composes original
source application, production extraction, actual encoding/decoding, and decoded
body execution for every input, subject to explicit local-count and body-size
format limits. There is no per-program semantic/correspondence hypothesis.
This is still a function-body theorem, not a whole-module/export theorem.
ArithmeticBytesAudit builds and reports only propext, Classical.choice, and
Quot.sound for the composed theorem and decoder lemmas; no sorryAx or new axioms.
Full module construction/validation, invocation, source admission limits, and
final clean-checkout/independent-package/runtime gates remain unfinished.

### Function signatures and UTF-8 names (checked)

HeaderParsing proves exact parsing of production byte vectors, arbitrary UTF-8
export names, repeated i64 parameter/result types, and complete function types,
subject to the relevant U32 length bounds. It connects String.fromUTF8? to the
original string and includes arbitrary byte prefixes, suffixes, and limits.
The module builds. Complete sections, fixed runtime bodies, validation, and
exported invocation still remain.

### Export, memory, and global entries (checked)

MetadataParsing proves exact production export-entry parsing, bounded function/
memory/global indices, minimum memory limits, mutable i64 global types, and
signed i64 global initializers. The module builds. These lemmas supply the
metadata payloads for the forthcoming complete module decoder theorem.

### Module header and section-loop composition (checked)

SectionParsing proves complete-input parser composition and section-loop steps,
including duplicate-section and order checks. ModuleParsing connects a completed
section stream to the actual module magic/version parser; ParsesEnd.runAll
connects that result to the public complete-input decoder. Both modules build.
Split the original module-header proof after an elaboration heartbeat limit;
explicit parser continuations now check without raising the limit. The exact
compiler module still needs its six concrete sections and fixed runtime bodies
instantiated, followed by validation and exported invocation.

### Fixed-runtime instruction forms (checked)

RuntimeAtoms proves roundtrip decoding for the additional indexed, memory,
global, call, branch, conversion, comparison, and signed -1 instructions used
by the production runtime. RuntimeStructure proves their structured-control byte
shapes and non-terminator opcode prefixes. Both modules build. The runtime's
nested instruction-sequence decoder proof and the four concrete runtime bodies
are still pending; arithmetic source support has not been expanded.

### Nested runtime instruction decoding (checked)

RuntimeParsing proves decoding for nested runtime instruction sequences,
including blocks, loops, empty-result conditionals with and without else arms,
and expression terminators. The proof uses the production instruction encoder
and the existing decoder with sufficient byte-derived fuel. The focused build
completed successfully. This is a general parser lemma, not yet its instantiation
for the four actual runtime bodies or a complete module theorem.

### Arithmetic milestone completion requirements (restated)

Completion requires the actual normal source compiler's emitted whole Wasm file
to decode, validate, and execute the requested export with the original source
result for every UInt64 argument list of the right arity. The accepted source
syntax and format limits must imply compilation success without per-program
semantic or compiler-correspondence certificates. A usable proved-subset mode
must reject unsupported source and exceeded bounds. Clean-checkout builds,
axiom inspection, independent portable-package verification, independent Wasm
engine edge cases, and the existing mutation gates remain required. Arithmetic
source-to-function-body bytes is checked; whole-module assembly, validation,
exported invocation, admission limits, and final gates remain incomplete.

### Actual fixed runtime instruction lists (checked)

RuntimeBodies constructs raw Wasm syntax together with the encoding-relation
proofs for the existing allocator, reset, retain, and release instruction lists.
The release function uses index four, as in an actual single-source-function
module. Each construction applies checked relation constructors to the real
runtime definition; no runtime code or compiler output is replaced. The module
builds, and RuntimeParsing therefore supplies instruction-expression decoding
for these exact lists. Local declarations and body size prefixes, complete
section assembly, module validation, and exported invocation remain to compose.

### Complete runtime body containers (checked, length bounds explicit)

RuntimeFunctionParsing composes the fixed runtime instruction proofs with actual
local declarations and the production body size-prefix encoder. Each of the
four body parsers is proved under its explicit U32 payload-length bound. The
module builds. These fixed bounds are being discharged using general encoder
length lemmas; complete section assembly, validation, and exported execution
remain unfinished.

### Runtime body decoding without assumed bounds (checked)

LebLengths proves the production signed and unsigned UInt64 encoders emit at
most ten bytes. RuntimeLengths bounds nested runtime instruction encodings and
discharges all four fixed payload limits. RuntimeFunctionParsing now proves
complete decoding of all four actual runtime bodies without length hypotheses.
All three modules build. This completes that component; complete module
sections, validation, exported invocation, and final gates remain pending.

### Whole six-section decoder composition (checked)

ModuleSections composes payload parsing into the public complete-input module
decoder for the exact six-section layout emitted by the production compiler.
It proves section order and uniqueness checks, exact module header consumption,
and sufficient section-loop fuel. The module builds. The remaining task at this
boundary is to supply the actual compiler payloads and their bounds; this general
composition theorem alone is not the source-to-module correctness result.

### Production vectors and fixed module payloads (checked)

ContainerEncoding now characterizes the native unsigned-vector emitter.
PayloadVectors proves production vectors decode from their entry proofs and
nonempty encodings, including arbitrary bounded U32 vectors. FixedPayloads
instantiates this for the actual five function-type indices, 16-page memory,
and six mutable i64 globals, and connects these payloads to the production
sections. All affected modules build. Variable signatures, exports, and user
code must still be assembled with these fixed payloads.

### All six concrete payload parsers (checked)

UserPayloads proves the actual variable function signatures and UTF-8 exports
decode correctly under their U32 bounds. CodePayloads assembles the actual user
body and all four proved runtime bodies into the production code vector.
FixedPayloadBounds discharges fixed function-index, memory, and global section
length bounds using general vector and constant-encoding length proofs. All
affected modules build. The exact moduleBytes composition theorem is now being
checked; validation and export invocation remain unfinished.

### Exact production module bytes decode (checked)

ArithmeticModuleBytes proves that the public decoder consumes the exact
CoreWasm.moduleBytes output for a single source function, including all runtime
functions and metadata. Its user-body parsing premise is the one established
by SourceFunctionBytes; its remaining format hypotheses are only parameter,
result, name, and variable section sizes. The module builds. Source composition
is next. This is not validation or export-invocation correctness.

### Original source to whole module bytes (checked and audited)

SourceModuleBytes composes successful production source extraction with exact
whole-module decoding and decoded user-body execution for every input. Parser
determinism fixes one decoded body; the universal execution proof is applied
to every argument list and every surrounding module/store. The theorem also
records the exact local declarations. ModuleBytesAudit reports only propext,
Classical.choice, and Quot.sound for the composed theorem, module decoder, and
runtime body proofs. Both modules build. Export lookup/calling convention,
module validation, normal-entry success composition, usable admission mode,
and final gates remain unfinished.

### Source-to-exported-invocation preservation (checked and audited)

ModuleInvocation proves lookup of the actual requested export, the translated
user function, argument reversal into interpreter stack order, exact local
initialization, and return-value extraction. SourceInvocation composes this
with exact module decoding and original source semantics: every argument list
of the correct arity terminates with the source value and preserves the store.
The explicit format bounds remain. Both modules build; the expanded audit
reports only propext, Classical.choice, and Quot.sound. This theorem does NOT
yet assert that the module passes validation. Full validation, normal compiler
entry success composition, the usable admission mode, and final gates remain.

### Compositional validation rules (checked); larger runtime checks pending

ValidationRules proves signed constant ranges, typed stack operations, and
validator sequence composition. TypedSequences derives typed encoding for
locals, constants, all ten arithmetic operations, equality, framing, and
concatenation. RuntimeValidation currently proves only reset. These modules
build. Direct reduction of retain/alloc/release hit the 200000-heartbeat limit;
a broad simplification attempt then reached the 90-second process timeout
without further diagnostics. Preserved that attempt in the scratch log area
and split the checked reset theorem from the unfinished larger proofs. The
next arithmetic validation step is the compiler-generated division/remainder
conditional, followed by the general expression theorem. No full-module
validation claim is made.

### General arithmetic validation induction (checked)

TypedConditionals proves the validator accepts the i64-result conditionals
used by division/remainder guards. ArithmeticTyping proves every admitted
arithmetic descriptor emits a sequence with the required stack type, under
its local-index and scratch-allocation bounds, for arbitrary nesting and all
ten operators. Both modules build. FunctionTyping and the source-to-function
validator composition are still being checked; no complete module-validation
claim follows yet.

### Actual source-produced user function validates (checked and audited)

FunctionTyping connects typed sequences to the existing complete function
validator, including actual i64 parameters/locals and result framing.
SourceFunctionValidation derives the typed sequence from production source
extraction and uses parser uniqueness to identify the actual decoded body.
Both modules build. ModuleBytesAudit reports only propext, Classical.choice,
and Quot.sound for extracted_function_valid. Larger runtime functions and
whole-module metadata validation remain. During export validation, found
reservedExportNames omits seven runtime exports; a regression and fix are next.

### Runtime export collision bug fixed and regression-tested

The production reserved-export list covered only memory/alloc/reset despite
emitting retain/release/free and four counter exports as well. A regression
against the actual compiler reproduced acceptance of RuntimeExportNames.retain
before the fix. Extended the list to all ten runtime exports. Rebuilt
LeanExe.Extract.Core and reran the regression successfully: every runtime name
is rejected for exported entries with the expected diagnostic, each remains
allowed for an internal function, and an ordinary arithmetic export compiles.
This fixes invalid duplicate-export modules and supplies the needed name
precondition for whole-module validation.

### Complete module metadata validation (checked)

MetadataValidation proves section ordering, the fixed memory limit and globals,
function type resolution, all eleven export indices, UTF-8 name agreement, and
export-name uniqueness for every source entry outside the runtime reserved list.
The module builds. This closes the metadata portion of validation; retain,
allocator, release, full validator composition, normal-entry composition,
usable arithmetic mode, and final gates remain unfinished.

### Execution blocked after metadata checkpoint (2026-09-25)

MetadataValidation completed successfully (3148 jobs) and was pushed at
62cb863e3d105f98d11604925c1aed8682492929. The subsequent bounded retain-validation
attempt used a restricted simp set, but the execution connection disconnected
before its result could be retrieved. New commands now fail with HTTP 409,
environment_offline: Environment is not connected. Resuming the existing process
also fails. This is not evidence that files were deleted or that the proof
passed. No retain validation result is claimed. The GitHub workflow-directory
lookup returned 404, so an existing CI runner was not available as a fallback.

Resume from the pushed metadata checkpoint, recover the retain attempt if it
remains on disk, and reduce its proof boundary before another long check. Finish
retain/allocator/release validation, compose full validation and the normal
compiler-entry theorem, implement the arithmetic admission mode, then run every
remaining clean-build, axiom, package, runtime, and mutation gate. The arithmetic
milestone remains INCOMPLETE.

### Workspace restored; arithmetic admission implementation being checked

After the execution outage, automated workspace maintenance removed the local
checkout files and toolchain. Restored `correct` from GitHub into a fresh local
checkout, restored pinned dependency revisions, and installed the exact pinned
Lean release. The production extractor and source-to-IR proofs rebuilt. The
first cache recovery reached its process limit after restoring part of the
cache; dependencies are being recovered in smaller steps.

Added reusable numeric arithmetic module size bounds and a strict arithmetic
entry that rejects excluded source forms, unsafe/partial entries, reserved
exports, and format overflows before invoking the existing normal compiler.
The two new production modules build. Admission regression checks, the CLI
wiring, and the proof connection are still being checked. No new end-to-end
correctness claim is made.

The arithmetic admission regression now passes. Supported expressions, bit
operations, and an overflowing literal produce byte-for-byte normal-compiler
output. Bindings, branches, helper calls, custom instances, non-UInt64 types,
reserved exports, and missing entries are rejected. An oversized parameter
count is rejected without constructing its type vector. These are executable
regression checks; the complete correctness theorem and CLI gate remain open.

### Arithmetic admission proofs and CLI wiring (checked)

ArithmeticCorrectness proves strict compilation accepts the independent source
subset whenever the explicit numeric format limits hold. It also proves every
successful strict compilation provides the original environment declaration,
safe/total flags, nonreserved export name, exact scalar extraction, and all
numeric bounds. ScalarEntryCorrectness now exposes the reusable connection
from successful extraction to the actual normal compiler. These modules build.
The CLI's compile-arithmetic command builds and calls this strict entry followed
by the unchanged production emitter. The actual CLI executable/engine gate and
full source-to-module theorem are still pending.

### Shared admission sizes connected to the checked byte layout

The production admission mode and the module-byte proofs now use the same type,
export, and code payload definitions for numeric size checks. The production
emitter is unchanged. Rebuilt exact whole-module decoding, fixed runtime-body
parsing, reset validation, and complete metadata validation successfully
(3110 jobs). Narrowed the runtime and metadata validation imports to the binary
layout and validator definitions they need. Retain/allocator/release validation
and the final composed theorem are still being checked.

### All actual runtime functions validate (checked and audited)

Retain, allocator, and release validation now pass Lean kernel checking in
3.5, 3.6, and 3.7 seconds respectively. Each theorem quantifies over the actual
surrounding arithmetic module and reports only propext in its dependencies.
Together with reset, all four fixed runtime bodies are covered.

KernelReduction constructs an ordinary Eq.refl proof term and leaves the
conversion check to declaration kernel checking, avoiding repeated expensive
elaborator normalization. It adds no axiom or native-evaluation oracle. A
negative control asserting Nat 0 = 1 was rejected by the kernel with a declaration
type mismatch. Full module-validation composition and the complete normal-entry
source-to-file theorem are being checked next; final gates remain open.

### Complete general compiler theorem (checked and audited; gates still open)

ModuleValidation composes source-function validation, all runtime functions, and
metadata into validateRaw for the exact decoded production module.
SourceCorrectness.extracted_correct combines this with exact byte decoding,
requested export lookup, argument/local ABI, and total source-equal execution
for every input, host, and store.

SourceCorrectness.compileEnvironment_correct proves independent source support
and explicit numeric format limits imply both normal and arithmetic-mode
compilation succeed with the same module and this full correctness property.
compileEnvironment_sound proves every successful arithmetic-mode compilation
has the property, with no caller-supplied semantic/correspondence premise.
All modules build (3166 jobs). The final compiler theorems report only propext,
Classical.choice, and Quot.sound; no holes, new axioms, or native-evaluation
certificates. This is the complete arithmetic compiler theorem. The milestone
remains INCOMPLETE until the actual CLI/independent-engine, standalone-package,
clean-checkout, mutation, and policy gates pass and documentation is finished.

### Second maintenance recovery; unfinished gates checkpointed

A later maintenance event again removed the restored checkout, installed Lean,
and local run logs. The complete general theorem and its audit remain pushed
at 5dfcd8f5. The previous automated proof gate and kernel-negative check passed,
but the CLI executable build was still in progress at the last observed log;
its eventual result is unavailable and is not counted as a passed gate.

Restored the gate driver, independent-engine comparator, and fresh Lean source
fixtures from the session. They are checkpointed before rerunning to avoid
another loss of unpushed gate work. Their reconstructed versions have not yet
passed the full run. Package verification, clean-checkout proof build, mutation
tests, and the independent type-safety policy gate also remain pending.
