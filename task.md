# Byte I/O completion

## Current state and scope

Updated 2026-09-24 after resuming on ARM macOS.  Branch `io` tracks `origin/io`; this session resumed from `4f3c3a394a8f13c4e897478b334c3cc9de16c989`.  Its implementation baseline is `fb19b5efdd6cc171033adf888667764203c14f14`, based on `a4655383ee80d3d80830b6bddfb6248a9d5c2b4b` on `main`.  The resumed work repairs string-literal and nested-loop temporary ownership, adds regression and CLI checks, proves the modeled byte-I/O host and protocol behavior, refreshes the existing compiler proofs, and reconciles the documentation.  The user requested frequent commits and pushes as validation proceeds.

The current task is to complete primitive byte I/O, validate its shared compiler changes, and reconcile the documentation.  The user deferred release-identity work on 2026-09-24.  Release receipts, release-input digests, and cold release verification remain deferred.  The user included formal verification of the new byte-I/O host behavior on 2026-09-24.  Rechecking the existing Talos proofs is part of compiler validation.

This document owns the current continuation agenda.  The [Development Journal](devnotes.md#2026-09-23-byte-io-on-branch-io) preserves the implementation history and reported test evidence.  Its September 23 entry contains both intermediate and final results.  The current I/O count is 47 execution cases.  Counts of 26, 30, and 38 describe earlier revisions.

The resumed session has built the compiler and reproduced the focused execution checks.  Current results below distinguish fresh runs from earlier reports.  The non-release inventory has run, including a successful source/IR comparison rerun after a local-runner compatibility fix.  All 69 regenerated source caches match, and the complete current source-proof library passes for all 68 registered complete specifications.  Release identity remains deferred.

## Agreed behavior

The [Language Specification](docs/spec.md#byte-input-and-output) defines the public behavior.  The [Byte I/O API](LeanExe/ByteIO.lean) has these signatures:

```text
abbrev ByteIO (α : Type) := BaseIO α

read (maxBytes : Nat) (timeoutNs : UInt64) : ByteIO (Except UInt32 ByteArray)
write (bytes : ByteArray) (timeoutNs : UInt64) : ByteIO UInt32
```

| Operation or rule | Required behavior |
|-------------------|-------------------|
| Read | Return up to the positive capacity.  A short read succeeds.  Empty success means EOF.  Each returned byte array retains its contents across later reads. |
| Read capacity | Zero or a capacity outside the WASM address range returns error `28`.  Allocation exhaustion follows the runtime allocator's trap behavior. |
| Write | Return zero after writing every byte, or an error after possibly writing a prefix.  An empty write succeeds. |
| Errors | A read returns an explicit `Except`; a write returns an explicit status.  The caller handles propagation.  The previous session rejected an `EIO UInt32` and `try`/`catch` design. |
| Sequencing | Every sequenced action executes once, including an action whose result is ignored.  A `let`-bound action executes when sequenced, on each sequencing. |
| Timeout | A monotonic duration in nanoseconds covers the whole operation.  Partial writes and interrupted calls retain the original deadline.  Zero allows one immediate nonblocking attempt.  Deadline addition saturates on overflow. |
| Timeout result | Expiry returns `73`.  Clock and scheduling resolution affect observed completion time. |
| Other error codes | The backend uses WASI Preview 1 numbers, including `8` for a bad descriptor, `28` for invalid input, `29` for an I/O failure, and `64` for a broken pipe. |
| Command entry | `compile-wasi-io` accepts a zero-argument `ByteIO UInt32` entry.  Its result becomes the process exit status.  Reads use stdin and writes use stdout. |
| Source boundary | Ordinary supported data types remain available.  I/O actions cannot be stored in arrays or passed as runtime function arguments.  The two opaque primitives have compiler implementations.  Native Lean execution is unavailable. |

The existing pure WASI adapters remain available for bounded stdin, argv, stdout, and stderr around pure entry functions.  General file access, user-defined host calls, concurrency, direct clock access, and system-call protocols require separate design work.

## Implementation and host

### Source map

| Component | Source and responsibility |
|-----------|---------------------------|
| Public API and examples | [Byte I/O API](LeanExe/ByteIO.lean) and [Byte I/O examples](LeanExe/Examples/ByteIO.lean).  Examples include streaming, retained buffers, errors, and action sequencing. |
| Entry recognition | [Extraction types](LeanExe/Extract/Types.lean), [pattern handling](LeanExe/Extract/Patterns.lean), and [core extraction](LeanExe/Extract/Core.lean).  `ByteIOCompilation.compileEnvironment` checks the entry type. |
| Effects and pruning | [IR definitions](LeanExe/IR/Core.lean), [effect analysis](LeanExe/IR/Effects.lean), and [value extraction](LeanExe/Extract/Values.lean).  `LocalLet.effectCall` preserves sequenced calls and their arguments. |
| I/O program representation | [Byte I/O IR](LeanExe/IR/ByteIO.lean).  Read and write occupy external runtime function indices after the extracted functions. |
| Ownership and loop emission | [Core extraction](LeanExe/Extract/Core.lean), [value extraction](LeanExe/Extract/Values.lean), and [binary emission](LeanExe/Wasm/Binary.lean).  These changes also affect pure programs. |
| WASI runtime | [Byte I/O emitter](LeanExe/Wasm/ByteIO.lean).  It emits deadline handling, read/write loops, polling, error returns, allocation, and command startup. |
| Command dispatch | [Compiler CLI](LeanExe/CLI.lean).  `compile-wasi-io` uses the existing categorized error interface. |
| Integer encoding | [LEB encoding](LeanExe/Wasm/Leb.lean), [binary emission](LeanExe/Wasm/Binary.lean), and [image emission](LeanExe/Wasm/Image/Emit.lean).  `i32.const` uses signed LEB128 after truncation and sign extension. |
| Native test host | [WASI I/O host](tools/wasi-io-host.c) and [host builder](tools/build-wasi-io-host.sh). |
| Execution tests | [Host tests](test/wasi_io_host.js), [source I/O tests](test/byte_io.js), [reference-counting tests](test/refcount.js), and [self-emission tests](test/self_emit.js). |
| Test inventory | [Aggregate execution driver](test/run_all.js) and [development requirements](DEVELOPING.md#development-workflow). |

### Changes that need broad validation

Effect analysis now retains effects in unused results, loop bodies, call arguments, and branch conditions.  Saved actions remain unevaluated until sequenced.  Effect calls lower to ordinary WASM calls while retaining their ownership information.

`forInStepOwnedTemporaries` visits conditional branches.  `releaseForInStepTemporaries` clears temporary owner slots at each iteration before collecting and releasing the owners created on that iteration.  This prevents a skipped branch from reusing an earlier iteration's pointer.

Accumulator analysis tracks fresh, preserved, and null owners.  `emitAccumulatorReleases` compares an old owner with the initial and next accumulator owners before releasing it.  Initial owners are saved after all initial expressions have been evaluated.  Result cleanup also protects enclosing-scope owner slots, including when an error path returns the initial buffer.  These rules changed several shared fold and loop emitters.

The signed `i32.const` repair fixes a separate pre-existing encoder defect: unsigned LEB128 made address 64 decode as -64.  The tests cover 63/64, 127/128, 8191/8192, both signed endpoints, and truncation of high input bits.

### Host requirements

The generated module imports six functions from `wasi_snapshot_preview1`: `fd_read`, `fd_write`, `fd_fdstat_set_flags`, `clock_time_get`, `poll_oneoff`, and `proc_exit`.

The previous session found that the pinned Wasmtime 44 CLI rejects setting nonblocking flags on its standard streams with `BADF`.  The [pinned standard-stream implementation](https://github.com/bytecodealliance/wasmtime/blob/v44.0.0/crates/wasi/src/p1.rs) is the recorded source for that behavior.  Polling followed by an unrestricted blocking write cannot enforce the requested write timeout.

The repository host uses the pinned Wasmtime engine and implements the required WASI calls over native nonblocking stdin/stdout.  Its supported subset accepts one iovec and at most two poll subscriptions.  It preserves descriptor flags on exit.  Its tests use native pipes and a five-second watchdog for each child.  Timeout behavior requires this host or another host satisfying the same requirements.

The [WebAssembly integer encoding specification](https://webassembly.github.io/spec/core/binary/values.html#integers) is the recorded reference for the signed-constant repair.  Repository requirements and operating instructions are in [Developing LeanExe](DEVELOPING.md).

## Evidence and unresolved defects

### Recorded results

These are results reported by the previous session in the development journal.  They require reproduction on the current checkout.  Earlier encoding, host, and WAT checks also precede the final ownership audit.

| Check | Reported result | Scope |
|-------|-----------------|-------|
| Byte I/O source tests | 38 execution cases passed, plus four pure-mode rejection checks. | Binary bytes, EOF, short reads, sequencing, saved actions, helpers, invalid capacity, zero and saturated timeouts, delayed input, partial writes, blocked/broken output, and cleanup. |
| Sustained streaming | Copied 4 MiB plus 137 bytes with 4,096-byte reads. | Compared the complete output and checked allocation/free counts between iterations and after return. |
| Retained buffers | Passed skipped-iteration, timeout, and output-error cases. | Exercises preservation of the initial and previous read buffers. |
| WASI host tests | Seven cases passed. | Nonblocking readiness, EOF, bounds errors, clock expiry, binary transfer, EOF polling, and blocked output. |
| Reference counting | 41 cases passed after the final accumulator and enclosing-scope changes. | Existing allocation and ownership behavior. |
| Signed-constant checks | Boundary checks and all 75 self-emitted LEB128 cases passed. | Native and image encoders. |
| WAT/binary agreement | Thirteen cases passed during the earlier audit. | Pure compiler serialization.  The current check uses `compile` and `compile-wat`. |
| Aggregate execution | Stopped at a release-input identity mismatch. | Later constituent tests still require a complete run.  Release identity is deferred by the user. |
| Core correctness | `arraySetIfInBoundsSkipsValueTrap` trapped. | The same failure and identical binary occurred on the branch base. |
| Documentation | Reported an absolute temporary-workspace path in the WGSL review document. | Existing documentation defect. |
| Talos | Stopped during the initial Mathlib cache download after 867 of 8,747 files. | Proof checks had not begun. |

### Current ownership results

The reported `arraySetIfInBoundsSkipsValueTrap` failure does not reproduce on the resumed branch: it returns `7` with one allocation and one free.  The generated binary has SHA-256 `c732ee7c5cb2f589e6f0beeda196f4b894dc29954ee95ed8229fbe0d3a76f65e`, different from the earlier failing binary.  Its IR guards the conditional result release against enclosing owners.  This guard was added in `cd20f9cf`.  The related out-of-bounds `Array.modify` case also returns `7` with balanced allocation counts.  Both now have explicit allocation assertions in the reference-counting suite; no additional alias-rule repair was needed.

The literal leak reproduced: `"ABC".toUTF8.size` returned `3` but allocated five blocks and freed two.  A byte-I/O helper writing the literal also left allocations live after returning.  The new regression tests failed before the repair.  Literal extraction now uses one `arrayLiteralSlots` backing array, replacing nested copying updates whose intermediate arrays had no cleanup binding.  Tests cover scalar use, returned bytes, string constants and concatenation, repeated sequenced writes, and broken-output cleanup.

Fresh checks passed: 7 native host cases; 40 byte-I/O runs and four pure-mode rejections; 48 reference-counting cases; 812 accepted, 48 rejected, and 14 expected-trap core cases; 70 byte-array allocation cases; 75 self-emitted LEB128 cases; and all 13 WAT/binary comparisons.  Session logs and the pre-fix failures are retained in the task workspace's `work` directory.  The initial pure-WASI adapter run failed because Wasmtime tried to create its default cache outside the sandbox; a wrapper now selects a workspace-local cache for reruns.

The nested-loop review found a second leak: an inner loop's final fresh
buffer was missed because its result could also alias the borrowed initial
buffer.  Step cleanup now tracks that result with guards for initial owners
and enclosing results.  New cases cover normal output, EOF, zero iterations,
timeout before and after replacement, and broken output.  All 47 I/O cases,
four pure-mode rejections, and 48 reference-counting cases pass.  The core
suite also passed after the initial repair; final compiler proof validation
continues below.

### Documentation and diagnostics

The [user manual](docs/manual.md#byte-input-and-output), [overview](README.md), [compiler guide](docs/compiler.md), and [development instructions](DEVELOPING.md) now describe byte I/O, the nonblocking host, diagnostic scope, and current accumulator cleanup.  The CLI error suite passes 15 cases plus help output, including byte-I/O command shape, pure/IO/parameterized entry rejection, missing entry, and output-file failures.  All 28 ownership-report cases pass after updating three stale statement-release counts from two to three; the reports now include the guarded final loop-result owner release.  CLI and standard-comparison checks exclude only exact local-runner notices from compiler/program stderr, preserving unknown failures and other output.  Runtime reporting and WAT commands retain their existing pure-entry scope.

The documentation checker now passes all 162 maintained Markdown files after removing the obsolete temporary checkout path from the WGSL review notes.  Root `task.md` and `devnotes.md` remain outside that checker's inventory and require separate review.

The follow-up review's two P2 native-host findings are repaired. Shared stdin/stdout flags are captured before either stream changes, and the host uses Cranelift with NaN canonicalization. The host suite passes seven I/O cases and twelve shared-descriptor restorations; source tests pass 53 executions, including six binary32/binary64 NaN cases, and four pure-mode rejections. Both regressions failed before their fixes. The byte-I/O proof gate passes again with identical echo bytes and 46 standard-axiom audits. The P3 manual finding is resolved by linking the modeled-host and exact-binary proof boundary while retaining its native-host assumptions.

## Talos relationship and proof scope

Talos supplies the WebAssembly semantics used by the Lean proofs.  LeanExe emits a module, the source-driven proof tools regenerate its Talos representation, and the Lean kernel checks the behavioral theorem.  The exact-binary path additionally proves decoding, validation, and translation of the embedded binary.  The [Talos Proofs guide](proofs/talos/README.md), [verification procedure](docs/verifying.md), and [artifact format](docs/artifact-format.md) define those paths.

### Existing compiler proof checks

The immediate obligation is to recheck existing programs after the shared extraction, ownership, loop-emission, and integer-encoding changes.  A source-driven check compares a regenerated candidate with the tracked `Program.lean`, then checks the registered specification.  A changed instruction stream requires review of the new proof subject and any affected proof.

`tools/talos-proof.js check --all` is the aggregate source-driven check.  `tools/talos-artifact.js prepare <case>` explicitly refreshes a generated cache.  Handwritten edits to `Program.lean` are prohibited.  Frozen exact-artifact packages retain their own bytes and identity; any deliberate replacement requires artifact and proof review.

`tools/talos-proof.js check --all` passes on 2026-09-24: all 69 regenerated caches match, registry/import checks pass, and the complete library builds for all 68 registered complete specifications. The retained partial sequence-softmax proof also passes separately; the full sequence registration remains incomplete as before. The completed source gate covers the compiler ownership changes, including current GCD, CLOB, Euler, cached GPT-2, LEB, and tiny-model instruction streams. Public model input ranges and numerical contracts are preserved. The LEB encoder returns an existential root because buffers can be reused, with explicitly typed runtime release-counter slots. No new axiom or admitted proof term was introduced. Evidence is recorded in the journal; frozen release identity remains deferred.

### Completed non-release execution inventory on this Mac

The non-release inventory passes the runner, artifact identity/conformance/migration unit checks, proof-tool unit checks, classification, floating-point, packed-data, Euler/WASM, matched-value, ASCII, integer-map, JSON, WASI adapter, and fuzz suites.  Standard comparisons pass all 340 native Lean/Wasm cases and 62 IR interpreter cases, including the string-constant byte result affected by this repair.  The pure-WASI rerun passes 33 execution cases, two traps, nine rejections, and 16 compiles with the local cache; fuzz validation passes 56 cases.

The C comparison now passes with `CC=/opt/homebrew/bin/gcc-15 node test/euler_rusanov_c.js`.  The driver accepts GCC's documented `__GCC_IEC_559 >= 2` advertisement while preserving all runtime format, evaluation-width, layout, rounding, strict-flag, and exact-word checks.  All eight mirror rows and seven Lanyon rows match the pinned CSV, whose bytes are unchanged.  The regression manifest records updated local source identities; vendored upstream source and frozen artifacts are unchanged.  The default Mac Clang still lacks the required advertisement, so the C comparison uses the explicit `CC` override.

### Formal I/O proofs: included in completion

The separate [byte-I/O proof gate](proofs/byte-io/README.md) now specifies all six generated WASI imports using pinned Talos `HostFn`, relational contracts, and `HostEnv.Satisfies`. It proves read/write prefix effects, EOF, bounded memory changes, preservation of other store resources, nonblocking flags, monotonic clock observations, canonical two-subscription polling, and exit status. Protocol theorems preserve byte order and the original saturated deadline, characterize successful complete output, and prove termination under explicit retry-clock progress.

A separate import-bearing binary profile proves decoding, validation, and translation without changing the existing import-free profile or frozen packages. The representative 2,082-byte echo binary has SHA-256 `a4eef742abcf9f01336de122839ebbc9db18a469a70d9ee11ac7586ac4615be5`. Six kernel-checked execution theorems cover partial writes, EOF, a committed prefix before a broken pipe, retry after readiness, absolute-deadline expiry, and the exported `_start` exit. Memory ownership checks include balanced allocation/free counts. The complete maintained gate compares the bytes with fresh compiler output and audits the public theorem axioms.

These are modeled-host and concrete generated-program theorems. They are not a universal compiler-refinement proof for every I/O program. Native C, Wasmtime, and the OS remain outside the proof boundary. A final nonblocking syscall may finish after the last clock observation; no strict wall-clock return guarantee is asserted. Release identity remains deferred. Existing compiler source-proof validation is complete.

## Environment and commands

### Current checkout

The user authorized local Lean execution on this Mac.  `tools/macos-env.sh` selects the repository's Darwin runner and pinned tools.  Existing tool installations are linked into ignored `build/tools`; the pinned proof packages were copied into this checkout using APFS file clones, so proof builds cannot modify the earlier checkout's dependencies.

| Requirement | Current selection |
|-------------|-------------------|
| Lean and Lake | `leanprover/lean4:v4.34.0-rc2`, required commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.  Compiler and fixtures built successfully. |
| Talos | Materialized CodeLib revision `87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47`, matching the proof manifest. |
| Node | `24.13.0`; version check passed. |
| Wasmtime | Pinned `44.0.0` CLI and C API.  Both native hosts compiled here. |
| wasm-tools | `1.251.0`; version check passed. |
| Runner | ARM macOS local mode, shared lock, one Lean thread, timeout, and the repository's authorized inherited-priority fallback.  No Linux cgroups or ionice. |

`WASMTIME`, `WASMTIME_C_API`, `WASM_TOOLS`, `LEAN_WASM_EXE`, and `LEANEXE_WASI_IO_HOST` select external or built tools.  For this checkout, sourcing `../work/io-env.sh` selects the session overrides.  Reruns use the pinned Wasmtime CLI through a wrapper supplying `-C cache-config` with a writable directory under `build/cache/wasmtime`.  All Lean processes still use `tools/leanrun` serially.  No dependency versions changed.

### Execution rules

Read [Repository Instructions](AGENTS.md) and [Developing LeanExe](DEVELOPING.md) before running Lean, and use the repository runner.  The `leanrunner` skill referenced by the earlier handoff is not installed in this session.  Every direct Lean, Lake, or compiler invocation goes through `tools/leanrun`.  Standard mode enforces the shared machine-wide lock, one Lean thread, `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=1G`, `CPUQuota=100%`, nice priority 10, and idle I/O priority.  Lean jobs run serially.

Use bounded command and lock waits.  A target that times out without a diagnostic requires a smaller elaboration boundary or a checked supporting lemma before another attempt.  If the required user scope or cgroup limits fail, follow the repository's approval rule.  The user explicitly authorized local Lean execution for this resumed Mac session.  `LEANRUN_LOCAL=1` is selected through the repository's macOS environment script.

The Node drivers use [the process runner](tools/run-process.js), which sends their Lean children through `tools/leanrun`.  Invoke those drivers directly.  In authorized local mode, place the variable on the driver.  Nesting runners would reacquire the same lock.

### Focused commands after setup

The initial build supplies the compiler and fixtures needed by the focused tests:

```sh
tools/leanrun --timeout 15m --lock-timeout 60 lake build lean-wasm LeanExe.Examples.ByteIO LeanExe.Examples.Correctness LeanExe.Examples.ByteArrayPrograms LeanExe.Wasm.ImageIntegrationTest
node test/wasi_io_host.js
node test/byte_io.js
node test/refcount.js
node test/self_emit.js
tools/check-wat.sh
```

Run each command serially and record its result.  The I/O test drivers build their host.  The source I/O driver also builds its source module and compiler, compiles each fixture, and runs `wasm-tools validate` on each artifact.  The reference-counting tests use the ordinary Wasmtime host.

The documented echo example, after the build and host setup above, is:

```sh
tools/leanrun --timeout 2m --lock-timeout 60 .lake/build/bin/lean-wasm compile-wasi-io --module LeanExe.Examples.ByteIO --entry LeanExe.Examples.ByteIO.echo --out build/echo.wasm
printf 'abcd' | build/tools/leanexe-wasi-io-host build/echo.wasm
```

The compiler supports `report`, `dump-ir`, `ownership-report`, and `compile-wat` for their documented modes.  Establish each diagnostic's support for the entry under investigation.  The present `compile-wat` command follows pure compilation and rejects the effectful echo fixture.  `wasm-tools print` can inspect the compiled I/O binary.

### Broader checks

Use the [aggregate execution driver](test/run_all.js) as the inventory of required builds and tests.  It currently runs release checks before the compiler and runtime suites and has no selection option.  With release work deferred, invoke the remaining constituent checks directly in their required order and record coverage.  Report the constituent results and the aggregate's deferred status.  A change to test selection in the maintained driver is a separate implementation decision.

The affected areas include core correctness, ownership reporting, reference counting, byte-array allocation, existing WASI adapters, CLI errors, source/IR comparisons, and compiler serialization.  Complete the broader inventory after focused repairs pass.  Preserve failures and compare inherited behavior with the base revision.

```sh
tools/talos-proof.js check --all
git diff --check
tools/check-docs.js
```

Keep each repository verification tool as the first command token.  Use the checked case configuration, ordinary path arguments, and tool-prefix approvals.  Frozen artifact changes also require the focused artifact check and `tools/artifact-proof.js check-all` under the repository's development rules.  Release-identity checks remain deferred.

The current documentation checker omits root `task.md` and `devnotes.md` from its file inventory.  Review their local links and examples in addition to running that checker.  The commands above have been reviewed against the scripts.  Execution results belong in the journal when they are run.

## Completion agenda

The proposed order below preserves the scope discussed in this session.  Implementation choices that change the API, host model, supported diagnostics, proof scope, or dependencies require confirmation.

- [x] Establish the pinned local tools and authorized runner mode, then reproduce the focused I/O, host, ownership, and encoding results.
- [x] Check both reported ownership defects: preserve passing array-alias regressions and repair the reproduced string-literal leak with failing-before/passing-after tests.
- [x] Review shared ownership and effect rules across retained buffers, conditional replacements, nested loops, helper calls, ignored results, and early returns.  Repair the newly reproduced nested-loop final-buffer leak and pass 47 I/O cases, four pure rejections, and 48 reference-counting cases.
- [x] Resolve the C comparison portability gate.  Every non-release execution suite and all 13 WAT/binary checks pass.
- [x] Complete existing Talos source-driven checks, diagnose inherited failures against the base, and review every changed generated program before updating its cache or proof.
- [x] Reconcile the overview, manual, specification, compiler documentation, and development instructions.  Test the new CLI's required error behavior.
- [x] Record the resumed revision, local changes, per-command results, remaining failures, and agreed exclusions in this document and the journal.
- [x] Include formal byte-I/O host proofs, as requested by the user.
- [x] Prove the modeled host contracts and byte-transfer protocol, connect representative generated WASM to Talos execution, and record assumptions and axiom audits. The maintained gate passes all 46 public-theorem audits.

The current implementation task is complete: I/O behavior and the included ownership defects pass their execution checks, compiler source-proof validation passes, modeled byte-I/O host and protocol proofs are checked, and the documentation records their assumptions. The execution aggregate itself remains deferred because it includes release checks; all non-release execution constituents passed separately. Release identity remains deferred.

## Maintenance

After each work session, update the implementation revision, current environment observations, evidence table, next unchecked tasks, and open decisions.  Record new tests with their command, revision, result, and retained evidence path when available.  Move detailed investigation history into the development journal and keep this document focused on the current state.  The previous journal records a request for frequent commits and pushes.  Preserve reviewable changes and record the branch state when publishing authorized work.
