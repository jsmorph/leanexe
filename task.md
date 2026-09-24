# Byte I/O completion

## Current state and scope

Updated 2026-09-24.  Work continues on branch `io`, tracking `origin/io`, at implementation commit `fb19b5efdd6cc171033adf888667764203c14f14` (Document completed byte I/O behavior and tests).  Its base is `a4655383ee80d3d80830b6bddfb6248a9d5c2b4b` on `main`.  The branch contains eight commits beyond that base.  The working tree was clean before this continuation document and its journal entry were added.

The current task is to complete primitive byte I/O, validate its shared compiler changes, and reconcile the documentation.  The user deferred release-identity work on 2026-09-24.  Release receipts, release-input digests, and cold release verification remain deferred.  Formal verification of the new I/O operations is an open scope decision.  Rechecking the existing Talos proofs is part of compiler validation.

This document owns the current continuation agenda.  The [Development Journal](devnotes.md#2026-09-23-byte-io-on-branch-io) preserves the implementation history and reported test evidence.  Its September 23 entry contains both intermediate and final results.  The latest reported I/O count is 38 execution cases.  The earlier counts of 26 and 30 describe intermediate revisions.

The resumed session has inspected source and documentation.  Compiler, execution, and proof tests have not run in this session.  The evidence table below distinguishes prior reports from current observations.

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

### Open ownership defects

The [core correctness example](LeanExe/Examples/Correctness.lean) `arraySetIfInBoundsSkipsValueTrap` expects `7`.  Its out-of-bounds update preserves the original array.  The previous session diagnosed generated code that aliases that array and releases both aliases.  A clean build of the base revision produced the same trapping module, with SHA-256 `0dd850af132112b6bde0a76bbd66507d4a427a5a8b36866df9cd0f672eb96866`.  Reproduce the failure, inspect the extracted ownership and emitted releases, and repair the ownership rule at its cause.

An earlier version of `carryReads` seeded its initial buffer from a string literal.  That version exposed an unreleased inner `arrayAllocSlots` during literal construction.  The current fixture obtains its initial buffer from `read`, so its passing counter check covers read-buffer ownership.  Recover or reduce the literal-construction example and retain a focused test before repairing the leak.  The journal identifies the allocation but supplies no completed repair.

The baseline comparison establishes that the array double-release predates this branch.  The literal leak's origin remains to be established.  Both belong in the proposed ownership completion work because they affect memory operations available to I/O programs.

### Documentation and diagnostics

The [user manual](docs/manual.md#entry-shapes) still describes every entry as pure and omits `compile-wasi-io` from its entry table.  Its memory-management section describes the previous accumulator-release rule.  The root [Repository Overview](README.md) also introduces the language as pure.  The specification and status document received I/O edits, while the manual, overview, compiler guide, and development instructions need reconciliation.

The existing [CLI error tests](test/cli_errors.js), [classification tests](test/report_classification.js), and [ownership-report tests](test/ownership_report.js) contain no `ByteIO` or `compile-wasi-io` cases.  Review the intended diagnostic support and test the new command's entry rejection, unsupported effects, usage errors, and output-file failures through the existing error interface.  Any extension of reporting or WAT commands needs a scope decision before implementation.

On 2026-09-24, `tools/check-docs.js` reproduced the journal's documentation failure in [WGSL review notes](paper/wgsl-verification-report/review.md): an absolute temporary-workspace path.  That file is unchanged.  The continuation document's 46 local links and whitespace checks passed, as did `git diff --check` for the tracked edit.

## Talos relationship and proof scope

Talos supplies the WebAssembly semantics used by the Lean proofs.  LeanExe emits a module, the source-driven proof tools regenerate its Talos representation, and the Lean kernel checks the behavioral theorem.  The exact-binary path additionally proves decoding, validation, and translation of the embedded binary.  The [Talos Proofs guide](proofs/talos/README.md), [verification procedure](docs/verifying.md), and [artifact format](docs/artifact-format.md) define those paths.

### Existing compiler proof checks

The immediate obligation is to recheck existing programs after the shared extraction, ownership, loop-emission, and integer-encoding changes.  A source-driven check compares a regenerated candidate with the tracked `Program.lean`, then checks the registered specification.  A changed instruction stream requires review of the new proof subject and any affected proof.

`tools/talos-proof.js check --all` is the aggregate source-driven check.  `tools/talos-artifact.js prepare <case>` explicitly refreshes a generated cache.  Handwritten edits to `Program.lean` are prohibited.  Frozen exact-artifact packages retain their own bytes and identity; any deliberate replacement requires artifact and proof review.

The base development plan also records an existing `gcd` generated-cache mismatch.  The September 23 I/O session stopped earlier, during dependency download.  Re-establish the first current failure and compare it with the base before assigning a cause to the I/O changes.

### Formal I/O proofs: scope decision pending

There is no registered `ByteIO` proof case.  The current [binary decoder](proofs/talos/lean/Project/Artifact/Binary/Decode.lean) rejects import sections.  The [translation field theorem](proofs/talos/lean/Project/Artifact/Binary/Proof/Translate.lean) records an empty import list for every accepted module.  This restriction belongs to this repository's exact-binary verification profile.  The pinned upstream Talos support for host calls requires inspection before choosing an extension.

A proof of an I/O program needs a model of the host interaction: returned bytes, partial transfers, EOF, errors, memory writes, descriptor state, clock observations, polling results, and exit.  The model must state which memory regions each host call may change.  A streaming theorem could relate bytes read to bytes written, preserve their order, describe prefixes emitted before failure, and account for buffer lifetimes.

Whole-operation deadline reasoning must include partial progress and interruptions.  Termination and claims about elapsed time require explicit assumptions about clock progress, polling, and host scheduling.  A theorem over modeled WASI calls relies on the host satisfying that model.  Verification of the C host, Wasmtime, or operating system would require further scope decisions.

If the user includes formal I/O verification in completion, agree on the theorem and host assumptions first.  The resulting work would include inspection of pinned Talos import semantics, a source I/O specification, required execution rules and lemmas, import syntax/decoding/validation/translation with their soundness proofs, and an exact-binary theorem for a representative I/O program.  Existing Talos checks establish the status of existing verified programs.  I/O execution tests establish the recorded runtime cases.

## Environment and commands

### Current checkout

| Requirement | Pin or observation on 2026-09-24 |
|-------------|---------------------------------|
| Lean and Lake | `leanprover/lean4:v4.34.0-rc2`, required commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`.  The matching elan toolchain directory exists.  The executable and commit have not been tested in this session. |
| Talos | `87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47`, pinned by the proof Lake files. |
| Node | Required and observed version `24.13.0`. |
| Wasmtime | Required CLI and C API version `44.0.0`.  The repository `build/tools` directory is absent, and `wasmtime` is absent from `PATH`. |
| wasm-tools | Required version `1.251.0`.  The command is absent from `PATH`. |
| C compiler and scope launcher | `cc` and `systemd-run` are on `PATH`.  Scope creation and resource enforcement remain untested. |
| Build state | The compiler executable, compiled WASI I/O host, and proof dependency directory are absent. |

The prior session's tool installations and partial Mathlib download are historical.  Setup on this checkout starts from the observations above.  Consult the [development prerequisites](DEVELOPING.md#prerequisites) and ask for missing required tools before execution.  Existing setup commands include `tools/download-wasmtime.sh`, `tools/build-wasmtime-host.sh`, and `tools/build-wasi-io-host.sh`.  New dependencies and dependency changes require approval.

`WASMTIME`, `WASMTIME_C_API`, `WASM_TOOLS`, `LEAN_WASM_EXE`, and `LEANEXE_WASI_IO_HOST` select external or built tools.  In particular, the I/O Node drivers use `WASM_TOOLS` or `wasm-tools` on `PATH`.  Record any overrides with test results.

### Execution rules

Read [Repository Instructions](AGENTS.md) and [Developing LeanExe](DEVELOPING.md) before running Lean, and use the installed `leanrunner` skill.  Every direct Lean, Lake, or compiler invocation goes through `tools/leanrun`.  Standard mode enforces the shared machine-wide lock, one Lean thread, `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=1G`, `CPUQuota=100%`, nice priority 10, and idle I/O priority.  Lean jobs run serially.

Use bounded command and lock waits.  A target that times out without a diagnostic requires a smaller elaboration boundary or a checked supporting lemma before another attempt.  If the required user scope or cgroup limits fail, follow the repository's approval rule.  The September 23 journal records local-mode authorization in that earlier environment.  The resumed checkout has not established a need for local mode.  `LEANRUN_LOCAL=1` requires applicable explicit authorization and must never activate implicitly.

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

- [ ] Establish the pinned local tools and runner limits, then reproduce the focused I/O, host, ownership, and encoding results.
- [ ] Reproduce and repair the array alias double-release and string-literal allocation leak, preserving focused failures as tests.
- [ ] Review the shared ownership and effect rules across retained buffers, conditional replacements, nested loops, helper calls, ignored results, and early returns.  Add cases where the review identifies a specific coverage gap.
- [ ] Complete the non-release aggregate execution inventory and repeat WAT/binary checks after the final ownership changes.
- [ ] Complete existing Talos source-driven checks, diagnose inherited failures against the base, and review every changed generated program before updating its cache or proof.
- [ ] Reconcile the overview, manual, specification, compiler documentation, and development instructions.  Test the new CLI's required error behavior.
- [ ] Record the final revision, per-command results, remaining failures, and agreed exclusions in this document and the journal.
- [ ] Obtain a scope decision on formal I/O proofs before extending host semantics or the exact-binary verification profile.

Completion of the current implementation work requires tested I/O behavior, resolution of the ownership defects included in scope, completed compiler and existing-proof validation or explicit decisions on remaining failures, and documentation matching the implementation.  Release identity remains deferred.  The status of formal I/O verification must remain explicit.

## Maintenance

After each work session, update the implementation revision, current environment observations, evidence table, next unchecked tasks, and open decisions.  Record new tests with their command, revision, result, and retained evidence path when available.  Move detailed investigation history into the development journal and keep this document focused on the current state.  The previous journal records a request for frequent commits and pushes.  Preserve reviewable changes and record the branch state when publishing authorized work.
