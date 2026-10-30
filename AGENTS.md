# Repository Instructions

## Lean Process Limits

- Run every `lean`, `lake`, and Lean compiler command through [`tools/leanrun`](tools/leanrun).  In standard mode the runner enforces `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=1G`, `CPUQuota=100%` over a 100 ms period, `nice -n 10`, and `ionice -c 3`, and it sets `LEAN_NUM_THREADS=1`.
- The runner acquires the same machine-wide lock as `../vq/tools/leanrun`.  Never bypass the runner.  Lean and Lake processes run concurrently on one host only inside one runner command.  The user has authorized concurrent runs on separate hosts, each through its own resource-limited runner.
- `--threads N` sets `LEAN_NUM_THREADS=N`.  Lake takes its number of parallel jobs from `LEAN_NUM_THREADS`, and each Lean process uses it for its own tasks.  `--cpus N` sets `CPUQuota` to `N` CPUs, and `--cpus auto` uses every online CPU.  Without `--cpus` the quota equals the thread count, and without `--threads` the thread count equals the `--cpus` count, or 1 when neither is given.  `LEANRUN_THREADS` and `LEANRUN_CPUS` supply these settings to repository drivers.  The user has authorized more than one thread.
- Memory and swap limits apply to the whole job, so its threads share one `MemoryHigh`.  On an 8-CPU host with about 12 GiB of memory, three threads with `--memory-high 9G` or `10G` avoid paging, and eight threads under the 4 GiB default thrash.  Run a known memory-heavy proof alone with fewer threads when concurrent heavy proofs cause thrashing.  Monitor swap traffic, memory stalls in `/proc/pressure/memory`, and user versus system CPU time when choosing concurrency.
- `--memory-high SIZE` selects a memory high limit in whole gibibytes, such as `10G`, and a maximum 2 GiB above it.  The default limits remain 4 GiB high and 6 GiB maximum.  The full numerical proof builds recorded in the journal use `10G` for the lgamma root-range proofs.  Set `LEANRUN_MEMORY_HIGH=10G` for the full `tests/verified/run.sh`, `tests/wasi/run.sh`, and `tests/running-sumfp/run.sh` drivers: the printer's file check paged under the 4 GiB high limit, and the initial combined parser and printer WASI build recorded a 4.84 GiB memory peak.
- Add a reasonable `timeout` to diagnostic commands whose runtime is not intrinsically bounded.
- After a target reaches its timeout without a diagnostic, do not run the unchanged target again.  First divide the proof or module, or add a verified reusable lemma that reduces the elaboration boundary.
- Pass `--timeout` for a command-specific limit and `--lock-timeout` when the default 900-second lock wait is unsuitable.  Keep `tools/leanrun` as the first command token so one approval covers every Lean target.  If the runner cannot create its user scope or enforce the required cgroup properties, stop and ask the user; the only exception is the explicitly authorized local mode below.
- Only after the user explicitly authorizes local execution without a systemd cgroup may `LEANRUN_LOCAL=1` be set on the repository driver or `tools/leanrun` invocation.  This opt-in mode retains the pinned toolchain, shared lock, timeout, selected Lean worker count, `nice`, and `ionice`, but it warns that CPU, memory, and swap cgroup limits are absent.  It never activates implicitly.  Invoke runner-calling repository drivers directly with the variable rather than wrapping the driver in `tools/leanrun`; nested local-mode runner calls fail immediately because they would otherwise wait on the same non-reentrant lock.
- Do not wrap `tools/leanrun` in another resource scope.  Do not substitute an address-space limit such as `ulimit -v` or `prlimit --as`.

The standard command form is:

```bash
tools/leanrun --timeout <duration> <lean-or-lake-command>
```

## Python Programs

- Run every Python program in this repository with `uv run PATH`, never with `python3` or a hand-made virtual environment.  Each program declares `requires-python = ">=3.12"` and its pinned dependencies in a PEP 723 `# /// script` block, and a new program must do the same.

## Approval Boundaries

- Reuse saved command approvals through normal execution.  If a sandbox failure requires escalation, request a reusable prefix for the repository driver or command category.
- Transfer saved command output from a remote host by writing a file remotely and fetching it with `rsync`.  Keep Tailscale SSH and `rsync` invocations as separate direct commands.  Local redirection and shell wrappers can prevent reusable approval matching.
- The user has granted reusable authorization to cancel and restart our own test jobs after a diagnosed configuration error.  Leave unrelated jobs untouched.  Restarts must use `tools/leanrun`, its shared lock, and the documented resource limits.
- Keep the repository driver as the first command token for verification runs: [`tests/modules/run.sh`](tests/modules/run.sh), [`tests/gpt/run.sh`](tests/gpt/run.sh), [`tests/wgsl/run.sh`](tests/wgsl/run.sh), [`tests/gpt32/native.sh`](tests/gpt32/native.sh), [`tests/drone/oracle.sh`](tests/drone/oracle.sh), [`tests/verified/run.sh`](tests/verified/run.sh), [`tests/wasi/run.sh`](tests/wasi/run.sh), [`tests/running-sum/run.sh`](tests/running-sum/run.sh), [`tests/running-sumfp/run.sh`](tests/running-sumfp/run.sh), [`tools/demo-check`](tools/demo-check), [`tools/verified-request-check`](tools/verified-request-check), or [`tools/full-check`](tools/full-check), each of which calls [`tools/leanrun`](tools/leanrun) itself.  Request approval for that driver prefix rather than one case, module, corpus file, temporary path, or internal child command.
- Put repeatable corpus membership and expected results in the driver's checked files, such as an example's `Cases.lean` under [`Examples/`](Examples).  Do not place globs, brace expansions, generated file lists, pipes, or shell wrappers around a repository verification command.
- Use direct `tools/leanrun` commands only for focused diagnostics that do not belong in an existing repository gate.  Keep `tools/leanrun` as the first token and pass file paths as ordinary arguments without shell expansion.

## Proof Iteration

Treat accepted theorems and [the LeanExe compiler manual's full check](docs/leanexe-manual.md#the-full-check) as gates.  The full check is [`tools/full-check`](tools/full-check), which writes [`STATUS.md`](STATUS.md).  Evaluate each iteration across proof-generation time, successful LTG retrieval, agent revisions, proof structure and size, shared abstraction use, compiler hint use, and applicability beyond the measured program.  No single measurement determines retention or promotion.  Do not treat raw source bytes, word length, or identifier length as proof complexity.  Longer declaration names often record useful shared theorem use.  Consider lines, explicit syntax, local scaffolding, repeated derivations, and shared theorem or tactic use.  After every proof run, review the journal and the accepted proof together.  Use that evidence to consider changes to compiler hints, shared lemmas, tactics, and guidance, as well as the instructions that govern proof generation and journaling.

Keep journals as frequent, natural prose.  They should identify supplied help that worked or failed, explain changes of approach, and note missing general abstractions.  Test changes on fixed modules, preserve failures, and use diverse or held-out demos to avoid problem-specific optimization.

Preserve checked narrow or program-specific LTG material as worked examples by default.  Generality and recurring evidence determine importability, automatic selection, and promotion, while specificity alone does not justify deletion.  Remove an example only when it is invalid, stale, unsafe to disclose to a measured proof task, or duplicated without a distinct lesson.

## Verification Knowledge Base

[The verification knowledge base](VKB/README.md) holds lemmas, proof recipes, worked examples, and recorded failures for proofs about programs of the verified compiler.  Before a proof task, search its entries for the declarations and goal shapes at hand.  After the task, propose new entries or changes in the form of [the template](VKB/TEMPLATE.md), in the task's report or as files under `VKB/entries/`.  A reviewer admits a proposal when its guidance applies beyond the task, its declarations exist, and no entry already covers it, and `VKB/Check.lean` must pass after every admitted change.
