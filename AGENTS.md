# Repository Instructions

## Lean Process Limits

- Run every `lean`, `lake`, and Lean compiler command through `tools/leanrun`.  The runner enforces `MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=1G`, `CPUQuota=100%`, `nice -n 10`, and `ionice -c 3`.
- The runner acquires the same machine-wide lock as `../vq/tools/leanrun` and sets `LEAN_NUM_THREADS=1`.  Never bypass the runner or run Lean or Lake processes concurrently.
- Add a reasonable `timeout` to diagnostic commands whose runtime is not intrinsically bounded.
- After a target reaches its timeout without a diagnostic, do not run the unchanged target again.  First divide the proof or module, or add a verified reusable lemma that reduces the elaboration boundary.
- Pass `--timeout` for a command-specific limit and `--lock-timeout` when the default 900-second lock wait is unsuitable.  Keep `tools/leanrun` as the first command token so one approval covers every Lean target.  If the runner cannot create its user scope or enforce the required cgroup properties, stop and ask the user.
- Do not wrap `tools/leanrun` in another resource scope.  Do not substitute an address-space limit such as `ulimit -v` or `prlimit --as`.

The standard command form is:

```bash
tools/leanrun --timeout <duration> <lean-or-lake-command>
```

## Approval Boundaries

- Keep the repository tool as the first command token for verification runs: `tools/talos-artifact.js`, `tools/talos-proof.js`, `tools/artifact-proof.js`, `tools/artifact-conformance.js`, or `tools/artifact-release.js`.  Request approval for that tool prefix rather than one subcommand, artifact, corpus file, temporary path, or internal child command.
- Put repeatable corpus membership and expected results in the tool's checked configuration.  Do not place globs, brace expansions, generated file lists, pipes, or shell wrappers around a repository verification command.
- Use direct `tools/leanrun` commands only for focused diagnostics that do not belong in an existing repository gate.  Keep `tools/leanrun` as the first token and pass file paths as ordinary arguments without shell expansion.

## Artifact-Proof Iteration

Treat proving time as the primary metric and accepted proof structure and size as secondary metrics.  Do not treat raw source bytes or identifier length as proof complexity; consider lines, syntax, local scaffolding, and shared theorem use.  After every proof run, review the journal, accepted proof, and telemetry together.  Use that evidence to consider changes to compiler annotations, shared lemmas, tactics, and guidance, as well as the instructions that govern proof generation and journaling.

Keep journals as frequent, natural prose.  They should identify supplied help that worked or failed, explain changes of approach, and note missing general abstractions.  Test changes on fixed artifacts, preserve failures, and use diverse or held-out demos to avoid problem-specific optimization.
