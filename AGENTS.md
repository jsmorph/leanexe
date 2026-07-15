# Repository Instructions

## Lean Process Limits

- Run every `lean`, `lake`, and Lean compiler command under an enforced cgroup memory limit.  Use `MemoryHigh=4G`, `MemoryMax=6G`, and `MemorySwapMax=1G` unless the user approves different limits.
- Run those commands with `nice -n 10` and `ionice -c 3`.
- Set `CPUQuota=100%` on the cgroup so all child processes share at most one CPU core.  Lake 5.0.0 has no job-count option.  Never run Lean or Lake processes concurrently.
- Add a reasonable `timeout` to diagnostic commands whose runtime is not intrinsically bounded.
- After a target reaches its timeout without a diagnostic, do not run the unchanged target again.  First divide the proof or module, or add a verified reusable lemma that reduces the elaboration boundary.
- Use `systemd-run --user --scope --quiet --collect` to create the resource-limited scope.  If user scopes or the required cgroup properties are unavailable, stop and ask the user.  Do not run the command without a memory limit, and do not substitute an address-space limit such as `ulimit -v` or `prlimit --as`.

The standard command form is:

```bash
systemd-run --user --scope --quiet --collect \
  -p MemoryHigh=4G \
  -p MemoryMax=6G \
  -p MemorySwapMax=1G \
  -p CPUQuota=100% \
  nice -n 10 ionice -c 3 \
  timeout <duration> <lean-or-lake-command>
```
