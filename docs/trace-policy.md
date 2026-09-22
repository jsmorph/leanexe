# Trace policy example

This is a pure Lean policy and a synthetic trace harness. It performs no
filesystem operations and has no ptrace supervisor, strace parser, permissions
model, or host integration. The policy is Lean source, not a policy data file.

The [implementation](../LeanExe/Examples/TracePolicy.lean) allows:

- Reads from files strictly below `/job/input`.
- Writes, creation, and truncation strictly below `/job/output`.
- At most 1,048,576 bytes of successful file writes across the entire trace.
- Reads from the supplied stdin capability and writes to the supplied stdout
  and stderr capabilities. Standard-stream writes do not consume the file budget.

`readWrite` opens must satisfy both directory rules. These roots are disjoint,
so this first policy rejects them. Read-only creation is still a mutation and
must satisfy the output rule. Truncation requires write access and is checked
before the open completes.

## Try the samples

From the repository root, with the pinned Lean toolchain installed:

```sh
tools/trace-policy
tools/trace-policy --list
tools/trace-policy copy
tools/trace-policy budget-exceeded
node test/trace_policy.js
```

The driver builds only the example module and runs the native Lean harness.
Both commands use `tools/leanrun` and its normal resource policy. Environment
overrides follow [Developing LeanExe](../DEVELOPING.md); the driver never
enables local mode automatically.

With no arguments the harness checks every sample against an explicit expected
reason, failing event index, and byte total. Selecting a sample prints its
events. `PASS ... STOP ...` means the policy correctly rejected a trace that
the sample expected to reject. A mismatched expectation fails the harness.

Samples live in [TracePolicyHarness.lean](../test/TracePolicyHarness.lean).
Add a record to `samples`, using the small `opened`, `readBytes`, `writeBytes`,
and `closed` helpers. They construct data; they do not touch real files.

```lean
{ name := "small-output",
  events := opened "output/report" .writeOnly 3 true true ++
    writeBytes 3 20 12 ++ closed 3,
  written := 12 }
```

The example requests a 20-byte write but records a 12-byte completion. Only 12
bytes consume the budget. A request larger than the remaining allowance is
rejected before its result, even if it might have transferred fewer bytes.

## Model

`Request` contains `open`, `read`, `write`, and `close`. `OpenRequest` represents
access mode, creation, and truncation directly; it does not decode Linux flag
words. `Outcome.ok` contains a returned descriptor, transferred byte count, or
zero for close. `Outcome.error` is terminal in this version.

Events alternate between `before request` and `after outcome`. At most one
request is pending. `authorize` decides admission, `observe` accounts for a
result, and `step` enforces their ordering. Once stopped, all subsequent calls
to `step` preserve that state. The batch `check` function starts from the known
initial state, reports the first failure, and rejects a missing final result.

The descriptor table has 256 slots. Initially only 0, 1, and 2 are occupied.
An open result must name a free slot. Close frees a slot. Reusing a standard
stream's descriptor number for a file grants ordinary file access and budget
accounting, not the old stream capability. There are no aliases or inherited
descriptors beyond those three initial capabilities.

Paths are byte components, so non-UTF-8 names are supported. Relative names
start at the fixed `/job` working directory. Containment uses whole components
and requires a strict descendant. Repeated slashes and interior `.` components
are accepted. Empty paths, NUL bytes, `..`, trailing `/` or `.`, and paths over
4096 bytes are rejected. These are deliberate model restrictions, not a full
implementation of Linux path resolution.

The model assumes a stable directory tree containing ordinary files and
directories, with no symlinks, hard-link aliases, mount changes, or concurrent
external mutations. No filesystem snapshot is read or authenticated. The
checker evaluates supplied events; it does not establish that those events
describe a real execution.

Acceptance allows open descriptors at the end: cleanup is not part of this
first policy. Reads from writable output files are also outside this policy.
The write counter measures transferred file bytes, not final file sizes, disk
allocation, durability, or the amount removed by truncation.

## Verification boundary and next steps

The initial deliverable is the source policy and native Lean sample harness.
The harness checks 46 traces and admission/completion state transitions. The
Node regression also checks sample selection and unknown-sample exit status.
Tests are regression evidence. There is no claimed policy-correctness theorem,
compiled-WASM execution theorem, or operating-system enforcement guarantee.

LeanExe's `report` accepts `LeanExe.Examples.TracePolicy.check`, and `compile`
emits its WASM. The current harness exercises native Lean; WASM execution and
proofs are subsequent work. The source uses concrete first-order types, byte
arrays, bounded integer accounting, and supported loop forms. `Path` is a
structure because the current extractor does not unfold a type abbreviation in
this state layout. Path parsing, descriptor bookkeeping, and `authorize` are
separate definitions. Later ownership and permission state can extend the model
without changing the request/result split.
