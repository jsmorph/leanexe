# Stream fold

StreamFold holds the line-stream process of [Running sum](../RunningSum/README.md) and [the binary64 running sum](../RunningSumFp/README.md), with the proofs that both applications share.  A line kernel of type `Kernel Acc` maps an accumulator and a line to a validity bit, the next accumulator, and the bytes to write for the line.  `process kernel seed` reads chunks of at most 4,096 bytes, retains a partial line across reads, and writes the output of each line before it consumes more input.  It stops with status 28 at the first line that the kernel rejects, and with status 0 at EOF.  Each application states its own process and relates it to `process` by `Process.Rel` in its stream view.

## Model

The model consumes the input one byte at a time.  `Model.outcome kernel state bytes` gives the outputs and the status of the model: status 0 when the kernel accepts every line, including a last line without LF, and status 28 when the model stops at a rejected line, with the outputs of the lines before it.  `Model.lines` splits a byte list into the segments that LF ends and a nonempty final segment, and `Model.foldOutcome` applies the kernel to those lines up to the first rejected one.  `outcome_initial` states that the two agree from the initial state.

`LineValues Denotes lines values status` states the specification of an application in terms of a line predicate `Denotes`.  `values` holds the values of the lines before the first line without a value, and `status` is 0 when every line has a value and 28 when one does not.  `LineValues.unique` shows that a functional predicate determines both.  Each application proves that `foldOutcome` of its kernel matches `LineValues` for its own predicate.

## Theorems

`initial_terminates_output` states that, from the initial state, the process returns the status of `foldOutcome kernel seed (lines input)` after writing the outputs of the same fold.  When the status is 0, it has read the whole input.  `process_exec_correct` states that every finite execution from a state satisfying the stream invariant `StreamFuture` returns that status after writing those outputs, and `process_terminates` shows that some execution returns status 0 or 28.

| Premise | Requirement |
|---|---|
| [Kernel](Interface.lean) | `KernelSpec` supplies an invariant `Good` of the accumulator and a size condition `Room` for a line.  An accepted line keeps `Good` and produces nonempty output of fewer than `2^64` bytes. |
| [Line sizes](Model.lean) | `LineRooms` requires `Room` for each line up to and including the first rejected line. |
| [Host](StreamHost.lean) | `StreamHost` supplies successful reads and writes, consumes input prefixes, reports an empty read only at EOF, and commits output prefixes.  Each zero-byte write decreases a proof-only credit, and a read or a write of at least one byte may set the credit to any value. |

The compiled termination proof of each application needs allocation charges for begin and each
step.  [Sizes](Sizes.lean) bounds the pending line by any line-length bound that `Room` implies,
since the pending line is a prefix of a line whose `Room` holds, keeps the input buffer within one
read and the output buffer within a bound on the kernel's output, and bounds the line and total of
a state at which a step stops.  The integer application proves its charges from these bounds and
its limits on line length and total size, and the binary64 application takes its charges as
premises, as [the WASI manual](../../docs/wasi.md#resources-host-assumptions-and-total-execution)
states.  The StreamFold theorems cover successful transfers only.  A returned I/O error stops the process with its errno, as `afterRead` and `afterWrite` state, and the application drivers test that case.

## Modules

| Module | Contents |
|---|---|
| [Interface](Interface.lean) | The kernel, the buffered state, the process, and the byte model. |
| [Control](Control.lean), [ranks](Rank.lean), and [host progress](Host.lean) | Buffer safety, the termination rank, and `process_terminates`. |
| [Bytes](Bytes.lean) | Byte words of buffers and the accounting of partial writes. |
| [Model proofs](Model.lean) | `outcome` over appended input, the line split, `foldOutcome`, `LineValues`, and the safety of the model from `LineRooms`. |
| [Buffer](Buffer.lean) | The input loop as a prefix of the model, through acceptance or rejection. |
| [Stream host](StreamHost.lean) and [observed output](Observed.lean) | The host assumptions and the stdout journal of an observed host. |
| [Invariant](Invariant.lean), [future base](FutureBase.lean), and [future](Future.lean) | `StreamFuture`, `StreamDone`, and their preservation by each step. |
| [Correctness](Correct.lean) | `process_exec_correct`, `process_terminates_future`, and `initial_terminates_output`. |
| [Sizes](Sizes.lean) | The pending line's bound from any line-length bound that `Room` implies, the bounds of the buffers after each step, and the line and total of a state at which a step stops. |
| [Map](Map.lean) | Transport of `repeatWhile` along a state view. |
