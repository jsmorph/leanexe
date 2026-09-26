# Running-sum correctness

The [Lean example](../../LeanExe/Examples/RunningSum.lean) reads signed decimal
integers and writes the sum after each line.  Its source proof covers integers
of arbitrary magnitude, leading zeros, optional signs, CRLF, partial input
lines spanning reads, and a final line without a newline.

## Checked source theorem

`Project.RunningSum.Source.main_correct` in the
[source execution proof](../talos/lean/Project/RunningSum/SourceExecution.lean)
applies to the unchanged `LeanExe.Examples.RunningSum.main`.  For any finite
sequence of valid input bytes, divided into nonempty reads of at most 4,096
bytes, it proves that the program returns zero at EOF and that each output
represents the corresponding integer prefix sum.

`Source.newline_correct` in the
[output-order proof](../talos/lean/Project/RunningSum/SourceOrdering.lean)
shows that processing a newline calls `write` before the loop advances with
the new total.  A write error stops the loop with that error code.  This
statement specifies operation order.  It assumes the host calls return.

`SuccessfulHost` states the assumptions about the opaque Lean I/O primitives:
reads deliver the specified chunks and then EOF, and successful writes append
all requested bytes in order.  `rep` relates the Lean I/O state token to the
remaining input chunks and completed writes.  These assumptions concern the
two I/O operations.  Parsing, arithmetic, buffering, and loop behavior are
proved from the program definitions.

`ValidInput` defines input lines through their byte sequence.  `prefixSums`
computes the mathematical sums using Lean `Int`.  `DecimalOutput` specifies
canonical signed decimal output followed by LF.  The arithmetic proof relates
the program's byte-array arithmetic to those integers, including carry,
borrow, sign selection, and zero normalization.

The proofs use only `propext`, `Classical.choice`, and `Quot.sound`.  Run the
source check from the repository root:

```sh
node tools/running-sum-proof.js check-source
```

The driver runs Lean through `tools/leanrun` and rejects other proof axioms.

## Binary proof status

The frozen `running-sum.wasm` comes from the current compiler and example.
Lean checks its exact-byte decoding, module validation, imports, and `_start`
export.  The universal WASM execution and memory proofs remain open, so the
checked source theorem currently supplies the behavioral result.

The binary preparation and checking commands are:

```sh
node tools/running-sum-proof.js prepare
node tools/running-sum-proof.js check-binary
```

`prepare` regenerates the binary, its embedded bytes, the decoded module, and
the decoder proofs.  `check-binary` compares a fresh compilation with the
frozen bytes and checks decoding, validation, and theorem axioms.  Execution
of the deployed binary also depends on the
[host assumptions](../byte-io/README.md).
