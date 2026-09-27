# Euclidean Scalar-Loop Artifact Walkthrough

## Summary

This demo maps a singleton `Array UInt64` containing `x` to a singleton containing `gcd(x, 42)`.  It returns an array of every other length unchanged.  The generated source computes the scalar result with an imperative Euclidean remainder loop in a separate `UInt64 → UInt64` function, giving the artifact proof a scalar call boundary and a body-first loop.

The 1,770-byte WASM module has SHA-256 digest `8126a2d03d514dd1335250b05fc9a1f9b89b84b55cc5b4d3e5a019c0ca6599cf`.  Independent `leanexegen verify -s` accepted the exact-artifact theorem and each retained proof-time sample.  The compiler annotations and generated Lean equalities bind every supplied scalar transition to this decoded artifact rather than to the Lean source.

The annotation-free baseline completed Stage 5 in 1,056.072 seconds and produced a 191-line proof after nine edited candidates.  Three runs with the checked scalar post-test annotation completed in 495.497, 520.301, and 510.885 seconds, giving a 510.885-second median and a 24.804-second range.  The median is 51.6 percent below the baseline, while the accepted proofs contain 155, 157, and 171 lines and require three, two, and two edited candidates.

## Program and specification

The [generation request](request.txt) fixes the array behavior, the separate scalar helper, and the imperative Euclidean loop.  The [formal specification](spec.lean) defines the singleton result with `Nat.gcd` and states the artifact property over the public array ABI.  The [generated Lean program](program.lean) implements the loop without importing or referring to that specification.

```lean
def gcdWith42 (value : UInt64) : UInt64 := Id.run do
  let mut x := value
  let mut y : UInt64 := 42
  while y != 0 do
    let remainder := x % y
    x := y
    y := remainder
  return x

def compute (input : Array UInt64) : Array UInt64 :=
  if input.size == 1 then
    #[gcdWith42 input[0]!]
  else
    input
```

The [WASM module](program.wasm) is the executable covered by the proof, and the [WAT rendering](program.wat) exposes its decoded control and local operations.  Function zero initializes the pair `(x, 42)`, executes a body-first remainder loop over staged accumulator locals, and returns the first accumulator.  Function one checks the array length, calls function zero for a singleton, allocates the singleton result, and returns the input unchanged otherwise.

## Artifact proof

The selective [compiler annotations](program.annotations.json) contain the `leanexe.loop.scalar-post-test.v1` region for function zero and the mandatory direct-call region in function one.  The generated [annotation equalities and transition theorems](annotation-matches.lean) prove the exact scalar region, compact transitions, loop entry, and structurally matched singleton wrapper.  The [proof recipe plan](proof-recipes.json) names those declarations together with `ScalarTransition.postTestProgram_spec`, while the [selected strategy notes](proof-strategies.md) and [program feature report](proof-task-features.json) provide the guidance selected from the frozen Program.

The [behavioral proof](proof.lean) proves the formal specification for the Talos module decoded from the exact WASM bytes.  Its scalar invariant states that the current accumulator pair has the same natural-number GCD as `(input, 42)`, and its measure is the second accumulator's natural value.  The generated transition equations remove instruction sequencing, checked remainder behavior, staged local writes, the done flag, and the external argument order from the free-form proof.

The [proof journal](proof-journal.md) records the first retained agent's three edited candidates and identifies the exact exit suffix and compact-state normalization as its remaining artifact presentation work.  The [proof telemetry](proof-telemetry.json) records that run's Codex, outer-acceptance, total-time, and accepted-source identity fields.  The [three-run timing record](proof-timings.json) adds both repeats, the baseline, structural counts, the distribution, and the rejected exit-suffix screen.

The [stage reports](stage-reports.json) retain the accepted specification, source, and artifact-proof task identities and decisions.  They also record the artifact digest and package inputs used by outer acceptance.  Together with the proof journal and telemetry, they permit a later review to separate proof-generation behavior from Lean verification time.

## Execution

The first two samples exercise composite and prime singleton inputs.  The third sample exercises the non-singleton identity branch.  Direct execution of the retained WASM produced these results:

```text
Input: [60]
Output: [6]
Input: [97]
Output: [1]
Input: [12, 18]
Output: [12, 18]
```

## Retained files

Every retained file fixes an experiment input, records the proof context, or preserves an accepted result.  The files use the same generated namespace, artifact digest, and public ABI.  The table identifies each file's role in the walkthrough.

| File | Contents |
|---|---|
| [Generation request](request.txt) | The array behavior and required Euclidean helper loop. |
| [Formal specification](spec.lean) | The mathematical result, runtime precondition, and artifact property. |
| [Lean program](program.lean) | The generated source compiled by LeanExe. |
| [WASM module](program.wasm) | The exact executable artifact covered by the proof. |
| [WAT rendering](program.wat) | The textual instruction representation of the retained artifact. |
| [Behavioral proof](proof.lean) | The accepted direct proof of the generated WASM behavior. |
| [Compiler annotations](program.annotations.json) | The selected scalar post-test loop and mandatory direct-call regions. |
| [Annotation equalities and transitions](annotation-matches.lean) | The generated exact-region, compact-transition, entry, and singleton-wrapper theorems. |
| [Proof recipe plan](proof-recipes.json) | The checked theorem applications offered to the proving agent. |
| [Selected strategy notes](proof-strategies.md) | The feature-selected proof guidance supplied with the recipe. |
| [Program feature report](proof-task-features.json) | The reachable functions, instructions, locals, operations, and selected guidance identities. |
| [Proof journal](proof-journal.md) | The first retained agent's chronological account of proof construction. |
| [Proof telemetry](proof-telemetry.json) | The first retained run's measured Stage 5 intervals and proof identity. |
| [Three-run timing record](proof-timings.json) | The baseline, retained distribution, structural counts, and rejected follow-up. |
| [Stage reports](stage-reports.json) | The accepted task reports and source identities for the complete generation run. |
