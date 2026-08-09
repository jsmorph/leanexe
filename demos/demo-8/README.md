# Three-Accumulator Counter-Transfer Artifact Walkthrough

## Summary

This demo implements the identity function on `Array UInt64`.  A singleton passes through a scalar helper with remaining, result, and audit accumulators; each nonzero iteration applies `(remaining - 1, result + 1, audit + 2)`.  Every other array length returns unchanged.

The 1,793-byte WASM module has SHA-256 digest `932262dad153458571234372e49c4142d7a7ea82cff4d09e2f2fd5eb276e4151`.  Its scalar function has 23 locals, three accumulator coordinates, and result slot two, providing a distinct layout from Demo 7.  Independent `leanexegen verify -s` accepted the generated artifact proof.

The first out-of-sample run completed Stage 5 in 313.253 seconds and produced a 70-line proof after one edited candidate.  The proof agent used the generated complete scalar theorem directly and did not reconstruct the loop invariant or audit transition.  Demo 7's three-run distribution remains the timing basis for promotion, while this run establishes structural generality under a new request, namespace, source, and artifact.

## Program and specification

The [generation request](request.txt) requires the audit accumulator and prohibits replacing the scalar helper with a direct return.  The [formal specification](spec.lean) states the public identity result and runtime memory conditions without encoding that implementation requirement.  The [generated Lean program](program.lean) implements the separate three-accumulator helper and calls it in the singleton branch.

```lean
def scalarIdentity (value : UInt64) : UInt64 := Id.run do
  let mut remaining := value
  let mut audit := value
  let mut result : UInt64 := 0
  while remaining != 0 do
    remaining := remaining - 1
    result := result + 1
    audit := audit + 2
  return result
```

The [WASM module](program.wasm) is the executable covered by the theorem, and the [WAT rendering](program.wat) exposes its decoded instructions.  Function zero contains the body-first scalar loop, while function one implements the singleton-array boundary and calls function zero.  The nonsingleton branch returns the original array pointer.

## Artifact proof

The [compiler annotations](program.annotations.json) report a scalar post-test loop with accumulator coordinates `[4, 5, 6]`, result slot two, destination 18, and scratch start 19.  The generated [annotation equalities and transitions](annotation-matches.lean) prove the exact scalar region, compact transition equations, loop entry, complete scalar identity, and singleton wrapper.  The annotation consumer discovers remaining at coordinate five and result at coordinate six by checking their initial values and both loop transitions.

The [proof recipe plan](proof-recipes.json) names the complete scalar identity theorem before the lower-level loop declarations.  The [behavioral proof](proof.lean) supplies that theorem to `FixedArraySingletonWrapper.wrapperProgram_spec` and proves the two formal identity equations.  The audit coordinate remains existential inside the generated state view, where the checked nonzero transition records its independent increment by two.

The [selected strategy notes](proof-strategies.md) and [program feature report](proof-task-features.json) record the optional guidance and reachable artifact facts supplied to the agent.  The [proof journal](proof-journal.md) records the first-edit use of the wrapper and scalar summary.  The [proof telemetry](proof-telemetry.json), [timing record](proof-timings.json), and [stage reports](stage-reports.json) preserve monotonic proof time, source identity, and acceptance results.

## Execution

The singleton sample exercises all three scalar accumulators and the result allocation.  The second sample exercises the nonsingleton identity branch.  Direct execution of the proved artifact produced these values:

```text
Input: [7]
Output: [7]
Input: [1, 2]
Output: [1, 2]
```

## Retained files

Every retained file fixes a generation input, artifact, proof context, or accepted result.  The files share one generated namespace and artifact digest.  The table identifies each file's role.

| File | Contents |
|---|---|
| [Generation request](request.txt) | The public behavior and required three-accumulator helper. |
| [Formal specification](spec.lean) | The identity result, runtime precondition, and artifact property. |
| [Lean program](program.lean) | The generated source compiled by LeanExe. |
| [WASM module](program.wasm) | The exact executable artifact covered by the proof. |
| [WAT rendering](program.wat) | The textual instruction representation of the artifact. |
| [Behavioral proof](proof.lean) | The accepted proof using the checked scalar summary and array wrapper. |
| [Compiler annotations](program.annotations.json) | The scalar loop, length dispatch, and direct-call regions. |
| [Annotation equalities and transitions](annotation-matches.lean) | The exact-region, transition, entry, scalar-summary, and wrapper theorems. |
| [Proof recipe plan](proof-recipes.json) | The complete scalar theorem and lower-level fallback declarations. |
| [Selected strategy notes](proof-strategies.md) | The feature-selected proof guidance supplied to the agent. |
| [Program feature report](proof-task-features.json) | The reachable functions, instructions, locals, operations, and guidance identities. |
| [Proof journal](proof-journal.md) | The agent's chronological account of proof construction. |
| [Proof telemetry](proof-telemetry.json) | The measured Stage 5 intervals and accepted proof identity. |
| [Timing record](proof-timings.json) | The out-of-sample proof interval and structural counts. |
| [Stage reports](stage-reports.json) | The accepted task reports and frozen source identities. |
