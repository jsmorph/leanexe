# Counter-Transfer Scalar-Loop Artifact Walkthrough

## Summary

This demo implements the identity function on `Array UInt64`.  A singleton value passes through a separate helper that starts with `(remaining, result) = (x, 0)`, repeatedly changes the pair to `(remaining - 1, result + 1)`, and returns `result` when `remaining` reaches zero.  Every other array length returns unchanged.

The 1,750-byte WASM module has SHA-256 digest `f437ebc16e352391ff05ff79d957eb7ef5652424d6d28c3f279e782980eeb7a5`.  Independent `leanexegen verify -s` accepted each promoted proof over those exact bytes.  The selected representative is the median-time complete-composition run, which completed Stage 5 in 204.537 seconds and produced a 72-line proof.

The reference proof took 577.039 seconds, contained 171 lines, and required four edited candidates.  The arithmetic LTG runs have a 520.815-second median, the checked-summary runs have a 371.243-second median, and the complete-composition runs have a 204.537-second median.  The current median is 44.9 percent below the checked-summary median and 64.6 percent below the reference, while its 72-line median proof remains close to the checked-summary median of 68 lines.

## Program and specification

The [generation request](request.txt) requires the counter-transfer loop and prohibits replacing the helper with a direct return.  The [formal specification](spec.lean) states the public identity result and the runtime memory conditions for the singleton allocation.  The [generated Lean program](program.lean) implements the required scalar loop without importing that specification.

```lean
def scalarIdentity (value : UInt64) : UInt64 := Id.run do
  let mut remaining := value
  let mut result : UInt64 := 0
  while remaining != 0 do
    remaining := remaining - 1
    result := result + 1
  return result

def compute (input : Array UInt64) : Array UInt64 :=
  if input.size == 1 then
    #[scalarIdentity input[0]!]
  else
    input
```

The [WASM module](program.wasm) is the executable covered by the theorem, and the [WAT rendering](program.wat) exposes its decoded control and local operations.  Function zero contains the body-first scalar loop and returns the transferred counter.  Function one checks for a singleton, loads its element, calls function zero, allocates the singleton result, and returns the original input on the other branch.

## Artifact proof

The selective [compiler annotations](program.annotations.json) contain the scalar post-test region, the public length dispatch, and the direct call.  The generated [annotation equalities and transitions](annotation-matches.lean) prove the exact scalar region, compact body and condition evaluations, scalar entry, complete singleton wrapper, and store-preserving scalar identity.  The [proof recipe plan](proof-recipes.json) selects the complete scalar theorem only after the annotation consumer confirms the counter-transfer transition, initial values, exit test, and returned accumulator.

The [behavioral proof](proof.lean) proves the formal specification over the Talos module decoded from the exact WASM bytes.  The deterministic starter applies the generated scalar identity theorem as the callee premise of `FixedArraySingletonWrapper.wrapperProgram_spec`, leaving only the formal equations for invalid and singleton arrays.  The generated theorem uses the shared `CounterTransition.postTestProgram_spec` theorem internally, so the proving agent does not reconstruct the scalar invariant, hidden local frame, transition witnesses, termination measure, or wrapper execution.

The [selected strategy notes](proof-strategies.md) and [program feature report](proof-task-features.json) record the guidance and reachable artifact features supplied to the proof agent.  The [proof journal](proof-journal.md) records the representative run's candidate revisions and use of the supplied assistance.  The [proof telemetry](proof-telemetry.json), [timing record](proof-timings.json), and [stage reports](stage-reports.json) separate measured proof generation from artifact identities and acceptance decisions.

The timing record preserves three rejected experiments against these bytes.  A deterministic semantic cut-point starter that left the scalar proof open took 936.788 seconds, a three-run combined-local measure screen had a 577.172-second median, and a reduced task-context screen took 777.102 and 818.470 seconds.  The checked semantic summary reduced the median to 371.243 seconds, after which composing that summary with the checked public wrapper reduced it to 204.537 seconds.

## Execution

The first sample exercises the scalar loop and singleton allocation.  The second sample exercises the nonsingleton identity branch.  Direct execution of the retained WASM produced these results:

```text
Input: [7]
Output: [7]
Input: [2, 9]
Output: [2, 9]
```

## Retained files

Every retained file fixes an experiment input, records the proof context, or preserves an accepted result.  The files use the same generated namespace, artifact digest, and public ABI.  The table identifies each file's role in the walkthrough.

| File | Contents |
|---|---|
| [Generation request](request.txt) | The public identity behavior and required scalar counter loop. |
| [Formal specification](spec.lean) | The identity result, runtime precondition, and artifact property. |
| [Lean program](program.lean) | The generated source compiled by LeanExe. |
| [WASM module](program.wasm) | The exact executable artifact covered by the proof. |
| [WAT rendering](program.wat) | The textual instruction representation of the retained artifact. |
| [Behavioral proof](proof.lean) | The accepted proof using the checked scalar summary and complete array wrapper. |
| [Compiler annotations](program.annotations.json) | The selected scalar loop, length dispatch, and direct-call regions. |
| [Annotation equalities and transitions](annotation-matches.lean) | The generated exact-region, compact-transition, entry, scalar-summary, and wrapper theorems. |
| [Proof recipe plan](proof-recipes.json) | The checked complete scalar theorem and lower-level fallback declarations. |
| [Selected strategy notes](proof-strategies.md) | The feature-selected proof guidance supplied with the recipe. |
| [Program feature report](proof-task-features.json) | The reachable functions, instructions, locals, operations, and guidance identities. |
| [Proof journal](proof-journal.md) | The representative agent's chronological account of proof construction. |
| [Proof telemetry](proof-telemetry.json) | The representative run's measured Stage 5 intervals and proof identity. |
| [Timing record](proof-timings.json) | The reference, prior LTG distribution, promoted summary distribution, and rejected screens. |
| [Stage reports](stage-reports.json) | The accepted task reports and frozen source identities. |
