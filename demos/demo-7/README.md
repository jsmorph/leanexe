# Counter-Transfer Scalar-Loop Artifact Walkthrough

## Summary

This demo implements the identity function on `Array UInt64`.  A singleton value passes through a separate helper that starts with `(remaining, result) = (x, 0)`, repeatedly changes the pair to `(remaining - 1, result + 1)`, and returns `result` when `remaining` reaches zero.  Every other array length returns unchanged.

The 1,750-byte WASM module has SHA-256 digest `f437ebc16e352391ff05ff79d957eb7ef5652424d6d28c3f279e782980eeb7a5`.  Independent `leanexegen verify -s` accepted each retained LTG proof over those exact bytes.  The selected representative is the median-time retained run, which completed Stage 5 in 520.815 seconds and produced a 125-line proof.

The reference proof took 577.039 seconds, contained 171 lines, and required four edited candidates.  The three retained LTG runs have a 520.815-second median, a 411.486-second range, and a median proof size of 135 lines.  The median time reduction is 9.7 percent, while the broad range prevents a stronger timing claim.

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

The selective [compiler annotations](program.annotations.json) contain the scalar post-test region, the public length dispatch, and the direct call.  The generated [annotation equalities and transitions](annotation-matches.lean) prove the exact scalar region, compact body and condition evaluations, scalar entry, and complete singleton wrapper.  The [proof recipe plan](proof-recipes.json) selects those boundaries and reports fixed-width counter help only from the checked operations present in the scalar descriptor.

The [behavioral proof](proof.lean) proves the formal specification over the Talos module decoded from the exact WASM bytes.  Its invariant states that the wrapping sum of the remaining and result counters equals the original input, and its measure reads the remaining counter as a natural number.  `CounterTransition.decrement_add_increment` preserves the invariant, while `CounterTransition.decrement_toNat_lt` proves strict decrease for the nonzero branch.

The [selected strategy notes](proof-strategies.md) and [program feature report](proof-task-features.json) record the guidance and reachable artifact features supplied to the proof agent.  The [proof journal](proof-journal.md) records the representative run's candidate revisions and use of the supplied assistance.  The [proof telemetry](proof-telemetry.json), [timing record](proof-timings.json), and [stage reports](stage-reports.json) separate measured proof generation from artifact identities and acceptance decisions.

The timing record also preserves two later rejected experiments against these bytes.  A deterministic semantic cut-point starter took 936.788 seconds, while a three-run combined-local measure screen had a 577.172-second median.  Both exceed the retained 520.815-second median, so the public proof and active LTG remain unchanged.

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
| [Behavioral proof](proof.lean) | The accepted direct proof of the generated WASM behavior. |
| [Compiler annotations](program.annotations.json) | The selected scalar loop, length dispatch, and direct-call regions. |
| [Annotation equalities and transitions](annotation-matches.lean) | The generated exact-region, compact-transition, entry, and wrapper theorems. |
| [Proof recipe plan](proof-recipes.json) | The checked theorem applications and operation-selected scalar assistance. |
| [Selected strategy notes](proof-strategies.md) | The feature-selected proof guidance supplied with the recipe. |
| [Program feature report](proof-task-features.json) | The reachable functions, instructions, locals, operations, and guidance identities. |
| [Proof journal](proof-journal.md) | The representative agent's chronological account of proof construction. |
| [Proof telemetry](proof-telemetry.json) | The representative run's measured Stage 5 intervals and proof identity. |
| [Timing record](proof-timings.json) | The reference, retained distribution, and rejected composition, cut-point, and coordinate screens. |
| [Stage reports](stage-reports.json) | The accepted task reports and frozen source identities. |
