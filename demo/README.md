# Prime-Factor Artifact Walkthrough

## Summary

`leanexegen` turns a prose request into a WASM program accompanied by a Lean proof about that WASM program.  Its `reprove` command can later regenerate only the behavioral proof while holding the specification, source, WASM, and artifact model fixed.  This walkthrough includes both the original generation and a controlled proof-library experiment on the resulting artifact.

In the example below, the request asks for a function that counts prime factors with multiplicity, so the program maps `12` to `3` because `12 = 2 · 2 · 3`.  The result consists of an executable `prime-factors.wasm` and a proof directory that an independent command can check.

The tool uses AI (Codex current) for three separate jobs:

1. Write the formal specification
2. Write the Lean program
3. Prove the compiled artifact

All three AI tasks iterate using real Lean checks, and the program job also iterates against the LeanExe compiler.  A LeanExe rejection returns its diagnostics to the AI for further iteration.

The final proof starts from the emitted WASM bytes, decodes and validates them in Lean, translates the validated module into the [Talos](https://github.com/cajal-technologies/talos) execution model, and proves the formal specification for that module.  The proof task receives the formal specification and the artifact model, while the source program and compiler remain outside its workspace.  `tools/leanexegen verify` checks the resulting theorem without running Codex or recompiling the source.

The Lean excerpts below explain the structure of the resulting proof.  A from-scratch run on 2026-08-03 completed generation in 7 minutes 39 seconds and independent verification in about 60 seconds.  The retained [standard output](stdout.txt) and [standard error](stderr.txt) are the complete streams from that generation process.  The exact generated [formal specification](spec.lean), [Lean program](program.lean), [compiled WASM](program.wasm), [rendered WAT](program.wat), and [behavioral proof](proof.lean) are stored beside this walkthrough.

## 1. Describe the program

The user begins with a short text file.  The request fixes the mathematical behavior and leaves the implementation to the generator.  `leanexegen` currently uses a `UInt64 → UInt64` interface and exports the resulting WASM function as `compute`.

```text
Input is an integer > 0 and output is the number of prime factors (not unique).
Pick convenient input and output types.
```

The generation command names the WASM output.  The tool places the proof directory beside it under the name `prime-factors.proof`.  Temporary workspaces for the specification, source program, and artifact proof remain separate.

```sh
tools/leanexegen \
  -o /tmp/leanexegen-prime-factors-timestamped/prime-factors.wasm \
  /tmp/leanexegen-headless-prime-factors-20260803/request.txt
```

## 2. Generate the formal specification

The [generated formal specification](spec.lean) translates the prose into a mathematical function named `FormalSpec.expected`.  Its definition takes the length of the natural-number prime-factor list and converts the result to `UInt64`.  The definition covers every `UInt64` because the artifact theorem quantifies over the complete machine-word input type.

```lean
import CodeLib
import Mathlib.Data.Nat.Factors

namespace LeanExeGen.Generated.FormalSpec

def expected (input : UInt64) : UInt64 :=
  UInt64.ofNat (Nat.primeFactorsList input.toNat).length

end LeanExeGen.Generated.FormalSpec
```

The orchestrator adds `ArtifactSpec` after accepting `expected`.  This predicate resolves the exported `compute` function, invokes it with one WebAssembly `i64` argument, and requires termination with one `i64` result equal to `expected n`.  Lean then checks the complete specification module and confirms the types of both public definitions.

```lean
namespace LeanExeGen.Generated.FormalSpec

def ArtifactSpec (module_ : Wasm.Module) : Prop :=
  ∃ entry, module_.findExport "compute" = some entry ∧
    ∀ (env : Wasm.HostEnv Unit) (initial : Wasm.Store Unit) (n : UInt64),
      Wasm.TerminatesWith env module_ entry initial [.i64 n]
        (fun _ results => results = [.i64 (expected n)])

end LeanExeGen.Generated.FormalSpec
```

## 3. Generate and check the Lean program

The second AI task receives a copy of the accepted formal specification as context and writes the [generated Lean program](program.lean), whose entry is `Source.compute`.  The implementation uses bounded trial division, retaining the current divisor after a successful division so repeated factors contribute repeatedly.  The source module cannot import the formal specification, which prevents the executable definition from depending on proof-only material.

```lean
namespace LeanExeGen.Generated.Source

def countPrimeFactorsFuel :
    Nat → UInt64 → UInt64 → UInt64 → UInt64
  | 0, _, _, count => count
  | fuel + 1, remaining, divisor, count =>
      if remaining ≤ 1 then
        count
      else if divisor > remaining / divisor then
        count + 1
      else if remaining % divisor = 0 then
        countPrimeFactorsFuel fuel (remaining / divisor) divisor (count + 1)
      else
        countPrimeFactorsFuel fuel remaining (divisor + 1) count

def compute (input : UInt64) : UInt64 :=
  countPrimeFactorsFuel input.toNat input 2 0

end LeanExeGen.Generated.Source
```

The AI session type-checks `Source.compute : UInt64 → UInt64`, runs the LeanExe acceptance report, and performs a scratch compilation after each edit.  A failed command remains in the same session, which reads the diagnostic, edits the candidate, and repeats all three commands.  The outer process accepts the final source only after repeating the same checks in a separate workspace.

## 4. Compile and exercise the program

LeanExe compiles the accepted source into the retained 1,348-byte [WASM module](program.wasm), and the orchestrator freezes those bytes for the rest of the job.  The retained 13,421-byte [WAT rendering](program.wat) lets Talos produce a Lean definition of every WebAssembly function and the complete module.  Proof generation therefore concerns the program that was published, rather than a later compilation of the Lean source.

The program task proposes sample inputs and outputs, which the orchestrator runs against the compiled WASM.  The [captured standard output](stdout.txt) records every stage's start time, the checked sample, and the final Wasmtime command.  The [captured standard error](stderr.txt) records Wasmtime's `--invoke` notices and the four `leanexegen` trust-boundary warnings.  The retained sample checks multiplicity counting on a composite input.

```text
Input: 60
Output: 4
```

The resulting function can also run directly under Wasmtime.  Values through `2^63 - 1` use the same unsigned and signed decimal spelling, while larger `UInt64` values use the corresponding negative `i64` spelling at the command line.  The command prints `4` because `60 = 2 · 2 · 3 · 5`.

```sh
build/tools/wasmtime/current/wasmtime run \
  --invoke compute \
  demo/program.wasm \
  60
```

## 5. Prove the artifact behavior

The proof stage works from two representations of the compiled artifact.  Talos generates `Program.lean` from the WAT, while deterministic Lean modules embed and decode the WASM binary before translating the validated module into the same Talos representation.  The proof task receives these modules and `FormalSpec`, but it receives neither `Source` nor the LeanExe compiler.

AI produces the [generated behavioral proof](proof.lean), whose `artifact_behavior` theorem applies `FormalSpec.ArtifactSpec` to the WAT-derived module.  The proof establishes a trial-division invariant for the generated WebAssembly loop and connects the final counter to `FormalSpec.expected`.  Its public theorem has the following shape, although the retained file also contains the helper lemmas required by the compiled program.

```lean
import LeanExeGen.Generated.FormalSpec
import LeanExeGen.Generated.Program
import Interpreter.Wasm.Wp.Tactic

namespace LeanExeGen.Generated.Behavior

theorem artifact_behavior :
    LeanExeGen.Generated.FormalSpec.ArtifactSpec
      LeanExeGen.Generated.«module» := by
  refine ⟨1, rfl, ?_⟩
  intro env initial n
  apply Wasm.TerminatesWith.of_wp_entry
    (f := LeanExeGen.Generated.func1Def) rfl
  intro initial'
  exact countPrimeFactorsProgram_correct env initial initial' n

end LeanExeGen.Generated.Behavior
```

### Proof-kit refactoring

The [checked proof-kit refactoring](proof-kit.diff) preserves the generated proof above as its baseline.  Its diff consists of one import and two proof-opening changes.  The entry-only tactic shortens the helper theorem's initial conversion, while `wp_entry_single_call` reduces the public wrapper from nine mechanical proof commands to one structured invocation.  The number-theoretic lemmas, loop invariant, decreasing measure, `helper_correct` theorem, formal specification, and artifact theorem remain unchanged.

```lean
theorem artifact_behavior :
    LeanExeGen.Generated.FormalSpec.ArtifactSpec
      LeanExeGen.Generated.«module» := by
  refine ⟨1, rfl, ?_⟩
  intro env initial n
  wp_entry_single_call LeanExeGen.Generated.func1Def
    unfolding LeanExeGen.Generated.func1
    as initial'
    using helper_correct env initial' n
```

The [generic control-flow tactic](../proofs/talos/lean/Project/ProofKit/Control.lean) depends on the wrapper definition, its unfolded body, the initial-store name, and a callee theorem accepted by `Wasm.wp_call_tw`.  Its implementation refers to the Talos control-flow rules and carries no program declaration as a constant.  Lean rejects the invocation unless symbolic execution finds the expected straight-line wrapper, one direct call, and a return continuation discharged by the supplied theorem.

The refactored proof was checked in a source-free copy of the retained proof package under Lean 4.31.0.  The exact `LeanExeGen.GeneratedRc8c2d9f87deb0758.ArtifactResult` target rebuilt the changed behavior module in 11 seconds and the artifact result in 1.6 seconds.  The workspace omitted `Source.lean` and the LeanExe compiler, so this check exercised the same artifact-level proof boundary described by the walkthrough.

### Live proof-kit generation

A second from-scratch run gave Codex the proof-kit catalog and permitted the `Project.ProofKit.Control` import.  The generated proof imported that module, used `wp_entry` for the helper theorem, and used `wp_entry_single_call` for the exported wrapper.  Its changes from the baseline proof exactly match the retained [proof-kit diff](proof-kit.diff): the proof fell from 329 to 321 lines, while the loop invariant and number-theoretic argument remained unchanged.

The [proof-kit run's standard output](stdout-with-proof-kit.txt) and [standard error](stderr-with-proof-kit.txt) retain the complete process streams.  Stage 5 took 4 minutes 13.925 seconds, compared with 3 minutes 58.557 seconds in the baseline run, so this run supplies no evidence that the tactic reduced Codex's proof-generation time.  The eight-line reduction affects a small wrapper around a 300-line loop proof, and normal Codex and Lean runtime variation exceeded that reduction.

The run compiled the same 1,348-byte WASM artifact as the baseline, with SHA-256 digest `8ef01d38a73edaca6c9098876af4212bf037ff1a14ba69e186b96a884c54cdcf`.  `tools/leanexegen verify` then checked the published proof package independently in 36.6 seconds and accepted `LeanExeGen.GeneratedRc8c2d9f87deb0758.Artifact.artifact_correct`.  The result demonstrates proof-library discovery and use, along with a smaller generated proof, but a more substantial reusable theorem or tactic must remove work from the loop proof before an end-to-end timing reduction becomes measurable.

### Controlled proof-only generation

The next experiment added two structural tactics to `Project.ProofKit.Control`.  `wp_block_loop invariant inv decreasing measure` packages the repeated Talos block and loop rule pair, while `wp_entry_to_loop functionDef unfolding functionBody as initial'` performs the entry conversion, unfolds the generated function, executes its straight-line prefix, and exposes the loop-rule goal.  Neither tactic contains prime-factor definitions, generated function constants, or application mathematics.

`leanexegen reprove` received the preceding proof package as its input.  The command accepted a changed proof-library digest but required the Lean, Talos, verifier, artifact support, Node, Wasmtime, and `wasm-tools` identities to remain fixed.  It omitted stages two through four, withheld Source and the old Behavior module from Codex, and generated a replacement Behavior proof against the frozen artifact modules.

```sh
tools/leanexegen reprove \
  -o /tmp/leanexegen-reprove-loop-20260803/prime-factors.wasm \
  /tmp/leanexegen-prime-factors-proofkit-20260803/prime-factors.proof
```

Codex read the revised catalog and used `wp_entry_to_loop` for the trial-division helper.  The tactic replaces the entry conversion, function unfolding, straight-line symbolic execution, and block-rule application, after which the proof states the same invariant and measure in its application of `Wasm.wp_loop_cons`.  The exported wrapper continues to use `wp_entry_single_call` with `helper_correct` as its explicit semantic premise.

```lean
wp_entry_to_loop LeanExeGen.Generated.func0Def
  unfolding LeanExeGen.Generated.func0
  as initial'
apply Wasm.wp_loop_cons
  (Inv := factorInv initial' (FormalSpec.expected n))
  (μ := factorMeasure)
```

The [controlled reproof diff](controlled-reproof.diff) records every change from the preceding 321-line proof.  The result has 316 lines: the loop opening is two lines shorter, three imports become unnecessary through `Project.ProofKit.Control`, and the remaining edits remove unused simplifier arguments or use equivalent library statements.  The formal specification, Source, Program, deterministic artifact modules, and all 1,348 WASM bytes matched the input package byte-for-byte.

Controlled stage five took 390.849 seconds, compared with 253.925 seconds for the preceding proof-kit run.  The experiment therefore establishes that Codex can discover and use a reusable loop abstraction under fixed proof inputs, and that the resulting proof is smaller; it supplies no evidence of faster proof generation.  Independent `leanexegen verify` accepted the new package and the same artifact theorem for SHA-256 `8ef01d38a73edaca6c9098876af4212bf037ff1a14ba69e186b96a884c54cdcf`.

The final theorem connects that behavioral result to the embedded WASM bytes.  Lean's decoder and validator produce a validated module, and the translation theorem identifies its Talos form with the module used by `artifact_behavior`.  The conclusion states the same `FormalSpec.ArtifactSpec` for the module recovered from the binary artifact.

```lean
namespace LeanExeGen.Generated.Artifact

theorem artifact_correct :
    ∃ raw validated,
      decode artifactBytes = .ok raw ∧
      validate raw = .ok validated ∧
      CoreValid raw ∧
      LeanExeGen.Generated.FormalSpec.ArtifactSpec
        validated.toTalos := by
  exact artifact_behavior_for_embedded_bytes

end LeanExeGen.Generated.Artifact
```

## 6. Verify the result independently

The successful generation command publishes two outputs: the executable WASM file and its Lean proof directory.  The proof directory contains the embedded artifact, formal specification, generated execution model, behavioral proof, and final artifact theorem.  A separate verification command checks those Lean modules without consulting the source program or compiler.

```sh
tools/leanexegen verify \
  /tmp/leanexegen-prime-factors-timestamped/prime-factors.proof
```

After this command succeeds, the user has a WASM function and a Lean theorem stating that invoking the artifact returns the specified prime-factor count for every `UInt64` input.  The theorem concerns the WASM bytes in the proof directory and uses the WebAssembly semantics formalized by Talos.  AI's interpretation of the prose and LeanExe's compilation remain recorded generation steps, while the checked result begins at the artifact.
