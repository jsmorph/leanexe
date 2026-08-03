# Prime-Factor Artifact Walkthrough

## Summary

`leanexegen` turns a prose request into a WASM program accompanied by a Lean proof about that WASM program.

In the example below, the request asks for a function that counts prime factors with multiplicity, so the program maps `12` to `3` because `12 = 2 · 2 · 3`.  The result consists of an executable `prime-factors.wasm` and a proof directory that an independent command can check.

The tool uses AI (Codex current) for three separate jobs:

1. Write the formal specification
2. Write the Lean program
3. Prove the compiled artifact

All three AI tasks iterate using real Lean checks, and the program job also iterates against the LeanExe compiler.  A LeanExe rejection returns its diagnostics to the AI for further iteration.

The final proof starts from the emitted WASM bytes, decodes and validates them in Lean, translates the validated module into the [Talos](https://github.com/cajal-technologies/talos) execution model, and proves the formal specification for that module.  The proof task receives the formal specification and the artifact model, while the source program and compiler remain outside its workspace.  `tools/leanexegen verify` checks the resulting theorem without running Codex or recompiling the source.

The Lean excerpts below explain the structure of the resulting proof.  A from-scratch run on 2026-08-03 completed generation in 7 minutes 39 seconds and independent verification in about 60 seconds.  The retained [standard output](stdout.txt) and [standard error](stderr.txt) are the complete streams from that generation process.  The exact generated [formal specification](spec.lean), [Lean program](program.lean), and [behavioral proof](proof.lean) are stored beside this walkthrough.

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

LeanExe compiles the accepted source into `prime-factors.wasm`, and the orchestrator freezes those bytes for the rest of the job.  It also renders the module as WAT so Talos can produce a Lean definition of every WebAssembly function and the complete module.  Proof generation therefore concerns the program that will be published, rather than a later compilation of the Lean source.

The program task proposes sample inputs and outputs, which the orchestrator runs against the compiled WASM.  The [captured standard output](stdout.txt) records every stage's start time, the checked sample, and the final Wasmtime command.  The [captured standard error](stderr.txt) records Wasmtime's `--invoke` notices and the four `leanexegen` trust-boundary warnings.  The retained sample checks multiplicity counting on a composite input.

```text
Input: 60
Output: 4
```

The resulting function can also run directly under Wasmtime.  Values through `2^63 - 1` use the same unsigned and signed decimal spelling, while larger `UInt64` values use the corresponding negative `i64` spelling at the command line.  The command prints `4` because `60 = 2 · 2 · 3 · 5`.

```sh
build/tools/wasmtime/current/wasmtime run \
  --invoke compute \
  /tmp/leanexegen-prime-factors-timestamped/prime-factors.wasm \
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
