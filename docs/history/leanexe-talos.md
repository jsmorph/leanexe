# Verifying Generated LeanExe WASM with Talos

This document records the original GCD proof experiment.  The current proof architecture, artifact inventory, and commands live in [Talos Proofs](../../proofs/talos-gcd/README.md), while [Verifying a Program](../verifying.md) defines the maintained procedure.  Historical commands and file descriptions below may differ from the current shared proof library.

This experiment connects [LeanExe](https://github.com/jsmorph/leanexe)-generated WASM to a [Talos](https://github.com/cajal-technologies/talos) proof.  The source program is ordinary Lean code inside the LeanExe supported subset.  LeanExe emits WASM, Talos decodes the generated WAT into a Lean model, and a Lean proof establishes the behavior of that decoded module.

The proved claim covers one generated WASM export.  For all `UInt64` inputs `a` and `b`, the generated `gcd` export terminates and returns `UInt64.ofNat (Nat.gcd a.toNat b.toNat)`.  The proof target is the program Talos decoded from the generated WAT, so the proof follows the emitted control flow and local-variable layout.

## Goal

The experiment ties together the Lean source program, the generated WASM artifact, and the formal proof about that artifact.  A proof about a rewritten WAT model would leave a gap between the compiler output and the verified program.  The experiment keeps the generated artifact in the proof path and checks that the proof input still matches the current compiler output.

Two checks serve separate purposes.  The Talos Lean proof proves the GCD postcondition under Talos’s WASM semantics.  The artifact check regenerates the WASM and WAT from the Lean source, compares them byte-for-byte against the files used by the proof, and then rebuilds the proof project.

## Source Program

The LeanExe source program is a Euclidean GCD algorithm written in Lean.  It uses `UInt64`, mutable variables in `Id.run`, a `while` loop, unsigned remainder, and a scalar return value.  LeanExe compiles this definition to a WASM export named `gcd`.

```lean
namespace LeanExe
namespace Examples.TalosGcd

def gcd (a b : UInt64) : UInt64 := Id.run do
  let mut x := a
  let mut y := b
  while y != 0 do
    let r := x % y
    x := y
    y := r
  return x

end Examples.TalosGcd
end LeanExe
```

The source file is `LeanExe/Examples/TalosGcd.lean`.  The mathematical postcondition uses the `Nat` views of the operands and then casts the bounded GCD result back to `UInt64`.  The loop proof uses the identity `gcd x y = gcd y (x % y)` for `y ≠ 0`, with `y.toNat` as the decreasing measure.

## Generated Artifact

LeanExe compiles the source function with the normal `lean-wasm` executable.  The command names the Lean module, the entry definition, and the output WASM file.  In this experiment the output path is the artifact path consumed by the Talos proof directory.

```sh
.lake/build/bin/lean-wasm compile \
  --module LeanExe.Examples.TalosGcd \
  --entry LeanExe.Examples.TalosGcd.gcd \
  --out proofs/talos-gcd/rust/build/gcd/program.wasm
```

The generated WASM file in this experiment is 1,195 bytes.  The WAT printed from that WASM file is 11,882 bytes.  The module contains the exported `gcd` function and LeanExe runtime exports such as `alloc`, `retain`, and `release`, while the `gcd` export performs only local scalar computation.

Talos uses WAT in this proof.  `wasm-tools print` renders the generated WASM into `proofs/talos-gcd/rust/build/gcd/program.wat`.  Talos’s verifier emitter decodes that WAT into `proofs/talos-gcd/lean/Project/Gcd/Program.lean`, which contains a `Wasm.Module` value and a `func0` body corresponding to the exported `gcd` function.

## Talos Proof

The proof project is in `proofs/talos-gcd/lean`.  Its Lake file pins Talos through the `CodeLib` dependency at revision `bb3277e21c9786e3133d5c1601e34ebdc0bea4df`.  The proof imports `Project.Gcd.Program`, which is the Talos-generated Lean representation of the decoded WAT.

The core specification names the Lean source symbol and states the behavior of function index `0` in the decoded WASM module.  The postcondition inspects the returned WASM value stack and requires a single `i64` result.  This specification is the boundary between the generated artifact and the mathematical statement that the proof establishes.

```lean
@[spec_of "lean" "LeanExe.Examples.TalosGcd.gcd"]
def GcdSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64),
    TerminatesWith env «module» 0 initial [.i64 b, .i64 a]
      (fun _ rs => rs = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))])
```

The argument order in the stack list follows Talos’s WASM calling convention.  Talos reverses the argument list when constructing the callee local frame, so `local 0` receives `a` and `local 1` receives `b`.  The theorem proves this `TerminatesWith` statement for all host environments, all initial stores, and all `UInt64` inputs.

The proof uses Talos’s weakest-precondition rules for straight-line instructions, blocks, and loops.  The generated function has an outer block and an inner loop because the loop exits through a branch from generated WASM control flow.  The proof names the generated local frame, treats WASM locals `4` and `5` as the Euclidean state `(x, y)`, leaves compiler scratch locals unconstrained, and uses `y.toNat` as the loop measure.

The proof is in `proofs/talos-gcd/lean/Project/Gcd/Spec.lean`.  It handles the two loop cases explicitly: when `y = 0`, the function exits and returns `x`, and when `y ≠ 0`, the generated code updates the state to `(y, x % y)` and branches back to the loop.  The arithmetic step uses `Nat.gcd_rec`, `Nat.gcd_comm`, `UInt64.toNat_mod`, and `Nat.mod_lt`.

## Artifact Check

The proof input must remain tied to the source and compiler.  The repository includes `tools/check-talos-gcd.sh`, which regenerates the artifact and compares it against the proof input.  The script uses byte-for-byte file comparisons before it rebuilds the proof project.  It performs these steps in order:

1. Builds `LeanExe.Examples.TalosGcd` and the `lean-wasm` compiler.
2. Compiles `LeanExe.Examples.TalosGcd.gcd` to a fresh temporary WASM file.
3. Prints a fresh temporary WAT file with `wasm-tools print`.
4. Compares the fresh WASM file with `proofs/talos-gcd/rust/build/gcd/program.wasm`.
5. Compares the fresh WAT file with `proofs/talos-gcd/rust/build/gcd/program.wat`.
6. Builds the Talos Lean proof project with `lake build`.

The script accepts `WASM_TOOLS` when the `wasm-tools` binary is outside `PATH`.  It also checks `$HOME/.cargo/bin/wasm-tools`, which matches the installation used for this experiment.  A mismatch in the regenerated WASM or WAT causes `cmp` to fail before the script builds the proof project.

The verification command is short because the script contains the artifact comparison logic.  The command runs from the repository root.  It fails if the regenerated WASM or WAT differs from the proof input.

```sh
bash tools/check-talos-gcd.sh
```

A run of this command rebuilt the Lean source and `lean-wasm`, regenerated the WASM, regenerated the WAT, compared both generated files against the proof inputs, and rebuilt the Talos proof project.  The proof project build completed successfully.  This run establishes that the checked proof corresponds to the current generated artifact for this source program.

## Execution Tests

Wasmtime provides independent execution tests for selected inputs.  The Talos proof carries the universal claim, while these tests check selected executions under the target WASM engine.  They also record the exact WASM artifact executed outside the Talos model.

```sh
build/tools/wasmtime/current/wasmtime \
  --invoke gcd proofs/talos-gcd/rust/build/gcd/program.wasm 48 18

build/tools/wasmtime/current/wasmtime \
  --invoke gcd proofs/talos-gcd/rust/build/gcd/program.wasm 270 192

build/tools/wasmtime/current/wasmtime \
  --invoke gcd proofs/talos-gcd/rust/build/gcd/program.wasm 17 0
```

Wasmtime returned `6`, `6`, and `17`.  These cases cover an ordinary nontrivial GCD, another nontrivial pair, and the zero second operand case.  The universal correctness claim comes from the Talos proof, not from these sample executions.

## Result

The experiment proves a concrete statement: the WASM program generated by LeanExe for `LeanExe.Examples.TalosGcd.gcd`, after decoding through Talos’s WAT pipeline, terminates and returns the mathematical GCD for all `UInt64` inputs.  The proof is over Talos’s model of the decoded WAT, so it follows the emitted control flow and local-variable layout.  The artifact check reconnects that proof input to the LeanExe source and compiler by rebuilding and comparing the WASM and WAT files.

The experiment also gives a reusable pattern for future examples.  The pattern is a small Lean source program, normal LeanExe compilation, Talos proof-input generation from the emitted artifact, a semantic property over the decoded module, and an artifact check that fails when generated bytes change.  For larger examples, the proof burden will include generated-WASM control flow, generated helper functions, heap operations, and input/output behavior.

## Limits

This proof leaves general LeanExe compiler correctness unproved.  It proves one generated export correct after the compiler has produced one artifact.  The artifact check prevents accidental divergence between that artifact and the source/compiler at the time the check runs, but it does not establish a general compiler-correctness theorem.

This proof depends on Talos’s WASM semantics and decoder.  It proves behavior in the Talos model of the decoded WAT.  The Wasmtime execution tests confirm selected cases under the project’s target engine, but they do not prove that Talos’s semantics matches Wasmtime for every program.

The example avoids heap allocation, linear-memory reads and writes, WASI, JSON parsing, and source-level input/output.  This first proof target focuses the proof on the loop invariant, which already exercises Talos’s control-flow proof rules.  Larger LeanExe examples will require specifications and proof support for the runtime allocator, reference-counting operations, WASI imports, byte arrays, strings, arrays, structures, and recursive values.

## References

- [LeanExe](https://github.com/jsmorph/leanexe)
- [Talos](https://github.com/cajal-technologies/talos)
