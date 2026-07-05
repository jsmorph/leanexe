# Verifying Generated LeanExe List Lookup WASM with Talos

This experiment connects [LeanExe](https://github.com/jsmorph/leanexe)-generated WASM to a [Talos](https://github.com/cajal-technologies/talos) proof for a small recursive-data example.  The source program is ordinary Lean code inside the LeanExe supported subset.  LeanExe emits WASM, Talos decodes the generated WAT into a Lean model, and a Lean proof establishes the behavior of that decoded module.

The proved claim covers one generated WASM export.  For every `UInt64` key, the generated `lookupDemo` export terminates and returns the first matching value from a fixed association list, or `0` when the key is absent.  The proof target is the program Talos decoded from the generated WAT, so the proof follows the emitted allocation, memory layout, recursive calls, and local-variable layout.  The theorem therefore covers both the generated constructor path and the recursive consumer path.

## Goal

The experiment ties together the Lean source program, the generated WASM artifact, and the formal proof about that artifact.  The proof input comes from the WASM file emitted by LeanExe and the WAT printed from that file.  The check script regenerates those files from source, compares them byte-for-byte against the proof inputs, and then rebuilds the Talos proof project.

This example extends the GCD experiment from scalar control flow into heap-allocated recursive data.  The source program builds a fixed `List (UInt64 × UInt64)` and performs ordinary recursive lookup over that list.  The proof therefore has to account for generated allocation and linear-memory reads in addition to arithmetic and loop control.

## Source Program

The LeanExe source program is an association-list lookup written in Lean.  The `lookup` definition pattern matches on a `List` whose elements are product values, destructures the head pair as `(k, v)`, compares the stored key with the query key, and recurses over the tail on a miss.  The exported `lookupDemo` function searches a fixed source-level sample list.  The recursive branch preserves source-list order, so duplicate keys return the value from the first matching cell.

```lean
namespace LeanExe
namespace Examples.TalosAssocList

def lookup : List (UInt64 × UInt64) → UInt64 → UInt64
  | [], _ => 0
  | (k, v) :: rest, key =>
      if k == key then
        v
      else
        lookup rest key

def sample : List (UInt64 × UInt64) :=
  [(7, 70), (2, 20), (9, 90), (2, 22)]

def lookupDemo (key : UInt64) : UInt64 :=
  lookup sample key

end Examples.TalosAssocList
end LeanExe
```

The source file is `LeanExe/Examples/TalosAssocList.lean`.  The sample list deliberately contains the key `2` twice, so the expected result for key `2` is `20`, not `22`.  The proof statement captures first-match association-list behavior rather than set-like membership.

The source stresses one compiler feature beyond scalar arithmetic and loops.  A list constructor arm contains a product element, and the source pattern destructures that product into `k` and `v` in the same arm.  The generated lookup still reads one list payload from memory, while the source binders expose the key and value separately.

## Generated Artifact

LeanExe compiles the source function with the normal `lean-wasm` executable.  The command names the Lean module, the entry definition, and the output WASM file.  In this experiment the output path is the artifact path consumed by the Talos proof directory.

```sh
.lake/build/bin/lean-wasm compile \
  --module LeanExe.Examples.TalosAssocList \
  --entry LeanExe.Examples.TalosAssocList.lookupDemo \
  --out proofs/talos-gcd/rust/build/assoc_list/program.wasm
```

The generated WASM file in this experiment is 3,498 bytes.  The WAT printed from that WASM file is 34,541 bytes.  The module contains the exported `lookupDemo` function and LeanExe runtime exports such as `alloc`, `retain`, and `release`.

Talos uses WAT in this proof.  `wasm-tools print` renders the generated WASM into `proofs/talos-gcd/rust/build/assoc_list/program.wat`.  Talos’s verifier emitter decodes that WAT into `proofs/talos-gcd/lean/Project/AssocList/Program.lean`, which contains a `Wasm.Module` value and generated function bodies for list construction, recursive lookup, and the exported wrapper.  The proof imports that generated module as the semantic object under verification.

## Generated Layout

The decoded module separates the source program into generated WASM functions.  Function `0` performs recursive lookup over a list pointer and a key.  Function `1` constructs the fixed sample list in linear memory.  Function `2` is the exported wrapper: it calls function `1`, passes the returned root pointer and the input key to function `0`, and returns the lookup result.

The proof records the concrete memory layout produced by function `1`.  Each list cell stores a tag at offset `0`, a key at offset `8`, a value at offset `16`, and a tail pointer at offset `24`.  In the generated artifact used here, the root cell is at address `4464`, and the nil cell is at address `4144`.  Those addresses appear in the proof because the artifact check fixes the generated bytes used by Talos.

```lean
private def SampleListStore (st : Store Unit) : Prop :=
  read64At st 4464 = 1 ∧
  read64At st 4472 = 7 ∧
  read64At st 4480 = 70 ∧
  read64At st 4488 = 4384 ∧
  read64At st 4384 = 1 ∧
  read64At st 4392 = 2 ∧
  read64At st 4400 = 20 ∧
  read64At st 4408 = 4304 ∧
  read64At st 4304 = 1 ∧
  read64At st 4312 = 9 ∧
  read64At st 4320 = 90 ∧
  read64At st 4328 = 4224 ∧
  read64At st 4224 = 1 ∧
  read64At st 4232 = 2 ∧
  read64At st 4240 = 22 ∧
  read64At st 4248 = 4144 ∧
  read64At st 4144 = 0
```

This predicate belongs to the proof of the generated artifact.  It gives the proof a compact description of the generated heap shape.  It exposes the memory facts the symbolic lookup proof needs: the tag, key, value, and tail pointer for each generated cell.  A separate Boolean checker evaluates the generated constructor function through Talos `run 5000` and proves that the resulting store satisfies this predicate.

## Talos Proof

The proof project is in `proofs/talos-gcd/lean`.  Its Lake file pins Talos through the `CodeLib` dependency at revision `bb3277e21c9786e3133d5c1601e34ebdc0bea4df`.  The proof imports `Project.AssocList.Program`, which is the Talos-generated Lean representation of the decoded WAT.  The proof file `Project/AssocList/Spec.lean` states and proves the behavior of the decoded module.

The core specification names the Lean source symbol and states the behavior of function index `2` in the decoded WASM module.  The postcondition inspects the returned WASM value stack and requires a single `i64` result.  The theorem quantifies over every `UInt64` key.

```lean
@[spec_of "lean" "LeanExe.Examples.TalosAssocList.lookupDemo"]
def LookupDemoSpec : Prop :=
  ∀ key : UInt64,
    TerminatesWith (m := «module») (id := 2)
      (initial := «module».initialStore (α := Unit))
      (env := ({} : HostEnv Unit)) [.i64 key]
      (fun _ vs => vs = [.i64 (lookupDemoExpected key)])
```

The expected value mirrors first-match lookup over the source list.  Key `7` returns `70`, key `2` returns `20`, key `9` returns `90`, and every other key returns `0`.  The theorem proves this statement for all `UInt64` keys, rather than checking a finite set of representative inputs.  The duplicate key case forces the proof to use the first cons cell with key `2` and ignore the later one after a hit.

The proof has two main parts.  First, `func1_constructs_sample` runs the generated constructor function under Talos and proves that it returns root pointer `4464`, establishes `SampleListStore`, and leaves enough memory for the later loads.  Second, `func0_sample_terminates` and its suffix lemmas prove recursive lookup symbolically over the key.  This split keeps the generated construction proof concrete while making the exported theorem universal over the program input.  The constructor lemma is a generated-execution lemma; an allocator proof would replace that address-specific summary with a source-level heap abstraction.

The suffix lemmas follow the generated `func0` body one cell at a time.  The nil-cell theorem proves that tag `0` returns `0`.  Each cons-cell theorem reads the tag, reads the stored key, splits on equality with the query key, reads the value on a hit, and calls the theorem for the tail pointer on a miss.

## Artifact Check

The proof input must remain tied to the source and compiler.  The repository includes `tools/check-talos-assoc-list.sh`, which regenerates the artifact and compares it against the proof input.  The script uses byte-for-byte file comparisons before it rebuilds the proof project.

The script performs these steps in order:

1. Builds `LeanExe.Examples.TalosAssocList` and the `lean-wasm` compiler.
2. Compiles `LeanExe.Examples.TalosAssocList.lookupDemo` to a fresh temporary WASM file.
3. Prints a fresh temporary WAT file with `wasm-tools print`.
4. Compares the fresh WASM file with `proofs/talos-gcd/rust/build/assoc_list/program.wasm`.
5. Compares the fresh WAT file with `proofs/talos-gcd/rust/build/assoc_list/program.wat`.
6. Builds the Talos Lean proof project with `lake build Project.AssocList.Spec`.

The script accepts `WASM_TOOLS` when the `wasm-tools` binary is outside `PATH`.  It also checks `$HOME/.cargo/bin/wasm-tools`, which matches the installation used for this experiment.  A mismatch in the regenerated WASM or WAT causes `cmp` to fail before the script builds the proof project.

The verification command runs from the repository root.  It fails if the regenerated WASM or WAT differs from the proof input.  It also fails if the Talos proof project no longer proves the all-key theorem.  This command is the integrity check for the article’s proof claim.

```sh
bash tools/check-talos-assoc-list.sh
```

A run of this command rebuilt the Lean source and `lean-wasm`, regenerated the WASM, regenerated the WAT, compared both generated files against the proof inputs, and rebuilt `Project.AssocList.Spec`.  The proof project build completed successfully.  This run establishes that the checked proof corresponds to the current generated artifact for this source program.

## Execution Tests

Wasmtime provides independent execution tests for selected inputs.  The Talos proof carries the universal claim, while these tests check selected executions under the target WASM engine.  They also record the exact WASM artifact executed outside the Talos model.

```sh
build/tools/wasmtime/current/wasmtime \
  --invoke lookupDemo proofs/talos-gcd/rust/build/assoc_list/program.wasm 7

build/tools/wasmtime/current/wasmtime \
  --invoke lookupDemo proofs/talos-gcd/rust/build/assoc_list/program.wasm 2

build/tools/wasmtime/current/wasmtime \
  --invoke lookupDemo proofs/talos-gcd/rust/build/assoc_list/program.wasm 9

build/tools/wasmtime/current/wasmtime \
  --invoke lookupDemo proofs/talos-gcd/rust/build/assoc_list/program.wasm 5
```

Wasmtime returned `70`, `20`, `90`, and `0`.  These cases cover a hit at the head, a hit where an earlier duplicate must win, a later hit, and a miss.  The Talos proof supplies the universal correctness claim.

## Result

The experiment proves a concrete statement: the WASM program generated by LeanExe for `LeanExe.Examples.TalosAssocList.lookupDemo`, after decoding through Talos’s WAT pipeline, terminates and returns the first-match association-list result for every `UInt64` key.  The proof is over Talos’s model of the decoded WAT, so it follows generated allocation, generated linear-memory reads, generated Boolean-normalization blocks, recursive calls, and the exported wrapper.  The artifact check reconnects that proof input to the LeanExe source and compiler by rebuilding and comparing the WASM and WAT files.

The experiment also gives a proof pattern for internal recursive data.  The generated data constructor can be checked once through Talos evaluation and summarized as a memory predicate, while the recursive consumer can be proved symbolically over its input.  For larger examples, the same division can keep constructor proof obligations concrete while preserving universal statements about the program input.

## Limits

This proof leaves general LeanExe compiler correctness unproved.  It proves one generated export correct after the compiler has produced one artifact.  The artifact check prevents accidental divergence between that artifact and the source/compiler at the time the check runs, but it does not establish a general compiler-correctness theorem.

This proof depends on Talos’s WASM semantics and decoder.  It proves behavior in the Talos model of the decoded WAT.  The Wasmtime execution tests confirm selected cases under the project’s target engine, but they do not prove that Talos’s semantics matches Wasmtime for every program.

The proof uses a concrete memory predicate for the generated sample list.  That fits this fixed-data example because the list is constructed inside the generated module and has a stable artifact-specific layout.  Future examples with input-dependent allocation will need source-level heap abstractions, allocator specifications, or proof rules that summarize generated allocation without naming every address.

## References

- [LeanExe](https://github.com/jsmorph/leanexe)
- [Talos](https://github.com/cajal-technologies/talos)
