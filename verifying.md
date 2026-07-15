# Verifying a Program

This guide covers a new verified program: a Lean function, its compiled WASM artifact, and a machine-checked theorem that the shipped binary computes the function.  The `fold_sum` case serves as the worked example throughout.  Its source, generated model, and proof show the maintained file structure.

The pipeline has three trusted-base components: the Lean kernel, the Talos WASM model, and the Talos decoder.  The compiler is not trusted.  Each verified program is translation validation: the theorem is about the decoded instruction stream, and a byte comparison pins that stream to the artifact the compiler ships.

Complete the proof-workspace setup in [Developing LeanExe](DEVELOPING.md) before adding a case.  The compiler and proof workspaces use Lean 4.31.0, while the proof workspace adds pinned Talos dependencies.  A cold proof build compiles thousands of jobs, and an artifact update also requires the separately built Talos verifier emitter.

## 1. Write the Function

Write an ordinary Lean definition inside the accepted subset ([Language Specification](spec.md), [LeanExe User Manual](manual.md)).  The example lives in [`LeanExe/Examples/ByteArrayPrograms.lean`](LeanExe/Examples/ByteArrayPrograms.lean):

```lean
def foldSum (input : ByteArray) : Nat :=
  input.foldl (fun acc byte => acc + byte.toNat) 0
```

Add ordinary execution tests to the Node suite first.  A function that fails differential testing is not ready to verify.

## 2. Scaffold the Talos Case

A case named `fold_sum` needs four registrations, each one line or one small file:

1. `proofs/talos-gcd/rust/fold_sum/Cargo.toml`: a four-line package stub, and the package name added to the members list in `proofs/talos-gcd/rust/Cargo.toml`.
2. `tools/check-talos-fold-sum.sh`: a wrapper naming the case, module, entry, spec module, and program path.  Copy an existing wrapper and edit the five arguments.
3. A line in `tools/check-talos.sh` invoking the new wrapper.
4. An import of the future spec in `proofs/talos-gcd/lean/Project.lean`, and a stub `Spec.lean` that imports the (not yet generated) `Program.lean`.

Then emit the artifact and its model:

```sh
tools/check-talos-fold-sum.sh --update
```

Update mode compiles the entry, checks in the WASM and WAT under `proofs/talos-gcd/rust/build/fold_sum/`, and generates `lean/Project/FoldSum/Program.lean` through Talos's verifier emitter.  The generated model names each function `funcN` with its instruction stream; read the entry function once to plan the proof.

## 3. Pin the Runtime

Every generated module ends with the shared runtime suite: allocate, reset, retain, and release, in that order, after the user functions.  Add four `rfl` examples to [`lean/Project/Runtime/Checks.lean`](proofs/talos-gcd/lean/Project/Runtime/Checks.lean) identifying the new module's runtime functions with the shared definitions:

```lean
example : Project.FoldSum.func1Def = allocFuncDef := rfl
example : Project.FoldSum.func2Def = resetFuncDef := rfl
example : Project.FoldSum.func3Def = retainFuncDef := rfl
example : Project.FoldSum.func4Def = releaseFuncDef 4 := rfl
```

The release definition takes the function's own index, because its recursion calls itself.  If any `rfl` fails, the compiler's runtime emission changed and the shared library needs attention before the new proof.

## 4. State the Theorem

State the spec as a `Prop` with the `@[spec_of]` linkage to the source declaration, quantified over the program's inputs.  The strongest form relates the WASM result to the Lean function:

```lean
@[spec_of "lean" "LeanExe.Examples.ByteArrayPrograms.foldSum"]
def FoldSumSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr : UInt64)
    (bytes : List UInt8),
    bytes.length < 4294967296 →
    ptr.toNat + bytes.length < 4294967296 →
    BytesAt st ptr bytes →
    TerminatesWith (m := «module») (id := 0) (initial := st) (env := env)
      [.i64 (UInt64.ofNat bytes.length), .i64 ptr]
      (fun st' vs =>
        vs = [.i64 (UInt64.ofNat
          (bytes.foldl (fun acc b => acc + b.toNat) 0))] ∧
        st' = st)
```

The pieces: `BytesAt` states what the host wrote into linear memory at the input pointer; the argument list is the export's ABI (here length then pointer); the postcondition gives the result as the source-level computation plus a frame condition (here the strongest one — the store is untouched, because the program never writes).  Programs that allocate state their frame as counter facts and an everything-below-the-old-heap-top clause; see `push_size` for that template.

## 5. Prove It

The proof enters through `TerminatesWith.of_wp_entry_for`, changes to a `wp` goal over the entry's instruction stream, and steps with `wp_run` plus branch rewrites.  The shared machinery carries the weight:

- **Runtime behavior** comes from [`Runtime/Spec.lean`](proofs/talos-gcd/lean/Project/Runtime/Spec.lean): `retain_spec`, `release_null`, `release_decrements`, and `release_frees_fresh_raw`, each generic over the module and consumed through `wp_call_tw` with the lookup hypothesis discharged by `rfl`.
- **Recursive teardown** comes from `release_frees_tree` in [`Runtime/TreeSpec.lean`](proofs/talos-gcd/lean/Project/Runtime/TreeSpec.lean): exhibit the ownership tree with `TreeAt`, its footprint disjointness, and a page bound, and the theorem returns the exact memory, free list, and counters after the recursive release.
- **Memory reads over write chains** close with the `read_frames` tactic from [`Common.lean`](proofs/talos-gcd/lean/Project/Common.lean); address normal forms bridge with `toNat_sub_le`, `toUInt32_toNat`, and the other `Common` lemmas, all `omega`-friendly.
- **Loops** use `wp_loop_cons` with an invariant and a measure.  An input-consuming loop's invariant relates the accumulator to the source function on the consumed prefix; `fold_sum`'s invariant carries `List.foldl` over `bytes.take k`, with two ordinary list lemmas connecting the prefix to the whole.

Iterate against the goal states: put `trace_state` before an unfinished step, build, read the goal, write the step.  Keep elaboration cheap: prefer `rw` with equation lemmas over `simp` on large terms, evaluate `UInt64` literal `toNat`s with `show ... from rfl` before `omega`, and if a single theorem's elaboration grows past memory, cut it at a `wp` boundary into a helper theorem over an explicit instruction suffix (see `BoxFree/Spec.lean` for the pattern, including composing across the cut with `wp.imp`).

## 6. Gate It

```sh
tools/check-talos-fold-sum.sh   # byte comparison + proof build
tools/check-talos.sh            # all cases + the whole proof library
node test/run_all.js            # differential execution suite
```

A complete case has: no `sorry`, no new axioms, byte-identical artifact files, a green suite, and a `devnotes.md` entry recording what the theorem says and any new proof techniques.
