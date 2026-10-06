---
name: verified-executable
description: Turn an English request into a LeanExe program, its WebAssembly module, and a theorem that the module's bytes compute a specification that an independent agent reviewed against the request.  Use when the user asks for a verified executable from a description in English, or invokes this skill with a request.
---

# From an English request to a verified executable

The result of a run is a specification `expected`, a program in the LeanExe dialect, a module, and
the theorem `NAME_bytes`:

```lean
∃ bytes, Wasm.Encoding.encode NAME.module = .ok bytes ∧
  ∃ m, Wasm.Encoding.decode bytes = .ok m ∧ Implements m K expected
```

[`tools/demo-check`](../../../tools/demo-check) writes this statement itself and accepts the run only if `NAME_bytes` proves it
with no axioms beyond `propext`, `Classical.choice`, and `Quot.sound`, the specification is the one
the review accepted, and the module returns `expected` on every sample in Wasmtime.  `Implements`
allows a trap, which occurs when memory runs out.  The theorem says nothing about the request
beyond what `expected` says, so the independent review of `expected` against the request is the
only check that the theorem states what the request asks.  The run does not ask the user to approve the specification.

## Names and files

Choose a module name `NAME` in lower camel case, such as `primeFactors`.  `Name` is `NAME`
capitalized, and every file of the run is in `Examples/Name/`.

| File | Contents |
|------|----------|
| `request.txt` | The request, as the user wrote it. |
| `Spec.lean` | `Examples.Name.expected` in ordinary Lean.  Mathlib is allowed. |
| `Samples.lean` | `Examples.Name.samples : List α`, core Lean only. |
| `Program.lean` | The program in `Examples.Name`, with entry `compute`.  It imports only the dialect's modules. |
| `Module.lean` | `leanexe_compile NAME := [f, …, compute]` or `leanexe_compile NAME := compute`. |
| `Verify.lean` | `compute_eq`, the `Implements` theorems, and `NAME_bytes`. |
| `Cases.lean` | The module cases, printed from the samples. |
| `review.md` | The independent review of the specification. |
| `spec.sha256` | Written by `tools/demo-check --freeze`. |
| `journal.md` | The journal of the run. |
| `README.md` | The description of the result. |

`expected` has type `α → β`, where `α` is `UInt64`, `Array UInt64`, or a tuple of these, one
component per parameter of `compute` in order, and `β` is `UInt64` or `Array UInt64`.  Other types
are outside this skill.  If the request needs one, say so and stop.

## Stage 1: the specification

1. Write `request.txt` with the user's words.
2. Write `Spec.lean`: a direct statement of the request, in the request's terms, with no reference
   to the program and no attempt at efficiency.  Use Mathlib definitions where they state the
   request most directly, as `Nat.primeFactorsList` and `Nat.gcd` do in the prime-factor and gcd
   examples.  Decide every case the request leaves open, such as inputs of other lengths, and
   record each decision in a comment.
3. Write `Samples.lean` with inputs that cover the request's cases and edges: 0, 1, `2^64 − 1`, the
   empty array, and each length boundary.  Avoid inputs that make a slow specification
   impractical to evaluate.
4. Run `tools/demo-check --spec NAME`, which prints each sample with the output of `expected`.
5. Have a fresh agent review the specification: start it with the Agent tool and give it only the
   paths of `request.txt`, `Spec.lean`, and `Samples.lean` and the output of step 4.  Give it none
   of your reasoning or plans.  Ask it to read the request, to decide for each case of the input
   whether `expected` gives what the request asks, to name every case the request leaves open and
   whether the specification's comment records the choice, and to check each sample's output by
   hand from the request.  It reports each disagreement with the input that shows it.
6. Summarize the reviewer's report in `review.md`.  For each disagreement, correct the
   specification or samples, or record in `review.md` why the request supports the specification.
   Add a sample for each uncovered input class the reviewer names that a program could get wrong.
   After any change, run steps 4 and 5 again with a new agent.
7. A review that finds no disagreement with the request ends the stage, and its remaining notes go
   into `review.md`.  Run `tools/demo-check --freeze NAME`, which records the hashes of `Spec.lean`
   and `Samples.lean`, and proceed without asking the user.  Never edit either file afterward.  If
   one must change, repeat steps 4 to 7.

## Stage 2: the program

Write the program in the dialect that [the manual](../../../docs/manual.md#the-dialect) describes, in
the sections from "The dialect" through "Summary of constructs": integers are `UInt64`, recursion is tail recursion with a termination proof or a
combinator (`LeanExe.loop`, `LeanExe.build`, `LeanExe.repeatWhile`), and arrays are built at the
top of a function.  The program must not import the specification.  Bound any loop by the input,
as the examples bound arrays to eight words where the request does.  Compile with
`tools/leanrun --timeout 60m lake build Examples.Name.Module`, then run `tools/demo-check --run NAME`,
which emits the module and runs the samples without proofs.  Fix the program until every sample
passes.

## Stage 3: the proofs

`Verify.lean` has three parts.  `compute_eq` proves `compute x = expected x`, with a premise such
as `xs.size < 2 ^ 64` where the program uses `xs.size.toUInt64`.  The `Implements` theorems prove
that each compiled function computes its Lean definition, with the rule of its compiler template.
`NAME_bytes` combines them with `Wasm.Encoding.round_trip` and `Implements.congr`.  Follow the
example whose program has the same shape.

| Program shape | Example |
|---------------|---------|
| Tail recursion on words | [`Examples/PrimeFactors/Verify.lean`](../../../Examples/PrimeFactors/Verify.lean), [`Examples/Gcd/Verify.lean`](../../../Examples/Gcd/Verify.lean) (`Func.tail_implements`, one theorem per run of the loop body) |
| Fold over an array | [`Examples/SumArray/Verify.lean`](../../../Examples/SumArray/Verify.lean) (`Func.foldl_implements`) |
| `LeanExe.loop` with a tuple state, then an array literal | [`Examples/Lookup/Verify.lean`](../../../Examples/Lookup/Verify.lean) (`Stmt.loop_spec`, `Stmt.arrayLiteral_spec`) |
| `LeanExe.build` | [`Examples/Increment/Verify.lean`](../../../Examples/Increment/Verify.lean), [`Examples/RemoveZero/Verify.lean`](../../../Examples/RemoveZero/Verify.lean) (`Stmt.build_spec`) |
| `LeanExe.repeatWhile` over a function that pushes | [`Examples/Below100/Verify.lean`](../../../Examples/Below100/Verify.lean) (`Live.repeatWhileOne`, `Stmt.pushInPlace_spec`) |
| Calls between listed functions | [`Examples/PrimeFactors/Verify.lean`](../../../Examples/PrimeFactors/Verify.lean) (`Stmt.callImplements_spec`), [`Examples/RemoveZero/Verify.lean`](../../../Examples/RemoveZero/Verify.lean) (`Live.callScalar_seq`) |

Print the IR of each function first, as `#eval NAME.f.ir.body`, and write the proof against it.
[The manual's section on proving](../../../docs/manual.md#proving) describes the rules, `eval_body`, and
`eval_state`, and [the LTG entries](../../../ltg/README.md) describe each compiler template's rule.  A `simp` call that evaluates a large body
may need `set_option maxHeartbeats 1000000 in`.  Build with
`tools/leanrun --timeout 60m lake build Examples.Name.Verify`.

## Stage 4: acceptance and records

1. Run `tools/demo-check NAME`.  It must print the theorem line, the module, and
   `samples: N passed, 0 failed`.
2. Write `README.md` in the form of [the prime-factor example's README](../../../Examples/PrimeFactors/README.md): the request, the
   specification and its decisions, the program, a table of the theorems, the axioms, the tests,
   and the commands.
3. Write `Cases.lean`, which prints the samples in the format of the module tests:

   ```lean
   import Examples.Name.Spec
   import Examples.Name.Samples
   import Examples.Host

   namespace Examples.Name

   def cases : IO Unit := do
     for l in Examples.Host.lines "NAME" "compute" expected samples do
       IO.println l

   end Examples.Name
   ```

   Add `import Examples.Name.Program`, `import Examples.Name.Verify`, and `import Examples.Name.Cases`
   to [`Examples.lean`](../../../Examples.lean), and add `import Examples.Name.Cases` and the call
   `Examples.Name.cases` to [`tests/modules/Cases.lean`](../../../tests/modules/Cases.lean).
4. Report the result to the user with the theorem line and the sample count.  Commit only when
   the user's instructions call for it, after [the manual's full check](../../../docs/manual.md#the-full-check).

Keep `journal.md` during the run in natural prose: the decisions in the specification, the
program's form and why, each proof approach and what changed it, the examples and rules that
helped, and any missing general rule.  Record failures as they happen.
