---
name: verified-request
description: Turn an English request into a program that the repository's verified compiler compiles, with a call theorem that the module's export returns, without a trap, the value of a specification that an independent agent reviewed against the request.  Use when the user asks for a program from a description in English built with the verified compiler, or invokes this skill with a request.
---

# From an English request to a verified compilation

The result of a run is a specification `expected`, a program in the verified compiler's dialect,
the module `compiled.module` that `verified_compile` writes for it, and the call theorem
`compute_callSpec`.  With `K` the index of the export `compute`, it states:

```lean
Verified.CallSpec compiled.module compiled.tables K expected compiled.compute.bound
```

`Verified.CallSpec` and `Verified.Call` of [the call theorem](../../../Verified/Call.lean) give
the meaning.  Function `K`, called from a store that `Verified.Ready` states ready, with arguments
that represent `x` and move no object, and with room for `top` to rise by `compiled.compute.bound
x` bytes, returns without a trap the representation of `expected x`.  A store is ready when the
allocator invariant holds, the memory cap is at most 65,535 pages, and each table of the program is
a borrowed array at its address, and `Verified.Ready.initial` proves that the store in which the
module starts is ready.  After the call the store is ready again, every array borrowed before the
call stays borrowed, every region of the heap before the call keeps its bytes and lies apart from
the result, and `top` has risen by at most the bound.

[`tools/verified-request-check`](../../../tools/verified-request-check) writes the statement
itself.  It accepts the run only if `compute_callSpec` proves the statement with no axioms beyond
`propext`, `Classical.choice`, and `Quot.sound`, the specification is the one the review accepted,
and the module returns `expected` on every sample in Wasmtime and, where CompCert is installed, in
the module's translation to C.  The verified compiler's generated theorems state that the module
computes the program, so the run proves that the program equals the specification.  The theorem
says nothing about the request beyond what `expected` says, so the independent review of
`expected` against the request is the only check that the theorem states what the request asks.
The run does not ask the user to approve the specification.

## Names, files, and types

Choose a module name `NAME` in lower camel case, such as `treeLookup`, that no line of [the
verified module registry](../../../tests/verified/modules.txt) uses.  `Name` is `NAME`
capitalized, and every file of the run is in `Examples/Name/`, a new directory.

| File | Contents |
|------|----------|
| `request.txt` | Request, as the user wrote it. |
| `Spec.lean` | `Examples.Name.expected` in ordinary Lean.  Mathlib is allowed. |
| `Samples.lean` | `Examples.Name.samples : List α`, core Lean only. |
| `Program.lean` | Program in `Examples.Name` in the verified compiler's dialect, with entry `compute`.  It imports the dialect modules and any library programs it uses. |
| `Proof.lean` | `compute_eq`.  It imports the program, the specification, and lemmas about the dialect. |
| `Compiled.lean` | `verified_compile compiled := [f, …, compute]`, and after stage 3 `compute_callSpec` and a closed form of the bound. |
| `review.md` | Independent review of the specification. |
| `spec.sha256` | Written by `tools/verified-request-check --freeze`. |
| `journal.md` | Journal of the run. |
| `README.md` | Description of the result. |

`expected` has type `α → β`, where `α` is `UInt64`, `Array UInt64`, or a tuple of these, one
component per parameter of `compute` in order, and `β` is `UInt64` or `Array UInt64`.  Other types
are outside this version of the skill.  If the request needs one, say so and stop before stage 1.

## Stage 1: the specification

1. Write `request.txt` with the user's words.
2. Write `Spec.lean`: a direct statement of the request, in the request's terms, with no reference
   to the program and no attempt at efficiency.  Use Mathlib definitions where they state the
   request most directly, as `Nat.primeFactorsList` and `Nat.gcd` do in the specifications of the
   library's prime-factor count and GCD.  Decide every case the request leaves open, such as inputs of other lengths, and
   record each decision in a comment.
3. Write `Samples.lean` with inputs that cover the request's cases and edges: 0, 1, `2^64 − 1`, the
   empty array, and each length boundary.  Avoid inputs that make a slow specification
   impractical to evaluate.
4. Run `tools/verified-request-check --spec NAME`, which prints each sample with the output of
   `expected`.
5. Have a fresh agent review the specification: start it with the Agent tool and give it only the
   paths of `request.txt`, `Spec.lean`, and `Samples.lean` and the output of step 4, in the prompt
   or, when it is long, as the path of a file that holds it.  Give it none of your reasoning or
   plans.  Ask it to read the request, to decide for each case of the input whether `expected`
   gives what the request asks, to name every case the request leaves open and whether the
   specification's comment records the choice, and to check each sample's output by hand from the
   request.  It reasons from the files and the output alone, runs no build, test, or Lean command,
   and edits no file.  It reports each disagreement with the input that shows it, and the input
   classes that no sample covers.
6. Summarize the reviewer's report in `review.md`.  For each disagreement, correct the
   specification or samples, or record in `review.md` why the request supports the specification.
   After any change, run steps 4 and 5 again with a new agent.
7. The first review that finds no disagreement may name input classes that no sample covers.  Add
   a sample for each class that a program could get wrong, run step 4, and have a second fresh agent
   review the specification and samples as step 5 describes.  The classes that the second review
   names go into `review.md` without new samples.
8. A review that finds no disagreement ends the stage when it names no uncovered class or when it
   is the second review of step 7, and its remaining notes go into `review.md`.  Run
   `tools/verified-request-check --freeze NAME`, which records the hashes of `Spec.lean` and
   `Samples.lean`, and proceed without asking the user.  Never edit either file afterward.  If one
   must change, repeat steps 4 to 8.

## Stage 2: the program

Write the program in the dialect that [the verified compiler
manual](../../../docs/verified-manual.md#the-dialect) describes, in the sections from "The
dialect" through "Restrictions".  Integers are `UInt64`, an array is read with `xs[i.toNat]!`,
iteration uses `LeanExe.loop`, `LeanExe.build`, `LeanExe.repeatWhile`, a fold over the whole array,
or tail recursion, which compiles as a loop, and a definition calls only the definitions listed
before it.  Use no recursion other than tail recursion and no byte literal: other recursion adds a
condition on the call depth to `trapFree`, and a byte literal gives `trapFree` another form, and the
call theorem of this version covers neither.  The program must not import the specification.

No Lean file of the run may declare a global or scoped instance, notation, macro, syntax, or
elaborator, or code that runs at import, such as `instance`, `attribute [instance]`, `notation`,
`infixl`, `macro_rules`, or `initialize`.  The check elaborates its statement in a file that
imports the run's modules, where such a declaration could change what the statement means.  The
check and `--run` refuse each one with its file and line, and they accept the same form after
`local`, which keeps it in its file.

`Compiled.lean` starts with the compilation alone, listing the program's definitions and the
library definitions it calls, each callee before its callers:

```lean
import Examples.Name.Program
import Verified.Reflect.Command

namespace Examples.Name

verified_compile compiled := [f, …, compute]

end Examples.Name
```

Build it with `tools/leanrun --timeout 60m lake build Examples.Name.Compiled`.  A rejected form
names its term in the message, and the manual's restrictions table gives the rewrite.  Then run
`tools/verified-request-check --run NAME`, which emits the module and runs the samples in Wasmtime
without proofs, and fix the program until every sample passes.  Before the proofs, read the
premise of the generated theorem with `#check @Examples.Name.compiled.compute.trapFree`: room for
`compiled.compute.bound x` bytes when the function can abort, and `True` when it cannot.

## Stage 3: the proofs

`Proof.lean` holds `compute_eq`, the equality of the program with the specification.  It imports
the program, the specification, and lemmas about the dialect, such as `LeanExe.Dialect.Lemmas`
and the proof modules of the library programs that the program calls, and no module of
`Verified`.  When the program converts an array's size to a word, as `xs.size.toUInt64` does, the
equality has the premise `xs.size < 2 ^ 64`, which every array in memory meets, and the call
theorem takes it from the argument's representation, as `Examples.Increment.compute_callSpec` does.
Otherwise the equality has no premise, as in the running-maximum example, and passes to the call
theorem as `fun _ _ _ xs _ => compute_eq xs`:

```lean
theorem compute_eq (xs : Array UInt64) (h : xs.size < 2 ^ 64) : compute xs = expected xs
theorem compute_eq (xs : Array UInt64) : compute xs = expected xs
theorem compute_eq (a b : UInt64) : compute a b = expected (a, b)
```

`Compiled.lean` then imports `Examples.Name.Proof` in place of the program, and `Verified.Call`,
which `Verified.Reflect.Command` does not import, and adds `compute_callSpec` and `compute_bound`
after `verified_compile`.  `K` is 2 plus the position of `compute` in the list of
`verified_compile`, counted from 0, since functions 0 and 1 are the runtime's `alloc` and
`release`, and the check proves in the kernel that the export `compute` is function `K`.

| Declaration | Content |
|-------------|---------|
| `compute_callSpec` | Statement of the first section, proved as `Examples.Increment.compute_callSpec` and `Library.Numerics.Arithmetic.Gcd.gcd_callSpec` prove theirs.  `Verified.ImplementsTables.call (.ofA compiled.compute.trapFree) compiled.tables nofun` gives `Verified.Call`, and `Verified.Call.spec` turns it into `CallSpec` for `expected`, from `fun _ _ _ h => h` for the premise, or `fun _ _ _ _ => trivial` when `trapFree`'s premise is `True`, from `fun _ _ _ _ _ h => h` for the conclusion, and from `compute_eq` on represented arguments. |
| `compute_bound` | Closed form of `compiled.compute.bound x`, from `compiled.compute.bound_eq`, which the README states so that a reader knows how much room a call needs.  A function that cannot abort needs none. |

Follow the worked example whose program has the same shape.  The call theorem of every shape
follows `compute_callSpec` and `gcd_callSpec`, which differ only in the premise and in how the
argument's representation gives the premise of `compute_eq`.

| Program shape | `compute_eq` | Bound |
|---------------|--------------|-------|
| Tail recursion on words, word result | [GCD proof](../../../Library/Numerics/Arithmetic/Gcd/Proof.lean) (an equation per branch, recursion on the measure), [prime-factor proof](../../../Library/Numerics/Arithmetic/PrimeFactors/Proof.lean) (strong induction on the measure) | None: [GCD compilation](../../../Library/Numerics/Arithmetic/Gcd/Compiled.lean) |
| `LeanExe.build` of at most eight elements | [Increment proof](../../../Examples/Increment/Proof.lean) (`Array.ext`, `LeanExe.Dialect.build_size`, `LeanExe.Dialect.build_get`) | [Increment compilation](../../../Examples/Increment/Compiled.lean) (`Verified.blockCost_eq`) |
| Library call, then a build | [Zero-removal proof](../../../Examples/RemoveZero/Proof.lean) (`Library.Arrays.Search.firstZero_cases`) | [Zero-removal compilation](../../../Examples/RemoveZero/Compiled.lean) (a bound on the count before `generalize`) |
| `LeanExe.repeatWhile` over a listed function that pushes | [Bounded-build proof](../../../Examples/Below100/Proof.lean) (induction on the fuel, `keep_go`) | [Bounded-build compilation](../../../Examples/Below100/Compiled.lean) (`Verified.loopCost_le`, `Verified.sumBelow_const`) |
| `LeanExe.loop` over a literal count with a tuple state, then an array literal | [Lookup proof](../../../Examples/Lookup/Proof.lean), [tree-lookup proof](../../../Examples/TreeLookup/Proof.lean) (`simp only [LeanExe.loop]`, `by_cases` on each pass) | [Lookup compilation](../../../Examples/Lookup/Compiled.lean), [tree-lookup compilation](../../../Examples/TreeLookup/Compiled.lean) (`rw [compiled.compute.bound_eq]; decide`) |
| Fold over an array of any length whose state pushes onto the result | [Running-maximum proof](../../../Examples/RunningMax/Proof.lean) (`Array.foldl_toList`, induction on the list) | [Running-maximum compilation](../../../Examples/RunningMax/Compiled.lean) (`foldCost_const`, `min_le_right`) |

Before each proof, search [the verification knowledge base](../../../VKB/README.md) for the
declarations and goal shapes at hand.  Search the `entry.json` files under `VKB/entries/` for the
constants of the goal, such as `LeanExe.repeatWhile` or `Verified.loopCost`, and read the README of
every entry that names them.  The entries `spec-call-theorem`, `verified-bound-closed-form`,
`loop-combinators`, `array-fold-list-induction`, and `reflector-forms` cover the shapes of the
table.  [The manual's section on
proving](../../../docs/verified-manual.md#proving) describes the generated theorems and the bounds.
Rewrite a bound with `compiled.compute.bound_eq` and read the goal before choosing lemmas, and
never evaluate a bound with `#eval`, which runs the interpreter of the reflected program and can
take minutes.  A `simp` call that unfolds a large term may need `set_option maxHeartbeats 1000000
in`.  Build with `tools/leanrun --timeout 60m lake build Examples.Name.Proof` and then
`Examples.Name.Compiled`.  End the stage with proposals for new VKB entries or changes to
existing ones, in the form of [the template](../../../VKB/TEMPLATE.md), for each lesson of the
proofs that applies beyond this program: a missing lemma, a tactic that misled, or a goal shape
that no entry names.  Put them in `journal.md` and in the report to the user.

## Stage 4: acceptance and records

1. Run `tools/verified-request-check NAME`.  It must print the theorem line, the module,
   `samples: N passed, 0 failed`, and either `native samples: N passed, 0 failed` or the line that
   says CompCert's tools were not found.
2. Write `README.md` with these sections: "Request, specification, review, and program" (the
   request, the specification and its decisions, the review, and the program), a section whose
   heading states the main theorem, such as "The module searches the tree" (a table of
   `compute_eq`, `compute_bound`, and `compute_callSpec`, and the axioms), "Building, running, and
   testing" (the commands, their output, and the tests), "Related examples", and "References".
   [The running-maximum README](../../../Examples/RunningMax/README.md) gives the form and the
   commands.
3. Add the module to the verified tests.  Add the line
   `Examples.Name.Compiled:Examples.Name.compiled.module:NAME` to [the verified module
   registry](../../../tests/verified/modules.txt) and `import
   Examples.Name.Compiled` to [`Examples/Verified.lean`](../../../Examples/Verified.lean).  Add
   `import Examples.Name.Spec` and `import Examples.Name.Samples` to [the verified
   cases](../../../Verified/Examples/Cases.lean), and at the end of `portCases` a loop that prints
   each sample in the verified driver's format, as the running-maximum loop does:

   ```lean
     for xs in _root_.Examples.Name.samples do
       IO.println s!"NAME|compute|array-u64|{arrayArg xs}|\
         {arrayOut (_root_.Examples.Name.expected xs)}|2"
   ```

   The sixth field is the number of blocks that stay allocated after the call: one for each array
   argument, which the host allocates, and one for an array result.  A program from two words to a
   word has the line `s!"NAME|compute|i64|i64:{a} i64:{b}|{_root_.Examples.Name.expected (a,
   b)}|0"`.  Run `tests/verified/run.sh --cases NAME`, and `tests/native/verified.sh --module NAME`
   where CompCert is installed.  The registry entry gives the module its native coverage: the
   native driver translates every module of the registry to C, compiles it with CompCert, and runs
   its cases.
4. Run the gate of a new example: the acceptance check of step 1, `tests/verified/run.sh --cases
   NAME`, `tests/native/verified.sh --module NAME`, a build of every module that the run adds or
   changes and of those that import them, and the VKB check.  The build is `tools/leanrun
   --timeout 3h lake build Examples.Name.Compiled Examples.Verified Verified
   Verified.Examples.Cases verified-cases native-verified native-module-cases`, and the VKB check is
   `tools/leanrun --timeout 10m lake env lean --run VKB/Check.lean VKB/entries`.  [The verified
   compiler manual's full check](../../../docs/verified-manual.md#the-full-check) remains the gate
   for a change to the verified compiler or the runtime.
5. Report the result to the user with the theorem line, the sample counts, the gate's results, and
   the VKB proposals.  Commit only when the user's instructions call for it, after the gate.

Keep `journal.md` during the run in natural prose: the decisions in the specification, the
program's form and why, each proof approach and what changed it, the VKB entries and worked
examples that helped or failed, and any missing general rule.  Record failures as they happen.
[The running-maximum journal](../../../Examples/RunningMax/journal.md) gives the form.
