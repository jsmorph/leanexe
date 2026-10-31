# Running maximum: journal of the run

This is the first run of the verified-request skill.  The request asks for a new list whose entry
at each position is the largest value seen up to and including that position, and the skill's
types read the list as an array of unsigned 64-bit words.

## Specification

The specification states entry `i` of the result as the largest of entries `0` through `i` of the
input, `(input.toList.take (i + 1)).foldl max 0`, mapped over `Array.range input.size`.  The fold
starts at 0, which is the least word, so it gives the largest entry of every nonempty prefix, and
the result has the input's length.  The request leaves three cases open, which the specification's
comment records: the numbers are unsigned words compared as unsigned, the empty input gives the
empty result, and the input may have any length.  The verified compiler's call theorem takes a
bound function, so the request needs no limit on the length, unlike the examples that cap their
inputs at eight words.

The samples cover the empty array, one word of 0, 7, and `2^64 − 1`, increasing, decreasing, mixed,
and equal entries, a tie with the largest so far, the largest word first and last, a pair on each
side of `2^63` that separates unsigned from signed comparison, words around `2^32`, and inputs of
20 and 100 entries.  `tools/verified-request-check --spec runningMax` printed the outputs in under
two seconds.

## Review

Two fresh agents reviewed the specification, each given only the paths of the request, the
specification, and the samples, and the output of `--spec`.  The second received that output as a
file, since the 5,000-entry sample made it 41 kilobytes.  Neither found a disagreement.  The first
named lengths with remainders 6 and 7 after division by 8 and lengths of 4,096 or more, and four
samples were added for them.  The second named three further classes: long inputs with large
words, a long input whose later entries can change the output, and arrays of more than a page.
Step 6 of the skill then asked for a sample for each uncovered class and a new review after any
change, while step 7 ended the stage at a review that found no disagreement.  The run followed step 7 after
the second review, as the tree-lookup run of the other skill did, and recorded the classes in the
review.

## Program and proofs

The program folds over the input with a pair state, the largest entry so far and the result so
far, and pushes the new largest entry at each step.  A fold avoids the index conversions of a
`LeanExe.loop` over `xs[i.toNat]!`, and the pair state with a pushed array follows `pair` of the
fold example.  The compilation built in under five seconds, and `--run` passed all 21 samples on
the first attempt.  `#check @compiled.compute.trapFree` showed the premise of room for
`compiled.compute.bound xs` bytes, and `compiled.compute.bound_eq` showed the bound as the smaller
of an unpaid and a paid sum of `Verified.foldCost` charges.

`compute_eq` needs no premise, since the program converts no size to a word.  Its proof rewrites
the array fold as a list fold with `← Array.foldl_toList` and proves `foldl_largest` by induction
on the list, generalizing the state.  `List.range_succ_eq_map`, `List.take_succ_cons`, and
`List.map_map` close the step with `simp`, and `Array.toList_inj` turns the list equation into the
array equation.  No VKB entry then named `Array.foldl_toList` or this induction, and the
`loop-combinators` entry covered `LeanExe.loop`, `LeanExe.build`, and `LeanExe.repeatWhile`.

`compute_callSpec` follows `Examples.Increment.compute_callSpec`, with `fun _ _ _ xs _ => compute_eq
xs` for the equality on represented arguments.  The first build failed to find `Verified.Call.spec`
in a probe file that imported only the compilation, because `Verified.Reflect.Command` does not
import `Verified.Call`.  The increment example imports it through `Examples.ArrayCall`.
`Compiled.lean` now imports `Verified.Call`, the skill says so, and the checker's statement file
imports it itself rather than relying on the run's imports.

The `verified-bound-closed-form` entry then gave the block charges and the loop lemmas but no lemma
for `Verified.foldCost`.  `fold_charge_const` proves by induction on `Nat.fold_succ` that a constant
charge of `c` per step adds `c n`, and `foldCost_const` applies it to a fold.  `compute_bound`
takes the paid side of the bound with `min_le_right` and closes it with `Verified.blockCost_eq`,
`Verified.paidGrowCost_eq`, `Verified.creditCost`, and `omega`, for `80 n + 72` bytes.  Every proof
passed its first build.

## Acceptance and tests

`tools/verified-request-check runningMax` printed the theorem line for `compute_callSpec`, function
2, with the axioms `propext`, `Classical.choice`, and `Quot.sound`, the module of 1,956 bytes,
`samples: 21 passed, 0 failed`, and `native samples: 21 passed, 0 failed`.  `tests/verified/run.sh
--cases runningMax` passed 21 cases with two blocks live after each call, and
`tests/native/verified.sh --module runningMax` translated all three functions, matched the
`clightgen` program with the translation, and passed 21 cases.

## Proposals for the VKB

The proposals below follow the template.  The VKB has since admitted all three: the extension of
`verified-bound-closed-form`, the entry `array-fold-list-induction`, and the change to
`spec-call-theorem`.

An extension of `verified-bound-closed-form`, with `goals` `["Verified.foldCost xs init step (fun _ _ _ => c)", "min unpaid paid of a fold whose state pushes onto an array"]`, `declarations` `["Examples.RunningMax.foldCost_const", "Examples.RunningMax.fold_charge_const"]`, and `examples` `["Examples.RunningMax.compute_bound"]`.  The README would say that a fold's bound is `Verified.foldCost` of each step's charge, that a fold whose state is a pair with a pushed array has the bound `min unpaid paid` with the paid side `blockCost 0 + creditCost 0 + foldCost … (paidGrowCost 1)`, and that `foldCost_const` sums a constant charge.  Moving `foldCost_const` to `Verified/Reflect/FoldLemmas.lean` beside `foldCost_zero` is a separate code change.

A new entry `array-fold-list-induction`, with `goals` `["(xs.foldl f init).2 = …", "Array.foldl f init xs = …"]`, `modules` `["Examples.RunningMax.Proof"]`, `declarations` `["Array.foldl_toList", "Array.toList_inj", "List.range_succ_eq_map", "List.take_succ_cons"]`, `examples` `["Examples.RunningMax.foldl_largest", "Examples.RunningMax.compute_eq"]`, and `sources` naming this journal.  The README would say to rewrite the array fold as a list fold with `← Array.foldl_toList`, to prove the list fold's result for every initial state by induction on the list, and to compare arrays through `Array.toList_inj`.

A change to `spec-call-theorem`: `Verified.Reflect.Command` does not import `Verified.Call`, so a compilation that states `compute_callSpec` imports it, and `Examples.RunningMax.compute_callSpec` is a worked example of an input of any length, with the generated bound as the room.
