# Unbiased random choice

## Request, specification, review, and program

[The request](request.txt) asks for an unbiased random choice by rejection sampling, with a theorem
that every output value has the same number of accepted words.  The plan fixes the interface:
`choose N K` takes N and K in decimal, with 1 ≤ N < 2^64 and 1 ≤ K < 2^64, and writes K lines, each
the decimal of an integer uniform on [1, N].  A refused argument writes nothing and ends with status
2, and the errno of a failed call is the status.  The plan also fixes the method: the command draws
64-bit little-endian words with `random_get`, at most 512 a call, accepts a word w when
w ≥ 2^64 mod N, which `(0 - N) % N` computes in word arithmetic, and outputs (w mod N) + 1.

The pure core has three functions, whose specifications [the specification](Spec.lean) states,
written and reviewed by the method of [the verified-request
skill](../../.claude/skills/verified-request/SKILL.md).  `parseSpec` reads argument `i` from the
buffer that WASI's `args_get` fills, in which each argument follows the program name and ends with
a zero byte, and returns 0, which neither N nor K may equal, for a refusal.  `pickSpec (n, w)`
accepts w when n ≥ 1 and w ≥ 2^64 mod n and then gives (w mod n) + 1, and gives 0 for a rejected
word.  `renderSpec` writes one line for each element of an array, in Lean's decimal form of a
natural number, each followed by the byte 10.  The specification's comment records each choice
that the request leaves open: argument 0 is the program name, arguments after K are ignored,
leading zeros are digits, the range test applies to the numeral's value, and N = 0 accepts no word,
since [1, 0] holds no integer.

Two fresh agents reviewed the specification against the request, as [the review](review.md)
records.  Neither found a disagreement.  The first asked for three corrections of the comment and
named inputs that no sample covered, and [the samples](Samples.lean) now cover them, 132 in all.
The second named three classes that no sample covers and three notes on the comments, which the
review lists with their responses.

[The program](Program.lean) holds the three functions in the verified compiler's dialect.
`parseArg` reads the buffer once with a state of four parts: the zero bytes seen, the value of the
argument's digits, whether every byte so far is a digit and the value stays below `2^64`, and
whether the argument has a byte.  `pick` tests `n != 0 && (0 - n) % n ≤ w` and returns
`w % n + 1`.  `render` computes the size of its text, `textSize`, builds an array of that many
words, and writes each value's digits and newline into it with `putLine`, in place, so the
generated bound charges one block for the text and one for the output buffer.  [The verified
compilation](Compiled.lean) writes a module that exports `parseArg`, `pick`, and `render` as
functions 3, 4, and 9.

## The choice of each value has the same number of words

| Theorem | Statement |
|---|---|
| `parseArg_eq`, `pick_eq`, `render_eq` | Each program equals its specification, `parseArg_eq` for a buffer of fewer than `2^64` bytes and `render_eq` for an array of fewer than `2^59` values ([the proof](Proof.lean)). |
| `parseArg_callSpec`, `pick_callSpec`, `render_callSpec` | `Verified.CallSpec compiled.module compiled.tables K spec compiled.f.bound` for `K` = 3, 4, and 9: called with a borrowed argument from a ready store with room for the bound, the function returns the specification's value without a trap and leaves a ready store ([the compilation](Compiled.lean)). |
| `parseArg_bound`, `pick_bound`, `render_bound` | The generated bounds are 0, 0, and at most `189 · values.size + 112` bytes. |
| `pick_count` | For every N and every v with 1 ≤ v ≤ N, exactly `⌊2^64 / N⌋` words w are accepted and give v ([the counting theorems](Unbiased.lean)). |
| `picks_count` | For every K and every sequence o of K values in [1, N], exactly `⌊2^64 / N⌋^K` sequences of K accepted words give o. |
| `accepted_count`, `accepted_half` | N ≥ 1 accepts `2^64 - (2^64 mod N)` words, `N · ⌊2^64 / N⌋`, and at least `2^63`. |
| `short_count` | For N ≥ 1 and M ≥ 4 K + 1024, at most `2^(64 M - 512)` of the `2^(64 M)` sequences of M words hold fewer than K accepted words. |

The theorems of the table use only `propext`, `Classical.choice`, and `Quot.sound`.  The counting
theorems assume no probability.  When the host's words are independent and uniform on
[0, 2^64), the first K accepted words are independent and uniform on the accepted set, since
whether a word is accepted depends on that word alone, so `picks_count` gives each sequence of K
values the probability `⌊2^64 / N⌋^K / (N · ⌊2^64 / N⌋)^K = N^(-K)`: the output is uniform on
[1, N]^K.  Under the same assumption, `accepted_half` makes each word accepted with probability at
least 1/2, and `short_count` bounds by `2^-512` the probability that M words hold fewer than K
accepted ones.

`pick_count` rests on the accepted words forming the interval [2^64 mod N, 2^64), whose length is
`N · ⌊2^64 / N⌋`.  Mathlib's `Nat.count_modEq_card` counts the naturals below a bound that have a
given residue, and its counts below `2^64` and below `2^64 mod N` differ by `⌊2^64 / N⌋` for every
residue c < N (`residue_count`).  `short_count` bounds the count by the exponential moment: the sum over
the sequences of `3^r`, with r a sequence's number of rejected words, is the M-th power of the sum
over one word, `2^64 + 2 R ≤ 2^65` for R ≤ `2^63` rejected words, and a sequence with fewer than K
accepted words has `r ≥ M - K + 1`, so the count is at most `2^(65 M) / 3^(M - K + 1)`, at most
`2^(64 M - 512)` when M ≥ 4 K + 1024.

## Facts for a loop of draws

[The loop's facts](CommandProof.lean) concern a loop that draws 512 words a pass and stops after
`passes K = K / 128 + 3` passes, and they depend on no call.  `choose_eq` states that the helper
`choose` of [the program](Program.lean) keeps the picks of the accepted little-endian words of a
buffer, in order, at most a given number of them.  `cap_count` states that at most
`2^(64 M - 512)` of the sequences of the `M = 512 · passes K` words of the passes hold fewer than K
accepted words, since `M ≥ 4 K + 1024`, so under independent uniform words such a loop ends its
passes with fewer than K values with probability at most `2^-512`.  This version has no WASI
command.

## Building and testing

```sh
tests/random-choice/run.sh
tests/verified/run.sh --cases randomChoice
tests/native/verified.sh --module randomChoice
```

[The demo's driver](../../tests/random-choice/run.sh) checks the hashes of the reviewed
specification and samples, builds the demo's modules, and elaborates [the theorem
statements](../../tests/random-choice/Axioms.lean), which requires the three axioms of each.
[The verified driver](../../tests/verified/run.sh) runs the 132 samples of [the verified
cases](../../Verified/Examples/Cases.lean) in Wasmtime against the specifications, and each case of
`render` requires the argument's block and the result's to stay allocated after the call, the
argument's alone for an empty result, which has no block.  [The native
driver](../../tests/native/verified.sh) runs the same cases on the module's translation to C,
compiled with CompCert.  All 132 pass in each.

## Related examples

[The random-residue histogram](../RandomHistogram/README.md) draws random words in the same way,
and this demo reuses its `wordAt`, `words`, and lemmas on argument buffers and words.  [The running
maximum](../../Examples/RunningMax/README.md) is a run of the verified-request skill on words.

## References

- [Verified Compiler Manual](../../docs/verified-manual.md)
- [Verified WASI Manual](../../docs/wasi.md)
- [`Verified.Call`](../../Verified/Call.lean)
- [Mathlib `Nat.count_modEq_card`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Data/Int/CardIntervalMod.lean)
