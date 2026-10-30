# Natural numbers on limbs and exact unrounded scaling: `Uscale`

The module `Uscale` holds the integer routines that the decimal parsers and printers share: natural numbers of any size as arrays of 32-bit limbs in 64-bit words, and Cox's unrounded scaling [1] computed with them exactly.  `ParseFloat` and `PrintFloat` include these routines in their modules, and `Uscale` also has a standalone compilation.  Every routine has a theorem that states its result as a natural number, proved with only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and the verified compiler accepts the module.

## Specification

An array `a` denotes `val a = Σ a[i] · 2 ^ (32 i)`, least significant limb first, and `Limbs a` states that every element is below `2 ^ 32`; arrays may carry zero limbs at the top.  [The base module](UscaleBase.lean) defines both and proves that the element at position `i`, read with `a[i]!` and 0 past the end, is the base-`2 ^ 32` digit `i` of `val a` (`getElem!_digit`).  Each theorem below takes `Limbs` for its array arguments and a bound on their sizes, such as `a.size < 2 ^ 32`, which keeps the dialect's word positions exact; the arrays of the parsers and printers have fewer than 300 limbs.

| Routine | Result |
|---|---|
| `mulSmall a m c` | `val a · m + c` for words `m, c < 2 ^ 32`, one limb longer than `a` |
| `shl a k` | `val a · 2 ^ k` |
| `le a b` | `decide (val a ≤ val b)` |
| `sub a b` | `val a - val b` when `val b ≤ val a`, as many limbs as `a` |
| `wordBits x`, `bitLen a` | `Nat.size`, the number of bits, of `x` and of `val a` |
| `divBits n d bits` | `val n / val d` as a word and `val n % val d` as limbs, when `val n < val d · 2 ^ bits` and `bits ≤ 63` |
| `scaledQuot n d sn sd bits` | `⌊val n · 2 ^ sn / (val d · 2 ^ sd)⌋` as a word and whether the division leaves a remainder |
| `mulPow10 a k`, `pow10 k` | `val a · 10 ^ k` and `10 ^ k` |

## Algorithm

A limb of 32 bits keeps every intermediate value of the routines inside one word: the product of two limbs plus two limbs is at most `(2 ^ 32 - 1) ^ 2 + 2 · (2 ^ 32 - 1) = 2 ^ 64 - 1`.  `mulSmall` runs through the limbs once with a carry below `2 ^ 32`.  `shl` multiplies by `2 ^ (k % 32)` with `mulSmall` and then places `k / 32` zero limbs below the result.  `le` compares limbs from the top and stops at the first difference, `sub` runs through the limbs with a borrow, and `bitLen` finds the highest nonzero limb and the bit length of that limb.  `divBits` is restoring division: for `j` from `bits - 1` down to 0 it compares `d · 2 ^ j` with the remainder and subtracts it when it fits, setting bit `j` of the quotient, so its cost is `bits` shifts, comparisons, and subtractions.  `scaledQuot` divides `n · 2 ^ sn` by `d · 2 ^ sd` this way; the pair of the quotient and the remainder flag is Cox's unrounded form of the quotient [1], from which a rounding to nearest, a floor, or a ceiling follows.  `mulPow10` multiplies by `10 ^ 9` as many times as `k / 9` and once by `10 ^ (k % 9)`, and `pow10 k` is `mulPow10` applied to 1.

## Implementation

[`Uscale.lean`](Program.lean) holds the routines in the verified dialect, written for this project from the description above; no third-party code is ported.  The module compiles with `verified_compile` in about 20 seconds.  `limb` reads an element and gives 0 past the end without reading past it, since native Lean prints a panic with a backtrace for every read past the end: the first native check printed 12,082 of them.  Each loop is `LeanExe.loop` over limbs or bit positions with a state of an array and a word, so every routine allocates its result through the runtime and its byte theorem allows a trap when memory cannot grow.

## Theorems

| Theorem | Module | Statement |
|---|---|---|
| `loop_inv` | `UscaleBase` | Induction principle of `LeanExe.loop`: an invariant at 0 kept by each step holds after the count. |
| `getElem!_digit` | `UscaleBase` | `(a[i]!).toNat = val a / 2 ^ (32 i) % 2 ^ 32` for `Limbs a` |
| `mulSmall_spec` | `UscaleBase` | `Limbs`, `val (mulSmall a m c) = val a · m + c`, size `a.size + 1` |
| `shl_spec` | `UscaleArith` | `Limbs`, `val (shl a k) = val a · 2 ^ k`, size `a.size + 1 + k / 32` |
| `le_spec` | `UscaleArith` | `le a b = decide (val a ≤ val b)` |
| `sub_spec` | `UscaleArith` | `Limbs`, `val (sub a b) = val a - val b` for `val b ≤ val a`, size `a.size` |
| `wordBits_spec`, `bitLen_spec` | `UscaleArith` | `(bitLen a).toNat = Nat.size (val a)` |
| `divBits_spec` | `UscaleDiv` | the quotient word is `val n / val d`, and the remainder has `Limbs` and value `val n % val d` |
| `scaledQuot_spec` | `UscaleDiv` | the quotient word is `val n · 2 ^ sn / (val d · 2 ^ sd)`, and the flag is `decide (val n · 2 ^ sn % (val d · 2 ^ sd) ≠ 0)` |
| `mulPow10_spec`, `pow10_spec` | `UscaleDiv` | `Limbs`, `val (mulPow10 a k) = val a · 10 ^ k`, `val (pow10 k) = 10 ^ k` |

## Proof

Every loop invariant states a fact about the value of the first `k` limbs, `val a % 2 ^ (32 k)`, which `getElem!_digit` and `mod_succ` extend by one limb.  `mulSmall`'s invariant is `val out + 2 ^ (32 k) · carry = (val a % 2 ^ (32 k)) · m + c`, and `sub`'s is `val out + val b % 2 ^ (32 k) = val a % 2 ^ (32 k) + 2 ^ (32 k) · borrow`; at the end the borrow is 0 because `val b ≤ val a` and the result has `a.size` limbs.  `le`'s state is 0 while the values agree above the current limb, and 1 or 2 once they differ.  `divBits`'s invariant after `k` steps is that the quotient word is `⌊val n / (val d · 2 ^ (bits - k))⌋ · 2 ^ (bits - k)` and the remainder is `val n % (val d · 2 ^ (bits - k))`; `halve_div` gives the step from a divisor to half of it.  The modules are [`UscaleBase.lean`](UscaleBase.lean), [`UscaleArith.lean`](UscaleArith.lean), and [`UscaleDiv.lean`](UscaleDiv.lean).

## Tests

[`UscaleCheck.lean`](UscaleCheck.lean) runs the compiled native code of every routine on 400 pseudo-random operands of up to 120 limbs, and `pow10` for every `k` below 400, and compares each result with Lean's `Nat`.  All 4,026 results agree, in 10 seconds.

## Limits

The theorems concern the Lean functions; the compiled module's correctness comes from the verified compiler's theorem and trusts Talos's semantics and decoder.  The size hypotheses exclude arrays that WebAssembly's memory could not hold.

## References

1. R. Cox, "Floating-Point Printing and Parsing Can Be Simple And Fast (Floating Point Formatting, Part 3)", 19 January 2026, [research.swtch.com/fp](https://research.swtch.com/fp), sections "Unrounded Numbers" and "Unrounded Scaling".  Not peer reviewed.
