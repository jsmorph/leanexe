# Kadane's maximum segment sum

The maximum segment sum of a list of integers is the greatest sum of a run of consecutive elements, with the empty run, whose sum is 0, included.  Bird derives a linear-time program for it from a specification over all segments [1], and Bentley's column presents the problem and the linear scan that Kadane devised [2].  This directory holds the specification over ℤ, Kadane's algorithm over `Int64` in the verified compiler's dialect, a proof that the algorithm computes the specification when the absolute values of the elements sum to less than `2^63`, and the master theorem of the algorithm's WebAssembly module.  An AArch64 bare-metal Image that reads the words from the UART has a theorem that its output is the specification's value.

## Specification

[The specification](Spec.lean) defines `maxSegmentSum xs` for `xs : List Int` as `((xs.inits.map List.tails).flatten.map List.sum).foldr max 0`.  `List.inits` lists the prefixes of `xs`, `List.tails` the suffixes of each prefix, so the flattened list holds every segment of `xs`, and the fold takes the greatest of their sums from 0.  The value is therefore at least 0, and the empty list and a list of negative integers give 0.  The definition follows Bird's specification `maxL ∘ map sum ∘ concat ∘ map tails ∘ inits`, in which `maxL` folds `max` from 0, in the form of [the post on the Bird–Meertens derivation](https://satnam6502.github.io/bird-meertens/).  `List.inits` and `List.tails` come from Batteries.  The module's examples check the list `[-2, 1, -3, 4, -1, 2, 1, -5, 4]`, whose segment `[4, -1, 2, 1]` gives 6, and a list of negative integers, which gives 0.

## Program and proof

[The program](Program.lean) defines `mss : Array Int64 → Int64` as a fold from the left whose state `(best, ending)` starts at `(0, 0)`.  An element `x` sets `ending` to `max (ending + x) 0`, the greatest sum of a suffix of the elements read so far, the empty suffix included, and then `best` to `max best ending`.  The sums wrap modulo `2^64`.

[The proof](Proof.lean) establishes `mss_toInt`:

```lean
theorem mss_toInt (xs : Array Int64) (h : (xs.toList.map fun x => x.toInt.natAbs).sum < 2 ^ 63) :
    (mss xs).toInt = maxSegmentSum (xs.toList.map Int64.toInt)
```

The invariant of the fold states that after a prefix `p`, `best` is `maxSegmentSum p` and `ending` is `maxSuffixSum p`, the greatest sum of a suffix of `p`, the empty suffix included.  The suffixes of `p ++ [x]` are the suffixes of `p` with `x` appended and the empty list, which gives `maxSuffixSum (p ++ [x]) = max (maxSuffixSum p + x) 0`.  The segments of `p ++ [x]` are those of `p` and the suffixes of `p ++ [x]`, which gives `maxSegmentSum (p ++ [x]) = max (maxSegmentSum p) (maxSuffixSum (p ++ [x]))`.  These equations are the program's step over ℤ, so the proof needs neither Bird's derivation nor its fusion laws.  The invariant also bounds `ending` by the sum of the absolute values of `p`, so under the hypothesis no `Int64` sum of the program wraps.  Without the hypothesis, the words of `best` and `ending` may wrap, and the result need not be the specification's value.

## The WebAssembly module

[The compiled module](Compiled.lean) compiles `mss` into the module `libmss`, in which the function borrows its array and allocates nothing.  [The master theorem](Master.lean) states the specification without the program's definitions:

```lean
theorem mss_master :
    Verified.Master compiled.module compiled.tables "mss" compiled.mss.bound
      (fun (xs : Array Int64) => (xs.toList.map fun x => x.toInt.natAbs).sum < 2 ^ 63)
      (fun (xs : Array Int64) (y : Int64) => y.toInt =
        (((xs.toList.map Int64.toInt).inits.map List.tails).flatten.map List.sum).foldr max 0)
```

The export `mss`, called from a ready store on an array of `Int64` values whose absolute values sum to less than `2^63`, returns without a trap a value whose integer is the maximum segment sum of the values read as integers.  It follows from the compiler's theorem without a trap, `compiled.mss.trapFree`, and `mss_toInt`.  [The file theorems](File.lean) check that `build/verified/libmss.wasm`, which `tests/verified/run.sh` writes, holds the module's bytes.

## The AArch64 Image

[The Image's program](../../../tests/TestSupport/A64/Mss.lean) compiles `mss` with `wordAt` and `mssBytes`, a function over bytes that the third entry routine, `genBytesImage`, calls on a message that it reads from the UART.  `mssBytes` reads a message of `8 n` bytes as `n` words, each from its eight bytes with the lowest first, takes the words as `Int64` values, and returns the eight bytes of the word of `mss` of those values, the lowest first.  A message whose length is not a multiple of 8 gives no bytes.  The Image accepts messages of at most 8,800,000 bytes, and its memory's cap of 269 pages holds the message's block, the array of its words, and the result's block above the heap's start, so the compiler's theorem without a trap covers every message within the limit.

[The Image's theorems](../../../tests/TestSupport/A64/ImageFilesMss.lean) are `mss_uart`, `mss_uart_over`, and `mss_uart_flag`, in the form of the flip Image's in [the AArch64 document](../../../docs/a64-bare-metal.md#the-final-theorem), and `mss_uart_spec`:

```lean
theorem mss_uart_spec (h : Hw) (b : Boot) (B : UInt64) (hB : B.toNat % 4096 = 0)
    (hlo : 0x40000000 ≤ B.toNat) (hhi : B.toNat + mssMemSize ≤ 0x80000000)
    (hm : ∀ j < mssFileSize, b.core.mem (B + UInt64.ofNat j) = byteAt mssFile j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff)
    (hio : b.core.io.rxNext = 0 ∧ b.core.io.rxPolls = 0) (ws : List Int64)
    (hlen : 8 * ws.length ≤ 8800000) (hsum : (ws.map fun w => w.toInt.natAbs).sum < 2 ^ 63)
    (hd : h.rx.Delivers
      (bytesOf (UInt64.ofNat (8 * ws.length)) ++ (ws.map Int64.toUInt64).flatMap bytesOf)) :
    ∃ (b' : Boot) (y : Int64), BootReach h (protectedBytes B mssLength)
        (fetchFrom b.core.mem B (codeWords mssLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords mssLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ bytesOf y.toUInt64 ++ [0] ∧
      y.toInt = Library.Arrays.MaxSegmentSum.maxSegmentSum (ws.map Int64.toInt)
```

Suppose memory holds the bytes of `mss.img` at a base `B` that is a multiple of 4096 inside the RAM GiB, the core starts at `B` at EL1 with the MMU off, and the UART's receiver delivers, with no error flag, the eight bytes of the length `8 n` and then the eight bytes of each of `n` words, the lowest first.  If the length is at most 8,800,000 and the absolute values of the words, read as signed 64-bit integers, sum to less than `2^63`, the boot machine reaches the PSCI SYSTEM_OFF call after writing to the UART the eight bytes of a word `y` and the status byte 0, and `y`, read as a signed integer, is `maxSegmentSum` of the words read as integers.  Every message of `8 n` bytes is the bytes of some list of `n` words, so the hypothesis on the message's form restricts only its length.  The statement names the specification, `bytesOf`, and the boot model, and none of the program's definitions.

## Tests

`tests/verified/run.sh` runs the export `mss` of `libmss.wasm` on arrays from `TestSupport.LibraryCases` and compares each result with native Lean's.  `tests/baremetal/a64-uart.sh` writes `mss.img`, has the kernel check its theorems, and runs the Image under QEMU on the messages of `TestSupport.A64.Mss.messages`: no words, one word, two words, the list above, 50 pseudo-random words in `[−2^20, 2^20)`, 100 pseudo-random words of any value, the words `2^62`, `−1`, and `2^62 − 2`, whose absolute values sum to `2^63 − 1`, the largest word, the least word above `−2^63`, 30 negative words, and 13 bytes.  It also runs the lengths 8,800,001 and `2^64 − 1`, above the limit, and a break on the line.  The UART's bytes must equal those that native Lean computes.  The 53 module cases pass in Wasmtime.  Under TCG the kernel's check of the five Image theorems passes, and so does every run: each of the 11 messages from a file and from a pipe in pieces, the two lengths above the limit with the status 64, and the break with the status 65.  The Image has not run under KVM.

## Limits

The theorems over ℤ hold under the bound on the sum of the absolute values, which excludes `Int64.minValue` and admits a list of words in `[−2^63 + 1, 2^63 − 1]` only when their absolute values sum to less than `2^63`.  The program accepts every array, and outside the bound its sums wrap.  `mss_uart_spec` concerns the model of the boot machine, whose agreement with the processor rests on [the AArch64 document's trusted base](../../../docs/a64-bare-metal.md#trusted-base).

## References

1. R. S. Bird, "Algebraic identities for program calculation", *The Computer Journal* 32(2):122–126, 1989, [doi:10.1093/comjnl/32.2.122](https://doi.org/10.1093/comjnl/32.2.122).
2. J. Bentley, "Programming pearls: algorithm design techniques", *Communications of the ACM* 27(9):865–873, 1984, [doi:10.1145/358234.381162](https://doi.org/10.1145/358234.381162).
