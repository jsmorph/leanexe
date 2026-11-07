# The CIC decimation filter

A cascaded integrator–comb (CIC) filter of order N, decimation R, and differential delay M lowers a signal's sample rate by R with N integrators at the input rate and N combs at the output rate, using additions and subtractions alone [1].  This directory holds the filter's specification over the integers, a block form of the cascade that serves the integers and 64-bit words, a proof that the cascade computes the specification, and a proof that its outputs in 64-bit words are exact under Hogenauer's bound.  A program in the verified compiler's dialect computes the filter of order 3, decimation 8, and delay 1.  Its AArch64 bare-metal Image has a theorem that the Image's UART output is the specification's outputs on a fixed table of 64 samples, and the Image's runs under QEMU, with TCG and with KVM, write the outputs of an independent Python reference.

## Specification

[The specification](Spec.lean) defines the filter as a repeated moving sum over ℤ.  `movingSum L y t` is `y(t) + y(t − 1) + ⋯ + y(t − L + 1)` for a signal `y : ℤ → ℤ`, and `extend x` reads a sequence of samples as the signal that is 0 before time 0.  `output N R M x m` is the value at time `m·R + R − 1`, the last sample of block `m`, of the moving sum of length `R·M` applied `N` times to that signal.  `outputs N R M xs` gives the `⌊n / R⌋` outputs of a list of `n` samples, one for each complete block of `R`.

Hogenauer's equation (3) gives the cascade's system function, referenced to the input rate, as `(1 + z^(−1) + ⋯ + z^(−(R·M − 1)))^N`, the system function of the `N`-fold moving sum of length `R·M` [1].  The reading of the input as 0 before time 0 corresponds to registers that start at 0, and the time `m·R + R − 1` to a decimator that keeps the last sample of each block, for integrators whose value at a time includes the input at that time.  The outputs are unnormalized: for a constant input of 1, the outputs from time `N·(R·M − 1)` on equal the gain `(R·M)^N`.  An independent review compared the definitions with the English statement in the module's docstring.

## Block cascade

[The cascade module](Cascade.lean) defines the cascade once, over any type with a zero, an addition, and a subtraction.  `integrate` gives the running sums of a list, `decimate R` keeps the last element of each complete block of `R`, `comb M` subtracts from each element the element `M` before it, and `cascade N R M` applies `N` integrators, the decimation, and `N` combs.  `cascade_eq_outputs` proves that the cascade over ℤ equals `outputs N R M xs` for every order, decimation, delay, and list.

The proof reads a list as a signal.  The difference of a moving sum of length `L` is the comb of delay `L` of its input, and combs commute, so `N` differences of `N` combs of the integrators' output agree with the `N` differences of the `N`-fold moving sum.  Sampling at `m·R + R − 1` turns a comb of delay `R·M` into a comb of delay `M` at the output rate.  Over ℤ the cascade also evaluates the filter with `N·n` additions and `N·⌊n / R⌋` subtractions, where `outputs` reads the input `(R·M)^N` times for each output.

## Exactness in 64-bit words

At `UInt64` the cascade's operations wrap modulo `2^64`.  In [the exactness module](Exact.lean), `cascade_eq_map_ofInt` states that the word cascade of any input words gives the residues of the outputs over ℤ of the words read as signed integers.  `toInt_cascade` reads each output word as its exact output reduced into `[−2^63, 2^63)`.  `toInt_cascade_of_width` concludes that each output word reads as its exact output when every sample lies in `[−2^(B−1), 2^(B−1))` and `(R·M)^N · 2^(B−1) ≤ 2^63`.  For `R·M ≥ 1` and `B ≥ 1`, that condition is Hogenauer's `B + ⌈N·log₂(R·M)⌉ ≤ 64` [1].  The integrators' words may wrap, since each word is the residue of its value over ℤ, so only the outputs need the bound.

## Program

[The program](Program.lean) writes the filter of order 3, decimation 8, and delay 1 in the verified compiler's dialect, on `Array UInt64`.  `integratePass`, `decimatePass`, and `combPass` are folds whose state holds one word and the result so far: the running sum, the position in a block of 8, and the previous element.  `cic` composes three integrator passes, the decimation, and three comb passes.  `cic_toList` in [the proof module](Proof.lean) proves `(cic xs).toList = cascade 3 8 1 xs.toList` for every input array.  The proof takes the integrator's and the comb's folds by induction from the left, and the decimation's fold by induction from the right, with the invariant that its counter is the length read so far modulo 8.

## The AArch64 Image

[The table module](../../../../tests/TestSupport/A64/CicTable.lean) holds the table `input` and the entry `cicCheck n`, which filters the first `n` samples of the table, and `verified_compile` compiles the entry with the passes.  A wrapper, the form in which a compiled entry passes a table to a function, takes at least one parameter, so the entry takes the count and the Image passes 64, the whole table.  The table holds signed 16-bit samples, each stored as its two's-complement word.  `input_toInt` states its samples as integers:

| Samples | Value | Purpose |
|---|---|---|
| 0 to 23 | −32768 | A step from the 0 before time 0 to the most negative sample.  Output 2 reads 22 equal samples and equals `−2^24`, the least output that Hogenauer's bound admits for 16-bit samples. |
| 24 to 47 | 32767 | A step to the most positive sample.  Output 5 equals `512 · 32767 = 16,776,704`. |
| 48 to 63 | 16384 and −16384, alternating every 4 samples | A square wave of period `R·M = 8` with zero sum over each period. |

[The program's theorems](../../../../tests/TestSupport/A64/Cic.lean) are `check_toInt` and `runs`.  `check_toInt` states that the words of `cicCheck 64`, read as signed integers, are `outputs 3 8 1` of the table's samples.  It follows from `cic_toList` and `toInt_cascade_of_width` with `B = 16`, since `(8·1)^3 · 2^15 = 2^24 ≤ 2^63`.  `runs` states the program's run in the form that the Image's theorem takes, with the result as the only outcome: the compiler's trap-free theorem covers the allocations, and the stack's bound fits the stack's room.

[The Image theorems](../../../../tests/TestSupport/A64/ImageFiles.lean) end in `cic_outputs`:

```lean
theorem cic_outputs (h : Hw) (B : UInt64) (hB : B.toNat % 4096 = 0) (hlo : 0x40000000 ≤ B.toNat)
    (hhi : B.toNat + cicImageSize ≤ 0x80000000) (b : Boot)
    (hm : ∀ j < cicSize, b.core.mem (B + UInt64.ofNat j) = byteAt cicBytes j)
    (hpc : b.core.pc = B) (hoff : b.mmuOff) :
    ∃ (b' : Boot) (ys : Array UInt64), BootReach h (protectedBytes B cicLength)
        (fetchFrom b.core.mem B (codeWords cicLength)) b b' ∧
      fetchFrom b.core.mem B (codeWords cicLength) b'.core.pc = some (encode .hvc0) ∧
      b'.core.x 0 = 0x84000008 ∧ b'.uartDone = true ∧
      b'.core.out = b.core.out ++ LeanExe.Native.encodeArray ys ++ [0] ∧
      ys.toList.map (fun w => w.toBitVec.toInt) =
        Library.Numerics.Filters.Cic.outputs 3 8 1
          (TestSupport.A64.Cic.input.toList.map fun w => w.toBitVec.toInt)
```

Suppose memory holds the bytes of `cic.img`, which the kernel compares with the generator's output, at a base `B` that is a multiple of 4096 inside the RAM GiB, and the core starts at `B` at EL1 with the MMU off.  Then the boot machine reaches the PSCI SYSTEM_OFF call after writing to the UART the encoding of an array `ys` followed by the status byte 0.  The words of `ys`, read as signed 64-bit integers, are the specification's outputs on the table's samples read as integers.  The statement names `outputs`, the table, and the boot model, and none of the program's definitions.  [The AArch64 document](../../../../docs/a64-bare-metal.md#the-final-theorem) describes the boot model, the premises, and [the trusted base](../../../../docs/a64-bare-metal.md#trusted-base).

## Tests

[The Python reference](../../../../tests/cic/reference.py) computes the filter from its definition over Python's integers, and as a cascade of 64-bit words that wrap, without the Lean specification.  `uv run tests/cic/reference.py` runs its self-test.  [The table's listing](../../../../tests/cic/table.py) prints the samples in the reference's input form and, with the argument `lean`, as the Lean literal of the table.  `uv run tests/cic/reference.py outputs 3 8 1 $(uv run tests/cic/table.py)` prints the table's eight outputs, and `--hex` after `1` prints the bytes of their words.

[The Image test](../../../../tests/baremetal/a64-images.sh) writes the Images, has the kernel check their theorems, and runs each Image under QEMU's `virt` machine with TCG or KVM, as `ACCEL` selects.  It compares the UART's bytes with the bytes that Lean computes.  Under both accelerators, `cic.img` writes the length word 8, then the outputs −3,932,160, −14,942,208, −16,777,216, −8,913,016, 13,106,744, 16,776,704, 14,155,384, and 2,621,384, then the status byte 0.  These bytes equal the reference's.

## Limits

The program fixes order 3, decimation 8, and delay 1, while the specification, the cascade, and the exactness theorems hold for every order, decimation, and delay.  The Image filters the table compiled into it and reads no input at run time.  The table's integrators stay below `2^30` in magnitude, so the runs do not exercise the wraparound of 64-bit words, which the theorems cover for every input.  `cic_outputs` concerns the model of the boot machine.  Its agreement with the processor rests on [the AArch64 document's trusted base](../../../../docs/a64-bare-metal.md#trusted-base), among them the model's instruction semantics, which [the check against Isla's traces](../../../../docs/a64-bare-metal.md#isla) compares with Arm's specification.

## References

1. E. B. Hogenauer, "An economical class of digital filters for decimation and interpolation", *IEEE Transactions on Acoustics, Speech, and Signal Processing* 29(2):155–162, 1981, [doi:10.1109/TASSP.1981.1163535](https://doi.org/10.1109/TASSP.1981.1163535).
2. [The AArch64 bare-metal path](../../../../docs/a64-bare-metal.md).
