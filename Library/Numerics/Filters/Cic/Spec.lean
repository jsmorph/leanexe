import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Function.Iterate

/-! This module specifies a cascaded integrator–comb (CIC) decimation filter of order `N`,
decimation `R`, and differential delay `M` over the integers.  A signal is a function from the
integers, read as times, to the integers.  For a length `L`, the moving sum of a signal `y` is the
signal whose value at time `t` is `y(t) + y(t − 1) + ⋯ + y(t − L + 1)`, the sum of `y` over the `L`
consecutive times that end at `t`, and the moving sum of length 0 is the signal 0.
`movingSum L y t` gives this value as the sum over `i < L` of `y (t − i)`, with `t − i` computed in
ℤ.

An input is a sequence of integers `x₀, x₁, x₂, …`, with sample `xₜ` at time `t`.  The filter reads
it as the signal with value `xₜ` at each time `t ≥ 0` and 0 at each negative time, which `extend x`
gives.  The filter applies the moving sum of length `R·M` to that signal `N` times, and applying it
0 times leaves the signal unchanged.  Block `m` of the input holds the samples at times `m·R` to
`m·R + R − 1`, and output `m`, for each `m ≥ 0`, is the value of the `N`-fold moving sum at time
`m·R + R − 1`, the time of the last sample of block `m`.  `output N R M x m` gives output `m`.

A finite input is a list of `n` integers `x₀, …, x_{n−1}`.  It gives `⌊n / R⌋` outputs, one for each
complete block, in increasing order of `m`, and `outputs N R M xs` gives that list.  Output `m` of
the list is output `m` of the sequence that agrees with the list at times below `n` and is 0 from
time `n` on.  Output `m` depends only on samples at times up to `m·R + R − 1`, since each moving sum
depends only on times at or before the time of its value, and, for `R ≥ 1`, `m·R + R − 1 < n`
exactly when `m < ⌊n / R⌋`.  The zeros after the end of the list therefore change no output, and the
last `n mod R` samples, which form no complete block, give no output.  `outputs xs` reads `xs` as
the whole input from time 0, so `outputs xs` is a prefix of `outputs (xs ++ ys)`.  For `R, M ≥ 1`,
output `m` reads the `N·(R·M − 1) + 1` samples that end at time `m·R + R − 1`, which span several
blocks when `N·(R·M − 1) ≥ R`.

Every value is an unbounded integer, and the outputs are unnormalized: for `R, M ≥ 1`, the `N`-fold
moving sum of a constant input of 1 equals the gain `(R·M)^N` at every time from `N·(R·M − 1)` on.
Hogenauer's equation (3) gives the system function of his structure, referenced to the input rate,
`N` integrators at the input rate, decimation by `R`, and `N` combs of differential delay `M` at the
output rate, as `((1 − z^(−R·M)) / (1 − z^(−1)))^N = (1 + z^(−1) + ⋯ + z^(−(R·M − 1)))^N`, which is
the system function of the `N`-fold moving sum of length `R·M` (E. B. Hogenauer, "An economical
class of digital filters for decimation and interpolation," IEEE Transactions on Acoustics, Speech,
and Signal Processing 29(2), 1981).  The reading of the input as 0 before time 0 corresponds to
registers that start at 0, and the time `m·R + R − 1` to a decimator that keeps the last sample of
each block, for integrators whose output at time `t` includes the input at time `t`, as in
Hogenauer's equation (1), and combs whose output at index `m` is `v(m) − v(m − M)`.  A register in
the forward path of a stage delays the result by one sample.

The input of `output` is a sequence, a function on ℕ, and the input of `outputs` is a list.  The
sequence form states the filter at every time, and the list form states what an implementation
computes from finitely many samples.  Such an implementation emits an output each time a block of
`R` samples completes, which gives the count `⌊n / R⌋`, and `outputs` computes each output with
`output`, so the filter has one definition.

Signals are functions on ℤ, so `t − i` and `m·R + R − 1` are integer expressions, and no subtraction
truncates.  With natural-number times, `t − i` would truncate to 0 for `i > t` and read `x₀` where
the filter reads 0.  The moving sum of a signal that is 0 at every negative time is again 0 at every
negative time, so each of the `N` stages reads its input as 0 before time 0.

The sampling time `m·R + R − 1` is a convention, and a filter that keeps another sample of each
block computes a different function.  The parameters are natural numbers, and the filter has its
usual meaning for `R ≥ 1` and `M ≥ 1`.  With `R = 0` a list gives no outputs, since `n / 0 = 0` in
Lean, and the sequence form gives 0 at every index.  With `M = 0` and `N ≥ 1` every output is 0, and
with `N = 0` output `m` is the sample at time `m·R + R − 1`, decimation alone. -/

namespace Library.Numerics.Filters.Cic

def movingSum (L : ℕ) (y : ℤ → ℤ) (t : ℤ) : ℤ :=
  ∑ i ∈ Finset.range L, y (t - i)

def extend (x : ℕ → ℤ) (t : ℤ) : ℤ :=
  if 0 ≤ t then x t.toNat else 0

def output (N R M : ℕ) (x : ℕ → ℤ) (m : ℕ) : ℤ :=
  (movingSum (R * M))^[N] (extend x) ((m : ℤ) * R + R - 1)

def outputs (N R M : ℕ) (xs : List ℤ) : List ℤ :=
  (List.range (xs.length / R)).map (output N R M fun t => xs.getD t 0)

-- `N = 1`, `R = 2`: times 1 and 3 give 2 + 1 and 4 + 3, and the sample 5 forms no complete block.
example : outputs 1 2 1 [1, 2, 3, 4, 5] = [3, 7] := by decide

-- Times 1, 3, and 5 give −1 + 3, 1 − 4, and −9 − 5.
example : outputs 1 2 1 [3, -1, -4, 1, -5, -9] = [2, -3, -14] := by decide

-- One moving sum of length 2 is 1, 3, 5, 7, 9, 11, and the second gives 3 + 1, 7 + 5, and 11 + 9
-- at times 1, 3, and 5.
example : outputs 2 2 1 [1, 2, 3, 4, 5, 6] = [4, 12, 20] := by decide

-- One moving sum of length 2 is 1, 0, 0, 0, 0, 0, and the second gives 0 + 1, 0 + 0, and 0 + 0.
example : outputs 2 2 1 [1, -1, 1, -1, 1, -1] = [1, 0, 0] := by decide

-- One moving sum of length 3 is 2, −1, 4, −5, 9, −9, and the second gives 4 − 1 + 2 at time 2 and
-- −9 + 9 − 5 at time 5.  The sample 17 forms no complete block.
example : outputs 2 3 1 [2, -3, 5, -7, 11, -13, 17] = [5, -5] := by decide

-- `M = 2`, window 4: times 1, 3, and 5 give 2 + 1, 4 + 3 + 2 + 1, and 6 + 5 + 4 + 3.
example : outputs 1 2 2 [1, 2, 3, 4, 5, 6] = [3, 10, 18] := by decide

-- `N = 0`: the samples at times 2 and 5.
example : outputs 0 3 1 [7, 8, 9, 10, 11, 12, 13] = [9, 12] := by decide

-- Times 1 and 3 give 2 · (2^63 − 1) and 2 · (−2^63), outside the range of signed 64-bit integers.
example :
    outputs 1 2 1 [9223372036854775807, 9223372036854775807, -9223372036854775808,
      -9223372036854775808] = [18446744073709551614, -18446744073709551616] := by decide

example : outputs 3 2 1 [] = [] := by decide

-- `R = 0` gives no outputs, and `M = 0` gives 0.
example : outputs 1 0 1 [1, 2] = [] := by decide
example : outputs 2 2 0 [1, 2, 3, 4] = [0, 0] := by decide

-- A constant input of 1 with `N = 3`, `R = 2`: the three moving sums are 1, 2, 2, …, then
-- 1, 3, 4, 4, …, then 1, 4, 7, 8, 8, …, so output 0, at time 1, is 4 and output 1, at time 3, is
-- the gain 2^3.
example : output 3 2 1 (fun _ => 1) 0 = 4 ∧ output 3 2 1 (fun _ => 1) 1 = 8 := by decide

-- `R = 1`: every sample ends a block, and the moving sums of length 2 are 1, 3, 5, then 1, 4, 8.
example : outputs 2 1 2 [1, 2, 3] = [1, 4, 8] := by decide

-- A nonempty input shorter than one block gives no output.
example : outputs 1 3 1 [1, 2] = [] := by decide

-- `N = 2`, `M = 2`, window 4: the first moving sum is 1, 3, 6, 10, 14, 18, 22, 26, and the second
-- gives 3 + 1, 10 + 6 + 3 + 1, 18 + 14 + 10 + 6, and 26 + 22 + 18 + 14 at times 1, 3, 5, and 7.
example : outputs 2 2 2 [1, 2, 3, 4, 5, 6, 7, 8] = [4, 20, 48, 80] := by decide

-- `N = 0` with `R = 1` keeps every sample, and with `M = 0` it keeps the samples at times 1 and 3.
example : outputs 0 1 1 [5, 6] = [5, 6] := by decide
example : outputs 0 2 0 [1, 2, 3, 4] = [2, 4] := by decide

-- `R = 0` in the sequence form reads time −1, where the signal is 0.
example : output 0 0 1 (fun _ => 1) 0 = 0 := by decide

end Library.Numerics.Filters.Cic
