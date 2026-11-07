import Library.Numerics.Filters.Cic.Cascade
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! This module proves that the block cascade of `Cascade.lean` in 64-bit words computes each output
of the CIC decimation filter modulo `2^64`, and that each output word's two's-complement reading is
the exact output under Hogenauer's bound.  A word `w : UInt64` reads as the integer
`w.toBitVec.toInt` in `[−2^63, 2^63)`, and `UInt64.ofInt` maps an integer to the word that holds its
residue modulo `2^64`.  `UInt64.ofInt` preserves zero, addition, and subtraction, so `cascade_map`
and `cascade_eq_outputs` give `cascade_ofInt`: the word cascade of the residues of an integer input
is the list of residues of the outputs.  Every word is the residue of its reading, so
`cascade_eq_map_ofInt` states the word cascade of any input words as the residues of the outputs of
the words' readings.  `toInt_cascade` reads both sides: each output word reads as its exact output
reduced by `Int.bmod` into `[−2^63, 2^63)`.

`outputs_bound` is Hogenauer's bound in an asymmetric form.  If every sample lies in `[−A, A']` with
`A, A' ≥ 0`, each moving sum of length `L` lies in `[−L·A, L·A']`, so every output lies in
`[−(R·M)^N·A, (R·M)^N·A']`.  The bound requires `A, A' ≥ 0` because the specification reads the
input as 0 before time 0 and after the end of a list.  `toInt_cascade_of_bound` concludes that each
output word reads as its exact output when `(R·M)^N·A ≤ 2^63` and `(R·M)^N·A' < 2^63`, which place
every output in `[−2^63, 2^63)`, where `Int.bmod y (2^64) = y` (`Int.bmod_eq_of_le_mul_two`).
`toInt_cascade_of_width` states the case of inputs of `B` bits, `[−2^(B−1), 2^(B−1))`, under
`(R·M)^N·2^(B−1) ≤ 2^63`.  For `R·M ≥ 1` and `B ≥ 1` that condition is Hogenauer's
`B + ⌈N·log₂(R·M)⌉ ≤ 64`, since both say `(R·M)^N ≤ 2^(64−B)`.  It admits the most negative input
`−2^(B−1)`, whose outputs reach `−2^63` when `(R·M)^N·2^(B−1) = 2^63`, and it implies the strict
bound on the positive side, `(R·M)^N·(2^(B−1) − 1) < 2^63`.  The theorems place no bound on the
integrators, whose words wrap whenever their values over ℤ leave `[−2^63, 2^63)`.  Each word is the
residue of its value over ℤ, so only the outputs need a bound. -/

namespace Library.Numerics.Filters.Cic

theorem movingSum_bound (L : ℕ) {A A' : ℤ} {y : ℤ → ℤ} (hy : ∀ t, -A ≤ y t ∧ y t ≤ A') (t : ℤ) :
    -(L * A) ≤ movingSum L y t ∧ movingSum L y t ≤ L * A' := by
  constructor
  · have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.range L) => (hy (t - i)).1
    simpa [movingSum] using h
  · have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.range L) => (hy (t - i)).2
    simpa [movingSum] using h

theorem iterate_movingSum_bound (L N : ℕ) {A A' : ℤ} {y : ℤ → ℤ}
    (hy : ∀ t, -A ≤ y t ∧ y t ≤ A') (t : ℤ) :
    -((L : ℤ) ^ N * A) ≤ (movingSum L)^[N] y t ∧ (movingSum L)^[N] y t ≤ (L : ℤ) ^ N * A' := by
  induction N generalizing t with
  | zero => simpa using hy t
  | succ N ih =>
    rw [Function.iterate_succ_apply',
      show (L : ℤ) ^ (N + 1) * A = L * (L ^ N * A) by ring,
      show (L : ℤ) ^ (N + 1) * A' = L * (L ^ N * A') by ring]
    exact movingSum_bound L ih t

/-- Hogenauer's bound: if every sample lies in `[−A, A']`, output `m` lies in
`[−(R·M)^N·A, (R·M)^N·A']`. -/
theorem output_bound (N R M : ℕ) {A A' : ℤ} (hA : 0 ≤ A) (hA' : 0 ≤ A') {x : ℕ → ℤ}
    (hx : ∀ t, -A ≤ x t ∧ x t ≤ A') (m : ℕ) :
    -((R * M : ℤ) ^ N * A) ≤ output N R M x m ∧ output N R M x m ≤ (R * M : ℤ) ^ N * A' := by
  have he : ∀ t, -A ≤ extend x t ∧ extend x t ≤ A' := by
    intro t
    unfold extend
    split_ifs
    · exact hx _
    · exact ⟨by linarith, hA'⟩
  have h := iterate_movingSum_bound (R * M) N he ((m : ℤ) * R + R - 1)
  push_cast at h
  exact h

theorem outputs_bound (N R M : ℕ) {A A' : ℤ} (hA : 0 ≤ A) (hA' : 0 ≤ A') {xs : List ℤ}
    (hx : ∀ x ∈ xs, -A ≤ x ∧ x ≤ A') :
    ∀ y ∈ outputs N R M xs, -((R * M : ℤ) ^ N * A) ≤ y ∧ y ≤ (R * M : ℤ) ^ N * A' := by
  intro y hy
  simp only [outputs, List.mem_map, List.mem_range] at hy
  obtain ⟨m, -, rfl⟩ := hy
  refine output_bound N R M hA hA' (fun t => ?_) m
  simp only [List.getD_eq_getElem?_getD]
  cases h : xs[t]? with
  | none => exact ⟨by simp; linarith, by simpa using hA'⟩
  | some a => simpa using hx a (List.mem_of_getElem? h)

private theorem toBitVec_ofInt (z : ℤ) : (UInt64.ofInt z).toBitVec = BitVec.ofInt 64 z := by
  apply BitVec.eq_of_toNat_eq
  rw [UInt64.ofInt, UInt64.toBitVec_ofNat', BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  omega

private theorem ofInt_sub (a b : ℤ) : UInt64.ofInt (a - b) = UInt64.ofInt a - UInt64.ofInt b := by
  rw [Int.sub_eq_add_neg, UInt64.ofInt_add, UInt64.ofInt_neg, UInt64.sub_eq_add_neg]

private theorem ofInt_toInt (w : UInt64) : UInt64.ofInt w.toBitVec.toInt = w :=
  UInt64.toBitVec_inj.mp (by rw [toBitVec_ofInt, BitVec.ofInt_toInt])

private theorem toInt_ofInt (z : ℤ) : (UInt64.ofInt z).toBitVec.toInt = z.bmod (2 ^ 64) := by
  rw [toBitVec_ofInt, BitVec.toInt_ofInt]

/-- The word cascade of the residues of an integer input gives the residues of the outputs. -/
theorem cascade_ofInt (N R M : ℕ) (xs : List ℤ) :
    cascade N R M (xs.map UInt64.ofInt) = (outputs N R M xs).map UInt64.ofInt := by
  rw [cascade_map UInt64.ofInt (by decide) UInt64.ofInt_add ofInt_sub, cascade_eq_outputs]

/-- The word cascade gives the residues modulo `2^64` of the outputs of the input words'
readings. -/
theorem cascade_eq_map_ofInt (N R M : ℕ) (ws : List UInt64) :
    cascade N R M ws = (outputs N R M (ws.map fun w => w.toBitVec.toInt)).map UInt64.ofInt := by
  have h : (ws.map fun w => w.toBitVec.toInt).map UInt64.ofInt = ws := by
    rw [List.map_map]
    exact List.map_id'' ofInt_toInt ws
  conv_lhs => rw [← h]
  exact cascade_ofInt N R M _

/-- Each output word of the word cascade reads as its exact output reduced into
`[−2^63, 2^63)`. -/
theorem toInt_cascade (N R M : ℕ) (ws : List UInt64) :
    (cascade N R M ws).map (fun w => w.toBitVec.toInt) =
      (outputs N R M (ws.map fun w => w.toBitVec.toInt)).map (Int.bmod · (2 ^ 64)) := by
  rw [cascade_eq_map_ofInt, List.map_map]
  exact List.map_congr_left fun y _ => toInt_ofInt y

/-- Exactness under the asymmetric bound: if every input word reads in `[−A, A']`,
`(R·M)^N·A ≤ 2^63`, and `(R·M)^N·A' < 2^63`, each output word reads as its exact output. -/
theorem toInt_cascade_of_bound (N R M A A' : ℕ) (ws : List UInt64)
    (hw : ∀ w ∈ ws, -(A : ℤ) ≤ w.toBitVec.toInt ∧ w.toBitVec.toInt ≤ A')
    (hA : (R * M) ^ N * A ≤ 2 ^ 63) (hA' : (R * M) ^ N * A' < 2 ^ 63) :
    (cascade N R M ws).map (fun w => w.toBitVec.toInt) =
      outputs N R M (ws.map fun w => w.toBitVec.toInt) := by
  rw [toInt_cascade]
  refine (List.map_congr_left fun y hy => ?_).trans (List.map_id _)
  have hx : ∀ x ∈ ws.map (fun w => w.toBitVec.toInt), -(A : ℤ) ≤ x ∧ x ≤ A' := by
    intro x hx
    obtain ⟨w, hw', rfl⟩ := List.mem_map.mp hx
    exact hw w hw'
  obtain ⟨h1, h2⟩ := outputs_bound N R M (Int.natCast_nonneg A) (Int.natCast_nonneg A') hx y hy
  have g1 : ((R : ℤ) * M) ^ N * A ≤ 2 ^ 63 := by exact_mod_cast hA
  have g2 : ((R : ℤ) * M) ^ N * A' < 2 ^ 63 := by exact_mod_cast hA'
  show y.bmod (2 ^ 64) = y
  apply Int.bmod_eq_of_le_mul_two <;> omega

/-- Exactness for inputs of `B` bits under Hogenauer's bound: if every input word reads in
`[−2^(B−1), 2^(B−1))` and `(R·M)^N·2^(B−1) ≤ 2^63`, each output word reads as its exact output. -/
theorem toInt_cascade_of_width (N R M B : ℕ) (ws : List UInt64)
    (hw : ∀ w ∈ ws, -2 ^ (B - 1) ≤ w.toBitVec.toInt ∧ w.toBitVec.toInt < 2 ^ (B - 1))
    (hB : (R * M) ^ N * 2 ^ (B - 1) ≤ 2 ^ 63) :
    (cascade N R M ws).map (fun w => w.toBitVec.toInt) =
      outputs N R M (ws.map fun w => w.toBitVec.toInt) := by
  refine toInt_cascade_of_bound N R M (2 ^ (B - 1)) (2 ^ (B - 1) - 1) ws (fun w hw' => ?_) hB ?_
  · obtain ⟨h1, h2⟩ := hw w hw'
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    omega
  · rcases Nat.eq_zero_or_pos ((R * M) ^ N) with h | h
    · rw [h, zero_mul]
      norm_num
    · have h63 : 0 < 2 ^ 63 := by norm_num
      rw [Nat.mul_sub_one]
      omega

-- `N = 1`, `R = 2`: the outputs 2·(2^63 − 1) and 2·(−2^63) wrap to the words 2^64 − 2 and 0.
example :
    cascade 1 2 1 [(0x7FFFFFFFFFFFFFFF : UInt64), 0x7FFFFFFFFFFFFFFF, 0x8000000000000000,
      0x8000000000000000] = [0xFFFFFFFFFFFFFFFE, 0] := by decide

-- `N = 1`, `R = 2`, `B = 63`: the most negative input, −2^62, gives the output −2^63.
example :
    (cascade 1 2 1 [(0xC000000000000000 : UInt64), 0xC000000000000000]).map
      (fun w => w.toBitVec.toInt) = [-9223372036854775808] := by decide

end Library.Numerics.Filters.Cic
