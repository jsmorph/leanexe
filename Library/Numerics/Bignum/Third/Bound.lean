module

public import Library.Numerics.Bignum.Third.Compiled
public import Library.Numerics.Bignum.Third.PrintText
public import Library.Numerics.Bignum.Bound
public import Verified.BoundFacts

@[expose] public section

/-!
The frames and the allocation bounds of the third iteration's module.

Every helper of the division and of the printer updates the one workspace in place, and the
generated bound charges nothing for an update of an owned array, so the bound of `kara`, of the
recursion `rdiv` and its halves, of `udiv`, `divSeg`, `powInit`, and `toChunks` is 0
(`rdiv_bound`, `toChunks_bound`).  A division therefore allocates its workspace of
`3 m + 15 n + 11` words and its two trimmed results, or, below the threshold, what the first
iteration's Algorithm D allocates; a printer allocates its workspace of `31 · 2^K + 2 K + 22`
words, the copy of its `2^(K+1)` chunks, and its text, or, below the threshold, what the first
iteration's printer allocates.  Each closed form is linear in the lengths of the arguments.

`rdiv` recurses on `⌈m/2⌉` and `⌊m/2⌋` quotient limbs and stops below 3, so `rdiv_fits` finds
enough frames for `m ≤ 2^j + 1` with `j + 71` frames, which covers every `m` below `2^64` with 135;
the 71 frames are those of `lowHalf`, `halfStep`, `mulAcc`, `mulChunk`, and `kara`, which needs 66
for every argument.  `toChunks` recurses on its level, which `chunksDC` starts below 40, so it
needs fewer than 180 frames.  Every export's frame condition at 1,000 frames holds for every
argument.
-/

namespace Library.Numerics.Bignum.Third

open Library.Numerics.MultiPrecision
open LeanExe.Dialect (build_size loop_induction)
open Verified (blockCost growCost paidGrowCost creditCost loopCost loopCost_eq_zero loopFits_true
  blockCost_eq growCost_eq)

/-! ## Karatsuba's recursion -/

theorem kara_bound : ∀ (k : ℕ) (x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 ×
    UInt64 × UInt64 × UInt64 × UInt64), compiled.kara.bound k x = 0
  | 0, _ => rfl
  | k + 1, ⟨t, ⟨W⟩, ap, bp, rp, tp, n⟩ => by
    rw [compiled.kara.bound_eq, kara_bound k, kara_bound k, kara_bound k]
    simp

/-- `kara` finds its frames for `n ≤ 13 · 2^k + 2` limbs. -/
theorem kara_fits : ∀ (k : ℕ) (t : UInt64) (W : Array UInt64) (ap bp rp tp n : UInt64),
    n.toNat ≤ 13 * 2 ^ k + 2 → compiled.kara.fits (k + 1) (t, ⟨W⟩, ap, bp, rp, tp, n) = true
  | 0, t, W, ap, bp, rp, tp, n, h => by
    rw [compiled.kara.fits_eq]
    rw [if_pos (by
      simp only [decide_eq_true_eq]
      right; rw [UInt64.lt_iff_toNat_lt]; simp only [UInt64.reduceToNat]; omega)]
  | k + 1, t, W, ap, bp, rp, tp, n, h => by
    rw [compiled.kara.fits_eq]
    split
    · rfl
    · have hn := UInt64.toNat_lt n
      have hh : (n - n / 2).toNat = n.toNat - n.toNat / 2 := by
        rw [UInt64.toNat_sub_of_le _ _ (by
          rw [UInt64.le_iff_toNat_le, UInt64.toNat_div]; simp only [UInt64.reduceToNat]; omega),
          UInt64.toNat_div]; rfl
      have hl : (n / 2).toNat = n.toNat / 2 := by rw [UInt64.toNat_div]; rfl
      have hh1 : (n - n / 2 + 1).toNat = n.toNat - n.toNat / 2 + 1 := by
        rw [toNat_add_lt (by rw [hh]; simp only [UInt64.reduceToNat]; omega), hh]; rfl
      have hp : 13 * 2 ^ (k + 1) = 2 * (13 * 2 ^ k) := by ring
      rw [kara_fits k _ _ _ _ _ _ _ (by rw [hh]; omega),
        kara_fits k _ _ _ _ _ _ _ (by rw [hl]; omega),
        kara_fits k _ _ _ _ _ _ _ (by rw [hh1]; omega)]
      rfl

/-- `kara` finds its frames for every argument with 66 frames. -/
theorem kara_fits_all (k : ℕ) (hk : 66 ≤ k) (x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64) : compiled.kara.fits k x = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨t, ⟨W⟩, ap, bp, rp, tp, n⟩ := x
  apply kara_fits
  have h1 := UInt64.toNat_lt n
  have h2 : 2 ^ 64 ≤ 2 ^ k' := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-! ## The bounds of the helpers in place -/

theorem mulChunk_bound : ∀ (k : ℕ) (x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64), compiled.mulChunk.bound k x = 0
  | 0, _ => rfl
  | k + 1, ⟨t, ⟨W⟩, bp, k1, ql, c, ac, qc, j⟩ => by
    rw [compiled.mulChunk.bound_eq, kara_bound]

theorem mulAcc_bound : ∀ (k : ℕ) (x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64), compiled.mulAcc.bound k x = 0
  | 0, _ => rfl
  | k + 1, ⟨t, ⟨W⟩, bp, k1, qp, ql, c, sp⟩ => by
    rw [compiled.mulAcc.bound_eq]
    exact loopCost_eq_zero (fun _ => rfl) (fun _ _ => mulChunk_bound k _) _ _ _

theorem halfStep_bound : ∀ (k : ℕ) (x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64),
    compiled.halfStep.bound k x = 0
  | 0, _ => rfl
  | k + 1, ⟨t, ⟨W⟩, rp, bp, n, k1, qp, ql, c, sp⟩ => by
    rw [compiled.halfStep.bound_eq, mulAcc_bound]

theorem lowHalf_bound : ∀ (k : ℕ) (x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64),
    compiled.lowHalf.bound k x = 0
  | 0, _ => rfl
  | k + 1, ⟨t, ⟨W⟩, ap, bp, n, qp, sp, m, c1, c0⟩ => by
    rw [compiled.lowHalf.bound_eq, halfStep_bound]

theorem rdiv_bound : ∀ (k : ℕ) (x : UInt64 × UInt64 × LeanExe.Pipeline.Moved (Array UInt64) ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64), compiled.rdiv.bound k x = 0
  | 0, _ => rfl
  | k + 1, ⟨t, T, ⟨W⟩, ap, bp, qp, sp, n, m⟩ => by
    rw [compiled.rdiv.bound_eq]
    simp only [rdiv_bound k, halfStep_bound k, lowHalf_bound k, Nat.add_zero, ite_self]

theorem tdiv_bound : ∀ (k : ℕ) (x : UInt64 × UInt64 × LeanExe.Pipeline.Moved (Array UInt64) ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64), compiled.tdiv.bound k x = 0
  | 0, _ => rfl
  | k + 1, ⟨t, T, ⟨W⟩, ap, bp, qp, sp, n, m⟩ => by
    rw [compiled.tdiv.bound_eq, rdiv_bound, halfStep_bound]

theorem udiv_bound : ∀ (k : ℕ) (x : UInt64 × UInt64 × LeanExe.Pipeline.Moved (Array UInt64) ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64), compiled.udiv.bound k x = 0
  | 0, _ => rfl
  | k + 1, ⟨t, T, ⟨W⟩, ap, bp, qp, sp, n, M⟩ => by
    rw [compiled.udiv.bound_eq, loopCost_eq_zero (fun _ => rfl) (fun _ _ => rdiv_bound k _)]
    simp only [rdiv_bound k, tdiv_bound k, Nat.zero_add, ite_self]

theorem divSeg_bound : ∀ (k : ℕ) (x : UInt64 × UInt64 × LeanExe.Pipeline.Moved (Array UInt64) ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64), compiled.divSeg.bound k x = 0
  | 0, _ => rfl
  | k + 1, ⟨t, T, ⟨W⟩, xp, lx, dp, n, qp, sp⟩ => by
    rw [compiled.divSeg.bound_eq, udiv_bound]

theorem powInit_bound : ∀ (k : ℕ) (x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 ×
    UInt64 × UInt64), compiled.powInit.bound k x = 0
  | 0, _ => rfl
  | k + 1, ⟨t, ⟨W⟩, tb, pb, K⟩ => by
    rw [compiled.powInit.bound_eq]
    exact loopCost_eq_zero (fun _ => rfl) (fun _ _ => kara_bound k _) _ _ _

theorem toChunks_bound : ∀ (k : ℕ) (x : UInt64 × UInt64 × UInt64 ×
    LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 × UInt64),
    compiled.toChunks.bound k x = 0
  | 0, _ => rfl
  | k + 1, ⟨t, T, L, ⟨W⟩, tb, i, p, cp, fp⟩ => by
    rw [compiled.toChunks.bound_eq]
    simp only [toChunks_bound k, divSeg_bound k, Nat.add_zero, ite_self]

/-! ## Frames of the division -/

theorem mulChunk_fits (k : ℕ) (hk : 67 ≤ k) (x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :
    compiled.mulChunk.fits k x = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨t, ⟨W⟩, bp, k1, ql, c, ac, qc, j⟩ := x
  rw [compiled.mulChunk.fits_eq]
  exact kara_fits_all k' (by omega) _

theorem mulAcc_fits (k : ℕ) (hk : 68 ≤ k) (x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :
    compiled.mulAcc.fits k x = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨t, ⟨W⟩, bp, k1, qp, ql, c, sp⟩ := x
  rw [compiled.mulAcc.fits_eq]
  exact loopFits_true (fun _ => rfl) (fun _ _ => mulChunk_fits k' (by omega) _) _ _ _

theorem halfStep_fits (k : ℕ) (hk : 69 ≤ k) (x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :
    compiled.halfStep.fits k x = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨t, ⟨W⟩, rp, bp, n, k1, qp, ql, c, sp⟩ := x
  rw [compiled.halfStep.fits_eq]
  exact mulAcc_fits k' (by omega) _

theorem lowHalf_fits (k : ℕ) (hk : 70 ≤ k) (x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :
    compiled.lowHalf.fits k x = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨t, ⟨W⟩, ap, bp, n, qp, sp, m, c1, c0⟩ := x
  rw [compiled.lowHalf.fits_eq]
  exact halfStep_fits k' (by omega) _

/-- `rdiv` finds its frames for `m ≤ 2^j + 1` quotient limbs with `j + 71` frames. -/
theorem rdiv_fits : ∀ (j k : ℕ), j + 71 ≤ k → ∀ (t T : UInt64) (W : Array UInt64)
    (ap bp qp sp n m : UInt64), m.toNat ≤ 2 ^ j + 1 →
    compiled.rdiv.fits k (t, T, ⟨W⟩, ap, bp, qp, sp, n, m) = true
  | 0, k, hk, t, T, W, ap, bp, qp, sp, n, m, hm => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [compiled.rdiv.fits_eq, if_pos (by
      simp only [decide_eq_true_eq]
      right; rw [UInt64.lt_iff_toNat_lt]; simp only [UInt64.reduceToNat]; simp at hm; omega)]
  | j + 1, k, hk, t, T, W, ap, bp, qp, sp, n, m, hm => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [compiled.rdiv.fits_eq]
    split
    · rfl
    · have hn := UInt64.toNat_lt m
      have hh : (m - m / 2).toNat = m.toNat - m.toNat / 2 := by
        rw [UInt64.toNat_sub_of_le _ _ (by
          rw [UInt64.le_iff_toNat_le, UInt64.toNat_div]; simp only [UInt64.reduceToNat]; omega),
          UInt64.toNat_div]; rfl
      have hl : (m / 2).toNat = m.toNat / 2 := by rw [UInt64.toNat_div]; rfl
      have hp : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
      simp only [Bool.and_eq_true]
      exact ⟨rdiv_fits j k' (by omega) _ _ _ _ _ _ _ _ _ (by rw [hh]; omega),
        halfStep_fits k' (by omega) _,
        rdiv_fits j k' (by omega) _ _ _ _ _ _ _ _ _ (by rw [hl]; omega),
        lowHalf_fits k' (by omega) _⟩

/-- `rdiv` finds its frames for every argument with 135 frames. -/
theorem rdiv_fits_all (k : ℕ) (hk : 135 ≤ k) (x : UInt64 × UInt64 ×
    LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :
    compiled.rdiv.fits k x = true := by
  obtain ⟨t, T, ⟨W⟩, ap, bp, qp, sp, n, m⟩ := x
  apply rdiv_fits 64 k (by omega)
  have := UInt64.toNat_lt m
  omega

theorem tdiv_fits (k : ℕ) (hk : 136 ≤ k) (x : UInt64 × UInt64 ×
    LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :
    compiled.tdiv.fits k x = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨t, T, ⟨W⟩, ap, bp, qp, sp, n, m⟩ := x
  rw [compiled.tdiv.fits_eq, rdiv_fits_all k' (by omega), halfStep_fits k' (by omega)]
  rfl

theorem udiv_fits (k : ℕ) (hk : 137 ≤ k) (x : UInt64 × UInt64 ×
    LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :
    compiled.udiv.fits k x = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨t, T, ⟨W⟩, ap, bp, qp, sp, n, M⟩ := x
  rw [compiled.udiv.fits_eq, loopFits_true (fun _ => rfl) (fun _ _ => rdiv_fits_all k' (by omega) _),
    Bool.true_and]
  split
  · exact rdiv_fits_all k' (by omega) _
  · exact tdiv_fits k' (by omega) _

theorem divSeg_fits (k : ℕ) (hk : 138 ≤ k) (x : UInt64 × UInt64 ×
    LeanExe.Pipeline.Moved (Array UInt64) × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :
    compiled.divSeg.fits k x = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨t, T, ⟨W⟩, xp, lx, dp, n, qp, sp⟩ := x
  rw [compiled.divSeg.fits_eq]
  exact udiv_fits k' (by omega) _

theorem natDivModCheckedBZWith_fits (k : ℕ) (hk : 139 ≤ k)
    (x : UInt64 × UInt64 × UInt64 × Array UInt64 × Array UInt64) :
    compiled.natDivModCheckedBZWith.fits k x = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨t, T, D, u, v⟩ := x
  rw [compiled.natDivModCheckedBZWith.fits_eq]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · exact divSeg_fits k' (by omega) _

theorem natDivModCheckedBZ_fits (k : ℕ) (hk : 140 ≤ k) (x : Array UInt64 × Array UInt64) :
    compiled.natDivModCheckedBZ.fits k x = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨u, v⟩ := x
  rw [compiled.natDivModCheckedBZ.fits_eq]
  exact natDivModCheckedBZWith_fits k' (by omega) _

theorem intTDivModCheckedBZ_fits (k : ℕ) (hk : 141 ≤ k) (x : BigInt × BigInt) :
    compiled.intTDivModCheckedBZ.fits k x = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨a, b⟩ := x
  rw [compiled.intTDivModCheckedBZ.fits_eq]
  split
  · rfl
  · exact natDivModCheckedBZ_fits k' (by omega) _

theorem intEDivModCheckedBZ_fits (k : ℕ) (hk : 141 ≤ k) (x : BigInt × BigInt) :
    compiled.intEDivModCheckedBZ.fits k x = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨a, b⟩ := x
  rw [compiled.intEDivModCheckedBZ.fits_eq]
  split
  · rfl
  · exact natDivModCheckedBZ_fits k' (by omega) _

/-! ## Frames of the printer -/

theorem powInit_fits (k : ℕ) (hk : 67 ≤ k) (x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) ×
    UInt64 × UInt64 × UInt64) : compiled.powInit.fits k x = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨t, ⟨W⟩, tb, pb, K⟩ := x
  rw [compiled.powInit.fits_eq]
  exact loopFits_true (fun _ => rfl) (fun _ _ => kara_fits_all k' (by omega) _) _ _ _

/-- `toChunks` finds its frames at level `i` with `i + 139` frames. -/
theorem toChunks_fits : ∀ (i k : ℕ), i + 139 ≤ k → ∀ (t T L : UInt64) (W : Array UInt64)
    (tb ii p cp fp : UInt64), ii.toNat = i →
    compiled.toChunks.fits k (t, T, L, ⟨W⟩, tb, ii, p, cp, fp) = true
  | 0, k, hk, t, T, L, W, tb, ii, p, cp, fp, hi => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have h0 : ii = 0 := UInt64.toNat_inj.mp (by rw [hi]; rfl)
    rw [compiled.toChunks.fits_eq, if_pos (by simp [h0])]
  | i + 1, k, hk, t, T, L, W, tb, ii, p, cp, fp, hi => by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hii : (ii - 1).toNat = i := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hi]; simp), hi]; simp
    rw [compiled.toChunks.fits_eq]
    split
    · rfl
    · split
      · exact toChunks_fits i k' (by omega) _ _ _ _ _ _ _ _ _ hii
      · simp only [Bool.and_eq_true]
        exact ⟨divSeg_fits k' (by omega) _,
          toChunks_fits i k' (by omega) _ _ _ _ _ _ _ _ _ hii,
          toChunks_fits i k' (by omega) _ _ _ _ _ _ _ _ _ hii⟩

/-- The count of levels is at most 40 for every count of chunks. -/
theorem levelsFor_le (c : UInt64) : (levelsFor c).toNat ≤ 40 := by
  unfold levelsFor LeanExe.repeatWhile
  suffices h : ∀ (f : ℕ) (s : UInt64), s.toNat + f ≤ 40 →
      (LeanExe.repeatWhile.go (fun k => decide ((2 : UInt64) <<< k < c)) (fun k => k + 1) f
        s).toNat ≤ 40 from h _ 0 (by simp)
  intro f
  induction f with
  | zero => intro s hs; simpa [LeanExe.repeatWhile.go] using hs
  | succ f ih =>
    intro s hs
    simp only [LeanExe.repeatWhile.go]
    split
    · exact ih _ (by
        rw [toNat_add_lt (by simp only [UInt64.reduceToNat]; omega)]
        simp only [UInt64.reduceToNat]; omega)
    · omega

theorem chunksDC_fits (k : ℕ) (hk : 180 ≤ k) (x : UInt64 × UInt64 × UInt64 × Array UInt64) :
    compiled.chunksDC.fits k x = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨t, T, L, u⟩ := x
  rw [compiled.chunksDC.fits_eq, powInit_fits k' (by omega),
    toChunks_fits _ k' (by have := levelsFor_le (u.size.toUInt64 + u.size.toUInt64 / 14 + 2); omega)
      _ _ _ _ _ _ _ _ _ rfl]
  rfl

theorem natToTextDCWith_fits (k : ℕ) (hk : 181 ≤ k)
    (x : UInt64 × UInt64 × UInt64 × UInt64 × Array UInt64) :
    compiled.natToTextDCWith.fits k x = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨t, T, L, P, u⟩ := x
  rw [compiled.natToTextDCWith.fits_eq]
  split
  · rfl
  · exact chunksDC_fits k' (by omega) _

theorem natToTextDC_fits (k : ℕ) (hk : 182 ≤ k) (u : Array UInt64) :
    compiled.natToTextDC.fits k u = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [compiled.natToTextDC.fits_eq]
  exact natToTextDCWith_fits k' (by omega) _

theorem intToTextDC_fits (k : ℕ) (hk : 181 ≤ k) (x : BigInt) :
    compiled.intToTextDC.fits k x = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [compiled.intToTextDC.fits_eq]
  split
  · rfl
  · exact chunksDC_fits k' (by omega) _

/-! ## Closed forms of the reused functions

The copies of the first iteration's proofs for this module's `compiled`. -/

theorem add_bound_le (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.add.bound (u, v) ≤ 96 * max u.size v.size + 168 := by
  rw [compiled.add.bound_eq]
  have hw := width_toNat (u := u) (v := v) (by omega) (by omega)
  have hs := loop_push_size2 (width u v) ((0 : UInt64), (#[] : Array UInt64))
    (fun j s => ((u[j.toNat]! + v[j.toNat]! + s.1) / 4294967296,
      s.2.push ((u[j.toNat]! + v[j.toNat]! + s.1) % 4294967296))) (fun _ _ => by simp)
  rw [hs]
  refine le_trans (Nat.add_le_add_right (min_le_right _ _) _) ?_
  rw [Verified.loopCost_const, hw, Verified.blockCost_eq, Verified.growCost_eq, Verified.paidGrowCost_eq]
  simp [Verified.creditCost]
  omega

theorem sub_bound_le (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.sub.bound (u, v) ≤ 80 * max u.size v.size + 72 := by
  rw [compiled.sub.bound_eq]
  have hw := width_toNat (u := u) (v := v) (by omega) (by omega)
  refine le_trans (min_le_right _ _) ?_
  rw [Verified.loopCost_const, hw, Verified.blockCost_eq, Verified.paidGrowCost_eq]
  simp [Verified.creditCost]
  omega

theorem mulSmall_bound_le (a : Array UInt64) (m c : UInt64) (ha : a.size < 2 ^ 32) :
    compiled.mulSmall.bound (a, m, c) ≤ 96 * a.size + 168 := by
  rw [compiled.mulSmall.bound_eq]
  have hs := loop_push_size1 a.size.toUInt64 (LeanExe.build 0 fun _ => (0 : UInt64), c)
    (fun i (s : Array UInt64 × UInt64) =>
      have t := a[i.toNat]! * m + s.2
      (s.1.push (t &&& 4294967295), t >>> 32)) (fun _ _ => by simp)
  rw [hs, build_size]
  refine le_trans (Nat.add_le_add_right (min_le_right _ _) _) ?_
  rw [Verified.loopCost_const, toNat_size ha, Verified.blockCost_eq, Verified.growCost_eq,
    Verified.paidGrowCost_eq]
  simp [Verified.creditCost]
  omega

theorem shortDiv_bound_le (x : Array UInt64) (d len : UInt64) :
    compiled.shortDiv.bound (x, d, len) ≤ 24 * len.toNat + 152 := by
  rw [compiled.shortDiv.bound_eq]
  rw [loop_keep_size2 len _ _ (fun _ _ => by simp), build_size, Verified.blockCost_eq,
    Verified.growCost_eq]
  omega

theorem longDivS_bound_le (u v : Array UInt64) (t : UInt64) (hu : u.size < 2 ^ 32)
    (hv : v.size < 2 ^ 32) :
    compiled.longDivS.bound (u, v, t) ≤ 112 * u.size + 104 * v.size + 24 * t.toNat + 600 := by
  rw [compiled.longDivS.bound_eq]
  have h1 := mulSmall_bound_le v
    (1 <<< (32 - Library.Numerics.Arithmetic.Uscale.wordBits v[(t - 1).toNat]!)) 0 hv
  have h2 := mulSmall_bound_le u
    (1 <<< (32 - Library.Numerics.Arithmetic.Uscale.wordBits v[(t - 1).toNat]!)) 0 hu
  have h4 : (u.size.toUInt64 + v.size.toUInt64).toNat = u.size + v.size := by
    rw [UInt64.toNat_add, toNat_size hu, toNat_size hv]; omega
  rw [h4, toNat_size hu, Verified.blockCost_eq, Verified.blockCost_eq]
  refine le_trans (Nat.add_le_add h1 (Nat.add_le_add (Nat.add_le_add_left h2 _)
    (Nat.add_le_add_right (shortDiv_bound_le _ _ _) _))) ?_
  omega

theorem divideS_bound_le (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.divideS.bound (u, v) ≤ 112 * u.size + 128 * v.size + 600 := by
  rw [compiled.divideS.bound_eq]
  have h4 : (u.size.toUInt64 + v.size.toUInt64).toNat = u.size + v.size := by
    rw [UInt64.toNat_add, toNat_size hu, toNat_size hv]; omega
  split
  · rw [h4, Verified.blockCost_eq]; omega
  · split
    · have := shortDiv_bound_le u v[UInt64.toNat 0]! u.size.toUInt64
      rw [toNat_size hu] at this
      rw [h4, Verified.blockCost_eq]; omega
    · have := longDivS_bound_le u v (significant v) hu hv
      have := (significant_spec v (by omega)).1
      omega

theorem natTrim_bound_le (u : Array UInt64) (hu : u.size < 2 ^ 64) :
    compiled.natTrim.bound u ≤ 8 * u.size + 56 := by
  rw [compiled.natTrim.bound_eq, Verified.blockCost_eq]
  have := (significant_spec u (by omega)).1
  omega

theorem natAdd_bound_le (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.natAdd.bound (u, v) ≤ 104 * max u.size v.size + 232 := by
  rw [compiled.natAdd.bound_eq]
  have h1 := add_bound_le u v hu hv
  have h2 := natTrim_bound_le (add u v) (by rw [add_size u v hu hv]; omega)
  rw [add_size u v hu hv] at h2
  omega

theorem natSub_bound_le (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.natSub.bound (u, v) ≤ 88 * max u.size v.size + 128 := by
  rw [compiled.natSub.bound_eq]
  split
  · have h1 := sub_bound_le u v hu hv
    have h2 := natTrim_bound_le (sub u v) (by rw [sub_size u v hu hv]; omega)
    rw [sub_size u v hu hv] at h2
    omega
  · have h1 := sub_bound_le v u hv hu
    have h2 := natTrim_bound_le (sub v u) (by rw [sub_size v u hv hu]; omega)
    rw [sub_size v u hv hu] at h2
    omega

/-- The cost of Algorithm D with its trimmed results, for a divisor that is not empty. -/
theorem divCostS_le (u v : Array UInt64) (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.divideS.bound (u, v) +
        (blockCost u.size.toUInt64.toNat +
            compiled.natTrim.bound (slice (divideS u v) 0 u.size.toUInt64) +
          (blockCost v.size.toUInt64.toNat +
            compiled.natTrim.bound (slice (divideS u v) u.size.toUInt64 v.size.toUInt64))) ≤
      128 * u.size + 144 * v.size + 824 := by
  have h1 := divideS_bound_le u v hu hv
  have h2 := natTrim_bound_le (slice (divideS u v) 0 u.size.toUInt64)
    (by rw [slice_size, toNat_size hu]; omega)
  have h3 := natTrim_bound_le (slice (divideS u v) u.size.toUInt64 v.size.toUInt64)
    (by rw [slice_size, toNat_size hv]; omega)
  rw [slice_size, toNat_size hu] at h2
  rw [slice_size, toNat_size hv] at h3
  rw [toNat_size hu, toNat_size hv, Verified.blockCost_eq, Verified.blockCost_eq]
  omega

/-! ## Closed forms of the division -/

/-- The count of the significant words of a segment is at most its length. -/
theorem trimCount_le (W : Array UInt64) (p len : UInt64) :
    (LeanExe.loop len (0 : UInt64) fun i k => if W[(p + i).toNat]! = 0 then k else i + 1).toNat ≤
      len.toNat :=
  loop_induction (n := len) (init := (0 : UInt64))
    (f := fun i k => if W[(p + i).toNat]! = 0 then k else i + 1)
    (fun j (k : UInt64) => k.toNat ≤ j) (Nat.zero_le _) (by
      intro j k hj hk
      split
      · omega
      · rw [toNat_add_lt (by
          rw [toNat_ofNat_lt (by have := len.toNat_lt; omega)]; simp only [UInt64.reduceToNat]
          have := len.toNat_lt; omega), toNat_ofNat_lt (by have := len.toNat_lt; omega)]
        simp only [UInt64.reduceToNat]; omega)

/-- The trimmed copy of `len` words allocates at most `len` words. -/
theorem trimSeg_bound_le (W : Array UInt64) (p len : UInt64) :
    compiled.trimSeg.bound (W, p, len) ≤ 8 * len.toNat + 56 := by
  rw [compiled.trimSeg.bound_eq, blockCost_eq]
  have := trimCount_le W p len
  omega

theorem trimSeg_size_le (W : Array UInt64) (p len : UInt64) :
    (trimSeg W p len).size ≤ len.toNat := by
  unfold trimSeg
  rw [build_size]
  exact trimCount_le W p len

/-- The quotient of the division is at most as long as the dividend and the remainder at most as
long as the divisor. -/
theorem natDivModBZWith_size (t T D : UInt64) (u v : Array UInt64) (hu : u.size < 2 ^ 32)
    (hv : v.size < 2 ^ 32) (hv0 : v.size ≠ 0) :
    (natDivModBZWith t T D u v).1.size ≤ u.size ∧ (natDivModBZWith t T D u v).2.size ≤ v.size := by
  have hmu := toNat_size hu
  have hmv := toNat_size hv
  unfold natDivModBZWith
  dsimp only
  split
  · rename_i hlt
    rw [UInt64.lt_iff_toNat_lt, hmu, hmv] at hlt
    have := (significant_spec u (by omega)).1
    refine ⟨by simp, ?_⟩
    rw [natTrim_size]; omega
  · split
    · unfold natDivModS
      rw [size_toUInt64_beq_zero (by omega), decide_eq_false hv0, ite_eq_right (by decide)]
      dsimp only
      rw [natTrim_size, natTrim_size]
      have h1 := (significant_spec (slice (divideS u v) 0 u.size.toUInt64) (by
        rw [slice_size, hmu]; omega)).1
      have h2 := (significant_spec (slice (divideS u v) u.size.toUInt64 v.size.toUInt64) (by
        rw [slice_size, hmv]; omega)).1
      rw [slice_size, hmu] at h1
      rw [slice_size, hmv] at h2
      exact ⟨h1, h2⟩
    · rename_i hlt hs
      rw [UInt64.lt_iff_toNat_lt, hmu, hmv] at hlt
      simp only [decide_eq_true_eq, not_or, UInt64.not_lt, UInt64.le_iff_toNat_le, hmv,
        UInt64.reduceToNat] at hs
      refine ⟨le_trans (trimSeg_size_le _ _ _) ?_, le_trans (trimSeg_size_le _ _ _) (by omega)⟩
      rw [UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, toNat_add_lt (by simp only [hmu, UInt64.reduceToNat]; omega)]
        simp only [hmu, hmv, UInt64.reduceToNat]; omega),
        toNat_add_lt (by simp only [hmu, UInt64.reduceToNat]; omega)]
      simp only [hmu, hmv, UInt64.reduceToNat]
      omega

/-- The natural division allocates at most `128 m + 144 n + 824` bytes for operands of `m` and
`n` limbs, at every threshold: the first iteration's bound, which Algorithm D below the threshold
attains, and above it `32 m + 120 n + 264` for the workspace and the two results. -/
theorem natDivModCheckedBZWith_bound_le (k : ℕ) (t T D : UInt64) (u v : Array UInt64)
    (hu : u.size < 2 ^ 32) (hv : v.size < 2 ^ 32) :
    compiled.natDivModCheckedBZWith.bound (k + 1) (t, T, D, u, v) ≤
      128 * u.size + 144 * v.size + 824 := by
  have hmu := toNat_size hu
  have hmv := toNat_size hv
  rw [compiled.natDivModCheckedBZWith.bound_eq]
  split
  · rw [show UInt64.toNat 0 = 0 from rfl, blockCost_eq]; omega
  · split
    · have := natTrim_bound_le u (by omega)
      rw [show UInt64.toNat 0 = 0 from rfl, blockCost_eq]; omega
    · split
      · exact divCostS_le u v hu hv
      · rename_i h0 hlt hs
        rw [UInt64.lt_iff_toNat_lt, hmu, hmv] at hlt
        simp only [divSeg_bound, Nat.zero_add]
        refine le_trans (Nat.add_le_add_left
          (Nat.add_le_add (trimSeg_bound_le _ _ _) (trimSeg_bound_le _ _ _)) _) ?_
        have h3 : (3 * u.size.toUInt64 + 15 * v.size.toUInt64 + 11).toNat =
            3 * u.size + 15 * v.size + 11 := by
          simp only [UInt64.toNat_add, UInt64.toNat_mul, hmu, hmv, UInt64.reduceToNat]; omega
        have h4 : (u.size.toUInt64 + 1 - v.size.toUInt64).toNat ≤ u.size + 1 := by
          rw [UInt64.toNat_sub_of_le _ _ (by
            rw [UInt64.le_iff_toNat_le, toNat_add_lt (by simp only [hmu, UInt64.reduceToNat]; omega)]
            simp only [hmu, hmv, UInt64.reduceToNat]; omega),
            toNat_add_lt (by simp only [hmu, UInt64.reduceToNat]; omega)]
          simp only [hmu, UInt64.reduceToNat]
          omega
        rw [blockCost_eq, h3, hmv]
        omega

theorem natDivModCheckedBZ_bound_le (k : ℕ) (u v : Array UInt64) (hu : u.size < 2 ^ 32)
    (hv : v.size < 2 ^ 32) :
    compiled.natDivModCheckedBZ.bound (k + 2) (u, v) ≤ 128 * u.size + 144 * v.size + 824 := by
  rw [compiled.natDivModCheckedBZ.bound_eq]; exact natDivModCheckedBZWith_bound_le k _ _ _ u v hu hv

theorem intTDivModCheckedBZ_bound_le (k : ℕ) (x y : BigInt) (hx : x.mag.size < 2 ^ 32)
    (hy : y.mag.size < 2 ^ 32) :
    compiled.intTDivModCheckedBZ.bound (k + 3) (x, y) ≤
      128 * x.mag.size + 144 * y.mag.size + 824 := by
  rw [compiled.intTDivModCheckedBZ.bound_eq]
  split
  · rw [show UInt64.toNat 0 = 0 from rfl, blockCost_eq]; omega
  · exact natDivModCheckedBZ_bound_le k _ _ hx hy

/-- The Euclidean division adds to the natural division the moves of its two results and, for a
negative dividend with a remainder, the successor of the quotient and the difference of the
divisor and the remainder. -/
theorem intEDivModCheckedBZ_bound_le (k : ℕ) (x y : BigInt) (hx : x.mag.size < 2 ^ 32)
    (hy : y.mag.size < 2 ^ 32) :
    compiled.intEDivModCheckedBZ.bound (k + 3) (x, y) ≤
      248 * x.mag.size + 248 * y.mag.size + 1472 := by
  rw [compiled.intEDivModCheckedBZ.bound_eq]
  split
  · rw [show UInt64.toNat 0 = 0 from rfl, blockCost_eq]; omega
  · rename_i hy0
    have hy0' : y.mag.size ≠ 0 := by
      rw [size_toUInt64_beq_zero (by omega)] at hy0; simpa using hy0
    have h1 := natDivModCheckedBZ_bound_le k x.mag y.mag hx hy
    have hqr : natDivModCheckedBZ x.mag y.mag =
        (0, (natDivModBZWith karaThreshold divBase divThreshold x.mag y.mag).1,
          (natDivModBZWith karaThreshold divBase divThreshold x.mag y.mag).2) := by
      unfold natDivModCheckedBZ natDivModCheckedBZWith; rw [if_neg hy0]
    obtain ⟨s1, s2⟩ := natDivModBZWith_size karaThreshold divBase divThreshold x.mag y.mag hx hy hy0'
    have hq : (natDivModCheckedBZ x.mag y.mag).2.1.size ≤ x.mag.size := by rw [hqr]; exact s1
    have hr : (natDivModCheckedBZ x.mag y.mag).2.2.size ≤ y.mag.size := by rw [hqr]; exact s2
    generalize (natDivModCheckedBZ x.mag y.mag).2.1 = q at hq ⊢
    generalize (natDivModCheckedBZ x.mag y.mag).2.2 = r at hr ⊢
    refine le_trans (Nat.add_le_add_right h1 _) ?_
    rw [compiled.signEDiv.cost_eq]
    simp only [Verified.creditCost]
    split
    · have h2 := natAdd_bound_le q #[1] (by omega) (by simp)
      have h3 := natSub_bound_le y.mag r hy (by omega)
      rw [show UInt64.toNat 0 = 0 from rfl, blockCost_eq, growCost_eq]
      have h1s : (#[1] : Array UInt64).size = 1 := rfl
      have h0s : ({ toList := [] } : Array UInt64).size = 0 := rfl
      rw [h1s] at h2
      rw [h0s]
      have : max q.size 1 ≤ x.mag.size + 1 := by omega
      have : max y.mag.size r.size = y.mag.size := by omega
      omega
    · omega

/-! ## Closed forms of the printer -/

theorem chunks_size (m : Array UInt64) (K : UInt64) : (chunks m K).size = K.toNat := by
  unfold chunks
  rw [loop_keep_size2 _ _ _ (fun _ _ => by simp), build_size]

/-- The first iteration's printer allocates at most `94 n + 424` bytes for `n` limbs. -/
theorem intToText_bound_le (x : BigInt) (hs : x.mag.size < 2 ^ 32) :
    compiled.intToText.bound x ≤ 94 * x.mag.size + 424 := by
  rw [compiled.intToText.bound_eq]
  have hK : (x.mag.size.toUInt64 + x.mag.size.toUInt64 / 14 + 2).toNat =
      x.mag.size + x.mag.size / 14 + 2 := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_div, toNat_size hs]
    simp only [UInt64.reduceToNat]
    omega
  generalize hKd : x.mag.size.toUInt64 + x.mag.size.toUInt64 / 14 + 2 = K at hK ⊢
  have hcs := chunks_size x.mag K
  generalize chunks x.mag K = c at hcs ⊢
  have hsc := (significant_spec c (by omega)).1
  generalize significant c = sc at hsc ⊢
  have hT : (if (sc == 0) = true then (0 : UInt64) else sc - 1).toNat + 1 ≤ K.toNat := by
    by_cases h0 : sc = 0
    · rw [ite_eq_left (by simp [h0])]; simp; omega
    · rw [ite_eq_right (by simpa using h0), UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le]
        have : sc.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
        simp; omega)]
      simp; omega
  generalize (if (sc == 0) = true then (0 : UInt64) else sc - 1) = t at hT ⊢
  have hdc : (Library.Numerics.Decimal.Int64Text.digitCount c[t.toNat]!).toNat ≤ 20 := by
    rw [Library.Numerics.Decimal.Int64Text.digitCount_toNat]
    exact Library.Numerics.Decimal.Int64Text.digitWords_length_le _ (UInt64.toNat_lt _)
  have hS : (if x.neg = true then (1 : UInt64) else 0).toNat ≤ 1 := by split <;> simp
  have hlen : ((if x.neg = true then (1 : UInt64) else 0) +
      Library.Numerics.Decimal.Int64Text.digitCount c[t.toNat]! + 9 * t).toNat ≤
      1 + 20 + 9 * t.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul]
    simp only [UInt64.reduceToNat]
    have h1 := Nat.mod_le (9 * t.toNat) (2 ^ 64)
    have h2 := Nat.mod_le ((if x.neg = true then (1 : UInt64) else 0).toNat +
      (Library.Numerics.Decimal.Int64Text.digitCount c[t.toNat]!).toNat) (2 ^ 64)
    have h3 := Nat.mod_le (((if x.neg = true then (1 : UInt64) else 0).toNat +
      (Library.Numerics.Decimal.Int64Text.digitCount c[t.toNat]!).toNat) % 2 ^ 64 +
      9 * t.toNat % 2 ^ 64) (2 ^ 64)
    omega
  rw [Verified.blockCost_eq, Verified.blockCost_eq, Verified.blockCost_eq, toNat_size hs, hK]
  omega

/-- The text of `K` chunks allocates at most `80 K + 280` bytes: the copy of the chunks and at
most `21 + 9 K` bytes of text. -/
theorem textOfChunks_bound_le (neg : Bool) (W : Array UInt64) (cp K : UInt64) :
    compiled.textOfChunks.bound (neg, W, cp, K) ≤ 80 * K.toNat + 280 := by
  rw [compiled.textOfChunks.bound_eq]
  have hcs : (LeanExe.build K fun i => W[(cp + i).toNat]!).size = K.toNat := build_size _ _
  generalize LeanExe.build K (fun i => W[(cp + i).toNat]!) = c at hcs ⊢
  have hsc := (significant_spec c (by have := K.toNat_lt; omega)).1
  generalize significant c = sc at hsc ⊢
  have hT : (if (sc == 0) = true then (0 : UInt64) else sc - 1).toNat ≤ K.toNat := by
    by_cases h0 : sc = 0
    · rw [ite_eq_left (by simp [h0])]; simp
    · rw [ite_eq_right (by simpa using h0), UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le]
        have : sc.toNat ≠ 0 := fun e => h0 (UInt64.toNat_inj.mp (by rw [e]; rfl))
        simp; omega)]
      simp; omega
  generalize (if (sc == 0) = true then (0 : UInt64) else sc - 1) = t at hT ⊢
  have hdc : (Library.Numerics.Decimal.Int64Text.digitCount c[t.toNat]!).toNat ≤ 20 := by
    rw [Library.Numerics.Decimal.Int64Text.digitCount_toNat]
    exact Library.Numerics.Decimal.Int64Text.digitWords_length_le _ (UInt64.toNat_lt _)
  have hS : (if neg = true then (1 : UInt64) else 0).toNat ≤ 1 := by split <;> simp
  have hlen : ((if neg = true then (1 : UInt64) else 0) +
      Library.Numerics.Decimal.Int64Text.digitCount c[t.toNat]! + 9 * t).toNat ≤
      1 + 20 + 9 * t.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul]
    simp only [UInt64.reduceToNat]
    have h1 := Nat.mod_le (9 * t.toNat) (2 ^ 64)
    have h2 := Nat.mod_le ((if neg = true then (1 : UInt64) else 0).toNat +
      (Library.Numerics.Decimal.Int64Text.digitCount c[t.toNat]!).toNat) (2 ^ 64)
    have h3 := Nat.mod_le (((if neg = true then (1 : UInt64) else 0).toNat +
      (Library.Numerics.Decimal.Int64Text.digitCount c[t.toNat]!).toNat) % 2 ^ 64 +
      9 * t.toNat % 2 ^ 64) (2 ^ 64)
    omega
  rw [Verified.blockCost_eq, Verified.blockCost_eq]
  omega

/-- The count of chunks `c = n + ⌊n/14⌋ + 2` of `n` limbs as a word. -/
theorem chunkCount_toNat {u : Array UInt64} (hs : u.size < 2 ^ 32) :
    (u.size.toUInt64 + u.size.toUInt64 / 14 + 2).toNat = u.size + u.size / 14 + 2 := by
  rw [UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_div, toNat_size hs]
  simp only [UInt64.reduceToNat]
  omega

/-- The levels of `c` chunks: `K < 40` and `2^K ≤ c`. -/
theorem levels_pow {u : Array UInt64} (hs : u.size < 2 ^ 32) :
    (levelsFor (u.size.toUInt64 + u.size.toUInt64 / 14 + 2)).toNat < 40 ∧
      2 ^ (levelsFor (u.size.toUInt64 + u.size.toUInt64 / 14 + 2)).toNat ≤
        u.size + u.size / 14 + 2 := by
  have hc := chunkCount_toNat hs
  obtain ⟨hK40, -, hKmin⟩ := levelsFor_spec _ (by rw [hc]; omega) (by rw [hc]; omega)
  rw [hc] at hKmin
  refine ⟨hK40, ?_⟩
  rcases hKmin with h | h
  · rw [h]; simp
  · omega

/-- The words of the printer's workspace for `K` levels. -/
theorem printSpace_toNat (K : UInt64) (hK : K.toNat < 40) :
    (2 * K + 2 + (2 : UInt64) <<< K + 7 * ((1 : UInt64) <<< K) + 22 * ((1 : UInt64) <<< K) +
      20).toNat = 2 * K.toNat + 22 + 31 * 2 ^ K.toNat := by
  have hsh2 := shl_two K (by omega)
  have hsh1 := shl_one' K (by omega)
  have hp2 : 2 ^ (K.toNat + 1) = 2 * 2 ^ K.toNat := by ring
  have hP : 2 ^ K.toNat < 2 ^ 40 := Nat.pow_lt_pow_right (by norm_num) hK
  rw [hp2] at hsh2
  generalize 2 ^ K.toNat = P at hsh1 hsh2 hP ⊢
  have e1 : (2 * K).toNat = 2 * K.toNat := toNat_mul_lt' (by simp only [UInt64.reduceToNat]; omega)
  have e2 : (2 * K + 2).toNat = 2 * K.toNat + 2 := by
    rw [toNat_add_lt (by rw [e1]; simp only [UInt64.reduceToNat]; omega), e1]; rfl
  have e3 : (2 * K + 2 + (2 : UInt64) <<< K).toNat = 2 * K.toNat + 2 + 2 * P := by
    rw [toNat_add_lt (by rw [e2, hsh2]; omega), e2, hsh2]
  have e4 : (7 * ((1 : UInt64) <<< K)).toNat = 7 * P := by
    rw [toNat_mul_lt' (by rw [hsh1]; simp only [UInt64.reduceToNat]; omega), hsh1]; rfl
  have e5 : (2 * K + 2 + (2 : UInt64) <<< K + 7 * ((1 : UInt64) <<< K)).toNat =
      2 * K.toNat + 2 + 9 * P := by
    rw [toNat_add_lt (by rw [e3, e4]; omega), e3, e4]; omega
  have e6 : (22 * ((1 : UInt64) <<< K)).toNat = 22 * P := by
    rw [toNat_mul_lt' (by rw [hsh1]; simp only [UInt64.reduceToNat]; omega), hsh1]; rfl
  have e7 : (2 * K + 2 + (2 : UInt64) <<< K + 7 * ((1 : UInt64) <<< K) +
      22 * ((1 : UInt64) <<< K)).toNat = 2 * K.toNat + 2 + 31 * P := by
    rw [toNat_add_lt (by rw [e5, e6]; omega), e5, e6]; omega
  rw [toNat_add_lt (by rw [e7]; simp only [UInt64.reduceToNat]; omega), e7]
  simp only [UInt64.reduceToNat]
  omega

/-- The workspace of the printer, `31 · 2^K + 2 K + 22` words, allocates at most
`248 c + 872` bytes for `c = n + ⌊n/14⌋ + 2` chunks. -/
theorem chunksDC_bound_le (k : ℕ) (t T L : UInt64) (u : Array UInt64) (hs : u.size < 2 ^ 32) :
    compiled.chunksDC.bound (k + 1) (t, T, L, u) ≤ 248 * (u.size + u.size / 14 + 2) + 872 := by
  rw [compiled.chunksDC.bound_eq]
  simp only [powInit_bound, toChunks_bound, Nat.add_zero]
  rw [blockCost_eq]
  obtain ⟨hK40, hP⟩ := levels_pow hs
  generalize levelsFor (u.size.toUInt64 + u.size.toUInt64 / 14 + 2) = K at hK40 hP ⊢
  rw [printSpace_toNat K hK40]
  omega

/-- The natural printer allocates at most `438 n + 1968` bytes for `n` limbs, at every threshold
and every level of the leaves. -/
theorem natToTextDCWith_bound_le (k : ℕ) (t T L P : UInt64) (u : Array UInt64)
    (hs : u.size < 2 ^ 32) :
    compiled.natToTextDCWith.bound (k + 2) (t, T, L, P, u) ≤ 438 * u.size + 1968 := by
  rw [compiled.natToTextDCWith.bound_eq]
  split
  · have := intToText_bound_le ⟨false, u⟩ hs
    simp only at this
    omega
  · have h1 := chunksDC_bound_le k t T L u hs
    obtain ⟨hK40, hP⟩ := levels_pow hs
    have h2 := textOfChunks_bound_le false (chunksDC t T L u)
      (2 * levelsFor (u.size.toUInt64 + u.size.toUInt64 / 14 + 2) + 2)
      ((2 : UInt64) <<< levelsFor (u.size.toUInt64 + u.size.toUInt64 / 14 + 2))
    generalize levelsFor (u.size.toUInt64 + u.size.toUInt64 / 14 + 2) = K at hK40 hP h2 ⊢
    have hsh2 := shl_two K (by omega)
    have hp2 : 2 ^ (K.toNat + 1) = 2 * 2 ^ K.toNat := by ring
    rw [hsh2, hp2] at h2
    omega

theorem natToTextDC_bound_le (k : ℕ) (u : Array UInt64) (hs : u.size < 2 ^ 32) :
    compiled.natToTextDC.bound (k + 3) u ≤ 438 * u.size + 1968 := by
  rw [compiled.natToTextDC.bound_eq]; exact natToTextDCWith_bound_le k _ _ _ _ u hs

/-- The integer printer allocates at most `438 n + 1968` bytes for a magnitude of `n` limbs. -/
theorem intToTextDC_bound_le (k : ℕ) (x : BigInt) (hs : x.mag.size < 2 ^ 32) :
    compiled.intToTextDC.bound (k + 2) x ≤ 438 * x.mag.size + 1968 := by
  rw [compiled.intToTextDC.bound_eq]
  split
  · have := intToText_bound_le x hs
    omega
  · have h1 := chunksDC_bound_le k karaThreshold divBase printLeaf x.mag hs
    obtain ⟨hK40, hP⟩ := levels_pow hs
    have h2 := textOfChunks_bound_le x.neg (chunksDC karaThreshold divBase printLeaf x.mag)
      (2 * levelsFor (x.mag.size.toUInt64 + x.mag.size.toUInt64 / 14 + 2) + 2)
      ((2 : UInt64) <<< levelsFor (x.mag.size.toUInt64 + x.mag.size.toUInt64 / 14 + 2))
    generalize levelsFor (x.mag.size.toUInt64 + x.mag.size.toUInt64 / 14 + 2) = K at hK40 hP h2 ⊢
    have hsh2 := shl_two K (by omega)
    have hp2 : 2 ^ (K.toNat + 1) = 2 * 2 ^ K.toNat := by ring
    rw [hsh2, hp2] at h2
    omega

end Library.Numerics.Bignum.Third
