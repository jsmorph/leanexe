module

public import Library.Numerics.Bignum.Second.Compiled
public import Library.Numerics.Bignum.Second.Reader
public import Verified.BoundFacts

@[expose] public section

/-!
The frames and the allocation bounds of the second iteration's module.

`kara` is the one recursion.  A call on `n ≥ 16` limbs recurses on at most `⌈n/2⌉ + 1`, so
`kara_fits` finds enough frames whenever `n ≤ 13 · 2^k + 2`, and at 1,000 frames for every `n`
below `2^64` (`kara_fits_all`); its callers add one frame each (`natMulKaraWith`, `natMulKara`,
`intMulKara`) or three (`readPass`, `decimalValueDC`, and the readers), so every export's frame
condition at 1,000 frames holds for every argument.  The generated bound of `kara`, `baseMul`,
`addGen`, `subGen`, `mulAddSeg`, and `readPass` is 0: every array that they update is owned and
moved, and the bound charges nothing for an update in place (`kara_bound`, `readPass_bound`).  A
product therefore allocates its workspace and its trimmed result, and a reader its workspace of
`6 N` limbs, or `N` without passes, and its result.
-/

namespace Library.Numerics.Bignum.Second

open Library.Numerics.Bignum
open Library.Numerics.MultiPrecision (value Digits)
open Verified

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

theorem kara_fits_all (k : ℕ) (hk : 64 ≤ k) (x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64) : compiled.kara.fits (k + 1) x = true := by
  obtain ⟨t, ⟨W⟩, ap, bp, rp, tp, n⟩ := x
  apply kara_fits
  have h1 := UInt64.toNat_lt n
  have h2 : 2 ^ 64 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

/-! ## The passes of the reader -/

theorem readPass_bound : ∀ (k : ℕ) (x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) × UInt64 ×
    UInt64 × UInt64), compiled.readPass.bound k x = 0
  | 0, _ => rfl
  | k + 1, ⟨t, ⟨W⟩, N, e0, e⟩ => by
    rw [compiled.readPass.bound_eq, loopCost_eq_zero (fun _ => rfl) (fun i s => by
      simp only [kara_bound, Nat.add_zero])]
    simp only [kara_bound, Nat.zero_add, ite_self]

theorem readPass_fits (k : ℕ) (hk : 65 ≤ k) (x : UInt64 × LeanExe.Pipeline.Moved (Array UInt64) ×
    UInt64 × UInt64 × UInt64) : compiled.readPass.fits (k + 1) x = true := by
  obtain ⟨t, ⟨W⟩, N, e0, e⟩ := x
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [compiled.readPass.fits_eq, loopFits_true (fun _ => rfl) (fun i s => kara_fits_all k' (by omega) _)]
  simp only [kara_fits_all k' (by omega), Bool.true_and, ite_self]

/-! ## Frames of the callers -/

theorem natMulKaraWith_fits (k : ℕ) (hk : 65 ≤ k) (x : UInt64 × Array UInt64 × Array UInt64) :
    compiled.natMulKaraWith.fits (k + 1) x = true := by
  obtain ⟨t, u, v⟩ := x
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [compiled.natMulKaraWith.fits_eq]
  have hb : ∀ (b : Bool) (x), (if b = true then true else compiled.kara.fits (k' + 1) x) = true :=
    fun b x => by split <;> [rfl; exact kara_fits_all k' (by omega) x]
  split <;> split <;> first | rfl | exact loopFits_true (fun _ => rfl) (fun i s => hb _ _) _ _ _

theorem natMulKara_fits (k : ℕ) (hk : 66 ≤ k) (x : Array UInt64 × Array UInt64) :
    compiled.natMulKara.fits (k + 1) x = true := by
  obtain ⟨u, v⟩ := x
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [compiled.natMulKara.fits_eq]; exact natMulKaraWith_fits k' (by omega) _

theorem intMulKara_fits (k : ℕ) (hk : 67 ≤ k) (x : BigInt × BigInt) :
    compiled.intMulKara.fits (k + 1) x = true := by
  obtain ⟨a, b⟩ := x
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [compiled.intMulKara.fits_eq]; exact natMulKara_fits k' (by omega) _

theorem decimalValueDC_fits (k : ℕ) (hk : 66 ≤ k)
    (x : UInt64 × UInt64 × Array UInt64 × UInt64 × UInt64) :
    compiled.decimalValueDC.fits (k + 1) x = true := by
  obtain ⟨t, E, s, start, count⟩ := x
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [compiled.decimalValueDC.fits_eq]
  exact loopFits_true (fun _ => rfl) (fun i st => readPass_fits k' (by omega) _) _ _ _

theorem natOfTextDCWith_fits (k : ℕ) (hk : 67 ≤ k) (x : UInt64 × UInt64 × Array UInt64) :
    compiled.natOfTextDCWith.fits (k + 1) x = true := by
  obtain ⟨t, E, s⟩ := x
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [compiled.natOfTextDCWith.fits_eq]
  simp only [decimalValueDC_fits k' (by omega), ite_self]

theorem natOfTextDC_fits (k : ℕ) (hk : 68 ≤ k) (s : Array UInt64) :
    compiled.natOfTextDC.fits (k + 1) s = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [compiled.natOfTextDC.fits_eq]; exact natOfTextDCWith_fits k' (by omega) _

theorem intOfTextDC_fits (k : ℕ) (hk : 67 ≤ k) (s : Array UInt64) :
    compiled.intOfTextDC.fits (k + 1) s = true := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [compiled.intOfTextDC.fits_eq]
  simp only [decimalValueDC_fits k' (by omega), ite_self]

/-! ## Closed forms of the bounds -/

/-- The trimmed copy of `len` words allocates at most `len` words. -/
theorem trimSeg_bound_le (W : Array UInt64) (p len : UInt64) :
    compiled.trimSeg.bound (W, p, len) ≤ 8 * len.toNat + 56 := by
  rw [compiled.trimSeg.bound_eq, blockCost_eq]
  have := LeanExe.Dialect.loop_induction (n := len) (init := (0 : UInt64))
    (f := fun i k => if W[(p + i).toNat]! = 0 then k else i + 1)
    (fun j (k : UInt64) => k.toNat ≤ j) (Nat.zero_le _) (by
      intro j k hj hk
      split
      · omega
      · rw [toNat_add_lt (by
          rw [toNat_ofNat_lt (by have := len.toNat_lt; omega)]; simp only [UInt64.reduceToNat]
          have := len.toNat_lt; omega), toNat_ofNat_lt (by have := len.toNat_lt; omega)]
        simp only [UInt64.reduceToNat]; omega)
  omega

/-- The words of the workspace of a long product: `u` padded to `q` chunks of `n`, `v`, the
result, the buffer, and the scratch. -/
theorem workspace_toNat {m n : UInt64} {M Nn : ℕ} (hm : m.toNat = M) (hn : n.toNat = Nn)
    (hM : M < 2 ^ 32) (hN : Nn < 2 ^ 32) (hpos : 1 ≤ Nn) :
    ((m + n - 1) / n * n + n + (m + n - 1) / n * n + n + 2 * n + 6 * n).toNat ≤
      2 * (M + Nn) + 10 * Nn ∧ (m + n).toNat = M + Nn := by
  have hq : ((m + n - 1) / n).toNat = (M + Nn - 1) / Nn := by
    rw [UInt64.toNat_div, UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, toNat_add_lt (by omega)]; simp only [UInt64.reduceToNat]; omega),
      toNat_add_lt (by omega), hm, hn]
    simp only [UInt64.reduceToNat]
  have hQ := Nat.div_mul_le_self (M + Nn - 1) Nn
  generalize (m + n - 1) / n = q at hq ⊢
  have hqn : (q * n).toNat = (M + Nn - 1) / Nn * Nn := by
    rw [toNat_mul_lt (by rw [hq, hn]; omega), hq, hn]
  have h2n : (2 * n).toNat = 2 * Nn := by
    rw [toNat_mul_lt (by simp only [UInt64.reduceToNat]; omega), hn]; rfl
  have h6n : (6 * n).toNat = 6 * Nn := by
    rw [toNat_mul_lt (by simp only [UInt64.reduceToNat]; omega), hn]; rfl
  refine ⟨?_, by rw [toNat_add_lt (by rw [hm, hn]; omega), hm, hn]⟩
  have e1 : (q * n + n).toNat = (M + Nn - 1) / Nn * Nn + Nn := by
    rw [toNat_add_lt (by rw [hqn, hn]; omega), hqn, hn]
  have e2 : (q * n + n + q * n).toNat = 2 * ((M + Nn - 1) / Nn * Nn) + Nn := by
    rw [toNat_add_lt (by rw [e1, hqn]; omega), e1, hqn]; omega
  have e3 : (q * n + n + q * n + n).toNat = 2 * ((M + Nn - 1) / Nn * Nn) + 2 * Nn := by
    rw [toNat_add_lt (by rw [e2, hn]; omega), e2, hn]; omega
  have e4 : (q * n + n + q * n + n + 2 * n).toNat = 2 * ((M + Nn - 1) / Nn * Nn) + 4 * Nn := by
    rw [toNat_add_lt (by rw [e3, h2n]; omega), e3, h2n]; omega
  rw [toNat_add_lt (by rw [e4, h6n]; omega), e4, h6n]
  omega

/-- The product allocates its workspace and its result: at most `24 (m + n) + 80 min(m, n) + 112`
bytes for operands of `m` and `n` limbs, at every threshold. -/
theorem natMulKaraWith_bound_le (k : ℕ) (t : UInt64) (u v : Array UInt64) (hu : u.size < 2 ^ 32)
    (hv : v.size < 2 ^ 32) :
    compiled.natMulKaraWith.bound (k + 1) (t, u, v) ≤
      24 * (u.size + v.size) + 80 * min u.size v.size + 112 := by
  have hmu : u.size.toUInt64.toNat = u.size := LeanExe.Dialect.size_toUInt64 u (by omega)
  have hmv : v.size.toUInt64.toNat = v.size := LeanExe.Dialect.size_toUInt64 v (by omega)
  rw [compiled.natMulKaraWith.bound_eq]
  split
  · rename_i hlt
    rw [UInt64.lt_iff_toNat_lt, hmu, hmv] at hlt
    split
    · have h2 : (2 * (v.size.toUInt64 + u.size.toUInt64)).toNat = 2 * (v.size + u.size) := by
        rw [toNat_mul_lt (by rw [toNat_add_lt (by omega)]; simp only [hmu, hmv, UInt64.reduceToNat]; omega),
          toNat_add_lt (by omega)]
        simp only [hmu, hmv, UInt64.reduceToNat]
      have h1 : (v.size.toUInt64 + u.size.toUInt64).toNat = v.size + u.size := by
        rw [toNat_add_lt] <;> rw [hmu, hmv] <;> omega
      rw [blockCost_eq, h2]
      refine le_trans (Nat.add_le_add_left (trimSeg_bound_le _ _ _) _) ?_
      rw [h1]
      omega
    · rename_i hs
      obtain ⟨hw, hmn⟩ := workspace_toNat (m := v.size.toUInt64) (n := u.size.toUInt64) hmv hmu hv hu
        (by
          simp only [decide_eq_true_eq, not_or, UInt64.not_lt, UInt64.le_iff_toNat_le, hmu,
            UInt64.reduceToNat] at hs
          omega)
      simp only [kara_bound, ite_self, loopCost_const, Nat.mul_zero, Nat.zero_add]
      rw [blockCost_eq]
      refine le_trans (Nat.add_le_add_left (trimSeg_bound_le _ _ _) _) ?_
      rw [hmn]
      omega
  · rename_i hlt
    rw [UInt64.lt_iff_toNat_lt, hmu, hmv] at hlt
    split
    · have h2 : (2 * (u.size.toUInt64 + v.size.toUInt64)).toNat = 2 * (u.size + v.size) := by
        rw [toNat_mul_lt (by rw [toNat_add_lt (by omega)]; simp only [hmu, hmv, UInt64.reduceToNat]; omega),
          toNat_add_lt (by omega)]
        simp only [hmu, hmv, UInt64.reduceToNat]
      have h1 : (u.size.toUInt64 + v.size.toUInt64).toNat = u.size + v.size := by
        rw [toNat_add_lt] <;> rw [hmu, hmv] <;> omega
      rw [blockCost_eq, h2]
      refine le_trans (Nat.add_le_add_left (trimSeg_bound_le _ _ _) _) ?_
      rw [h1]
      omega
    · rename_i hs
      obtain ⟨hw, hmn⟩ := workspace_toNat (m := u.size.toUInt64) (n := v.size.toUInt64) hmu hmv hu hv
        (by
          simp only [decide_eq_true_eq, not_or, UInt64.not_lt, UInt64.le_iff_toNat_le, hmv,
            UInt64.reduceToNat] at hs
          omega)
      simp only [kara_bound, ite_self, loopCost_const, Nat.mul_zero, Nat.zero_add]
      rw [blockCost_eq]
      refine le_trans (Nat.add_le_add_left (trimSeg_bound_le _ _ _) _) ?_
      rw [hmn]
      omega

theorem natMulKara_bound_le (k : ℕ) (u v : Array UInt64) (hu : u.size < 2 ^ 32)
    (hv : v.size < 2 ^ 32) :
    compiled.natMulKara.bound (k + 2) (u, v) ≤
      24 * (u.size + v.size) + 80 * min u.size v.size + 112 := by
  rw [compiled.natMulKara.bound_eq]; exact natMulKaraWith_bound_le k _ u v hu hv

theorem intMulKara_bound_le (k : ℕ) (x y : BigInt) (hx : x.mag.size < 2 ^ 32)
    (hy : y.mag.size < 2 ^ 32) :
    compiled.intMulKara.bound (k + 3) (x, y) ≤
      24 * (x.mag.size + y.mag.size) + 80 * min x.mag.size y.mag.size + 112 := by
  rw [compiled.intMulKara.bound_eq]; exact natMulKara_bound_le k _ _ hx hy

/-! ## Bounds of the readers -/

/-- The reader of digits allocates its workspace of at most `6 N` limbs and its result of at most
`N` limbs, for the `N` limbs of its elements. -/
theorem decimalValueDC_bound_le (k : ℕ) (t E : UInt64) (s : Array UInt64) (start count : UInt64) :
    compiled.decimalValueDC.bound (k + 1) (t, E, s, start, count) ≤
      56 * ((((count + 8) / 9 + LeanExe.repeatWhile 32 1 (fun p => decide (E * p < (count + 8) / 9))
        (fun p => 2 * p) - 1) / LeanExe.repeatWhile 32 1 (fun p => decide (E * p < (count + 8) / 9))
        (fun p => 2 * p)) * LeanExe.repeatWhile 32 1 (fun p => decide (E * p < (count + 8) / 9))
        (fun p => 2 * p)).toNat + 112 := by
  rw [compiled.decimalValueDC.bound_eq]
  generalize LeanExe.repeatWhile 32 1 (fun p => decide (E * p < (count + 8) / 9)) (fun p => 2 * p) = P2
  generalize (count + 8) / 9 = C
  generalize (C + P2 - 1) / P2 = e0
  generalize e0 * P2 = N
  rw [compiled.readInit.bound_eq, blockCost_eq,
    loopCost_eq_zero (fun _ => rfl) (fun i st => readPass_bound k _), Nat.add_zero]
  refine le_trans (Nat.add_le_add_left (trimSeg_bound_le _ _ _) _) ?_
  have h6 : (if e0 < N then 6 * N else N).toNat ≤ 6 * N.toNat := by
    split
    · rw [UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; exact Nat.mod_le _ _
    · omega
  omega

/-- The count of base elements is a power of two, and the step before the last kept `E · p`
below the chunk count. -/
theorem count_pow_lt (E C : UInt64) (hE : E.toNat ≤ 2 ^ 32) :
    ∀ (f j : ℕ) (p : UInt64), p.toNat = 2 ^ j → j + f ≤ 32 →
      (j = 0 ∨ E.toNat * 2 ^ (j - 1) < C.toNat) →
    ∃ K, (LeanExe.repeatWhile.go (fun p => decide (E * p < C)) (fun p => 2 * p) f p).toNat =
      2 ^ K ∧ K ≤ 32 ∧ (K = 0 ∨ E.toNat * 2 ^ (K - 1) < C.toNat)
  | 0, j, p, h1, h2, h3 => ⟨j, by simpa [LeanExe.repeatWhile.go] using h1, by omega, h3⟩
  | f + 1, j, p, h1, h2, h3 => by
    simp only [LeanExe.repeatWhile.go]
    split
    · rename_i hc
      have hj : 2 ^ j ≤ 2 ^ 31 := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hEp : (E * p).toNat = E.toNat * 2 ^ j := by
        rw [toNat_mul_lt (by rw [h1]; nlinarith), h1]
      apply count_pow_lt E C hE f (j + 1) (2 * p) _ (by omega)
      · right
        simp only [decide_eq_true_eq, UInt64.lt_iff_toNat_lt, hEp] at hc
        simpa using hc
      · have h2' : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
        rw [toNat_mul_lt (by rw [h1]; simp only [UInt64.reduceToNat]; omega), h1, h2']
        simp only [UInt64.reduceToNat]
    · exact ⟨j, h1, by omega, h3⟩

/-- The elements of the reader take `N ≤ C + P - 1` limbs for `C` chunks and `P` base elements,
with `P = 1` or `E P < 2 C`. -/
theorem elements_toNat (E C : UInt64) (hE : E.toNat ≤ 2 ^ 32) (hC : C.toNat < 2 ^ 32)
    (hC1 : 1 ≤ C.toNat) :
    ∃ P : ℕ, ((C + LeanExe.repeatWhile 32 1 (fun p => decide (E * p < C)) (fun p => 2 * p) - 1) /
        LeanExe.repeatWhile 32 1 (fun p => decide (E * p < C)) (fun p => 2 * p) *
        LeanExe.repeatWhile 32 1 (fun p => decide (E * p < C)) (fun p => 2 * p)).toNat ≤
      C.toNat + P - 1 ∧ (P = 1 ∨ E.toNat * P < 2 * C.toNat) := by
  obtain ⟨K, hK, hK32, hKE⟩ := count_pow_lt E C hE 32 0 1 rfl (by omega) (Or.inl rfl)
  refine ⟨2 ^ K, ?_, ?_⟩
  · have hP : (LeanExe.repeatWhile 32 1 (fun p => decide (E * p < C)) (fun p => 2 * p)).toNat =
        2 ^ K := hK
    generalize LeanExe.repeatWhile 32 1 (fun p => decide (E * p < C)) (fun p => 2 * p) = P2 at hP ⊢
    have hpow : 1 ≤ 2 ^ K := Nat.one_le_two_pow
    have hpow32 : 2 ^ K ≤ 2 ^ 32 := Nat.pow_le_pow_right (by norm_num) hK32
    have he0 : ((C + P2 - 1) / P2).toNat = (C.toNat + 2 ^ K - 1) / 2 ^ K := by
      rw [UInt64.toNat_div, UInt64.toNat_sub_of_le _ _ (by
        rw [UInt64.le_iff_toNat_le, toNat_add_lt (by rw [hP]; omega), hP]
        simp only [UInt64.reduceToNat]; omega), toNat_add_lt (by rw [hP]; omega), hP]
      simp only [UInt64.reduceToNat]
    have hle := Nat.div_mul_le_self (C.toNat + 2 ^ K - 1) (2 ^ K)
    rw [toNat_mul_lt (by rw [he0, hP]; omega), he0, hP]
    omega
  · by_cases hK0 : K = 0
    · left; rw [hK0]; rfl
    · right
      rcases hKE with h | h
      · exact absurd h hK0
      have : 2 ^ K = 2 * 2 ^ (K - 1) := by rw [← pow_succ']; congr 1; omega
      rw [this]
      nlinarith

/-- With the base elements of at most `readBase = 768` chunks, the elements take at most
`C + C / 384` limbs for `C` chunks. -/
theorem elements_readBase (C : UInt64) (hC : C.toNat < 2 ^ 32) (hC1 : 1 ≤ C.toNat) :
    ((C + LeanExe.repeatWhile 32 1 (fun p => decide (readBase * p < C)) (fun p => 2 * p) - 1) /
        LeanExe.repeatWhile 32 1 (fun p => decide (readBase * p < C)) (fun p => 2 * p) *
        LeanExe.repeatWhile 32 1 (fun p => decide (readBase * p < C)) (fun p => 2 * p)).toNat ≤
      C.toNat + C.toNat / 384 := by
  obtain ⟨P, h1, h2⟩ := elements_toNat readBase C (by decide) hC hC1
  have hr : readBase.toNat = 768 := rfl
  rw [hr] at h2
  omega

/-- With any bound `1 ≤ E ≤ 2^32` on the base elements, the elements take fewer than `3 C`
limbs. -/
theorem elements_le (E C : UInt64) (hE1 : 1 ≤ E.toNat) (hE : E.toNat ≤ 2 ^ 32)
    (hC : C.toNat < 2 ^ 32) (hC1 : 1 ≤ C.toNat) :
    ((C + LeanExe.repeatWhile 32 1 (fun p => decide (E * p < C)) (fun p => 2 * p) - 1) /
        LeanExe.repeatWhile 32 1 (fun p => decide (E * p < C)) (fun p => 2 * p) *
        LeanExe.repeatWhile 32 1 (fun p => decide (E * p < C)) (fun p => 2 * p)).toNat ≤
      3 * C.toNat := by
  obtain ⟨P, h1, h2⟩ := elements_toNat E C hE hC hC1
  rcases h2 with h2 | h2
  · omega
  · have : P ≤ E.toNat * P := Nat.le_mul_of_pos_left _ (by omega)
    omega

/-- The chunk count of `count` digits as a word. -/
theorem chunks_toNat {count : UInt64} (h : count.toNat < 2 ^ 32) :
    ((count + 8) / 9).toNat = (count.toNat + 8) / 9 := by
  rw [UInt64.toNat_div, toNat_add_lt (by simp only [UInt64.reduceToNat]; omega)]
  simp only [UInt64.reduceToNat]

/-- The reader of digits with `readBase` allocates at most `56 (C + C / 384) + 112` bytes for
`C = ⌈count / 9⌉` chunks. -/
theorem decimalValueDC_readBase_le (k : ℕ) (t : UInt64) (s : Array UInt64) (start count : UInt64)
    (hc : count.toNat < 2 ^ 32) (hc1 : 1 ≤ count.toNat) :
    compiled.decimalValueDC.bound (k + 1) (t, readBase, s, start, count) ≤
      56 * ((count.toNat + 8) / 9 + (count.toNat + 8) / 9 / 384) + 112 := by
  have h1 := decimalValueDC_bound_le k t readBase s start count
  have h2 := elements_readBase ((count + 8) / 9) (by rw [chunks_toNat hc]; omega)
    (by rw [chunks_toNat hc]; omega)
  rw [chunks_toNat hc] at h2
  omega

/-- The reader of digits with a bound `1 ≤ E ≤ 2^32` allocates at most `168 C + 112` bytes. -/
theorem decimalValueDC_bound_le' (k : ℕ) (t E : UInt64) (s : Array UInt64) (start count : UInt64)
    (hE1 : 1 ≤ E.toNat) (hE : E.toNat ≤ 2 ^ 32) (hc : count.toNat < 2 ^ 32)
    (hc1 : 1 ≤ count.toNat) :
    compiled.decimalValueDC.bound (k + 1) (t, E, s, start, count) ≤
      168 * ((count.toNat + 8) / 9) + 112 := by
  have h1 := decimalValueDC_bound_le k t E s start count
  have h2 := elements_le E ((count + 8) / 9) hE1 hE (by rw [chunks_toNat hc]; omega)
    (by rw [chunks_toNat hc]; omega)
  rw [chunks_toNat hc] at h2
  omega

/-- The natural reader allocates at most `19 s + 262` bytes for a text of `s` words, with any
bound `1 ≤ E ≤ 2^32` on its base elements. -/
theorem natOfTextDCWith_bound_le (k : ℕ) (t E : UInt64) (s : Array UInt64) (hE1 : 1 ≤ E.toNat)
    (hE : E.toNat ≤ 2 ^ 32) (hs : s.size < 2 ^ 32) :
    compiled.natOfTextDCWith.bound (k + 2) (t, E, s) ≤ 19 * s.size + 262 := by
  have hn : s.size.toUInt64.toNat = s.size := LeanExe.Dialect.size_toUInt64 s (by omega)
  rw [compiled.natOfTextDCWith.bound_eq]
  split
  · rw [blockCost_eq]; simp only [UInt64.reduceToNat]; omega
  · rename_i h0
    have h1 : 1 ≤ s.size := by
      by_contra h; apply h0; rw [beq_iff_eq, ← UInt64.toNat_inj, hn]; simp only [UInt64.reduceToNat]
      omega
    split
    · have := decimalValueDC_bound_le' k t E s 0 s.size.toUInt64 hE1 hE (by omega) (by omega)
      rw [hn] at this
      omega
    · rw [blockCost_eq]; simp only [UInt64.reduceToNat]; omega

/-- The natural reader allocates at most `7 s + 168` bytes for a text of `s` words. -/
theorem natOfTextDC_bound_le (k : ℕ) (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    compiled.natOfTextDC.bound (k + 3) s ≤ 7 * s.size + 168 := by
  have hn : s.size.toUInt64.toNat = s.size := LeanExe.Dialect.size_toUInt64 s (by omega)
  rw [compiled.natOfTextDC.bound_eq, compiled.natOfTextDCWith.bound_eq]
  split
  · rw [blockCost_eq]; simp only [UInt64.reduceToNat]; omega
  · rename_i h0
    have h1 : 1 ≤ s.size := by
      by_contra h; apply h0; rw [beq_iff_eq, ← UInt64.toNat_inj, hn]; simp only [UInt64.reduceToNat]
      omega
    split
    · have := decimalValueDC_readBase_le k karaThreshold s 0 s.size.toUInt64 (by omega) (by omega)
      rw [hn] at this
      omega
    · rw [blockCost_eq]; simp only [UInt64.reduceToNat]; omega

/-- The integer reader allocates at most `7 s + 168` bytes for a text of `s` words. -/
theorem intOfTextDC_bound_le (k : ℕ) (s : Array UInt64) (hs : s.size < 2 ^ 32) :
    compiled.intOfTextDC.bound (k + 2) s ≤ 7 * s.size + 168 := by
  have hn : s.size.toUInt64.toNat = s.size := LeanExe.Dialect.size_toUInt64 s (by omega)
  rw [compiled.intOfTextDC.bound_eq]
  generalize hst : (if (s[UInt64.toNat 0]! == 45) = true then (1 : UInt64) else 0) = st
  have hst1 : st.toNat ≤ 1 := by rw [← hst]; split <;> simp
  split
  · rw [blockCost_eq]; simp only [UInt64.reduceToNat]; omega
  · rename_i h0
    have h1 : 1 ≤ s.size := by
      by_contra h; apply h0; rw [beq_iff_eq, ← UInt64.toNat_inj, hn]; simp only [UInt64.reduceToNat]
      omega
    split
    · rw [blockCost_eq]; simp only [UInt64.reduceToNat]; omega
    · rename_i hc0
      have hcn : (s.size.toUInt64 - st).toNat = s.size - st.toNat := by
        rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hn]; omega), hn]
      have hc1 : 1 ≤ (s.size.toUInt64 - st).toNat := by
        by_contra h; apply hc0; rw [beq_iff_eq, ← UInt64.toNat_inj]
        simp only [UInt64.reduceToNat]; omega
      split
      · have := decimalValueDC_readBase_le k karaThreshold s st (s.size.toUInt64 - st)
          (by omega) hc1
        rw [hcn] at this hc1
        omega
      · rw [blockCost_eq]; simp only [UInt64.reduceToNat]; omega

end Library.Numerics.Bignum.Second
