import Library.Numerics.Float64.Erfc.ErfcFastMain
import Library.Numerics.Float64.Erfc.ErfcSeriesI
import Library.Numerics.Float64.Erfc.ErfcRound

/-!
One row of `cr_erf_fast` from `1/16` on.  For `x` in `[i/16, (i+1)/16)`, `Erfc.erfFastMain` takes
`v = ⌊16 x⌋ = i` (`ErfcRound.floorF_spec`), the coefficients of row `i` from `13 (i - 1)`, and the
exact reduced argument `z = (x - 1/32) - v/16 = x - (2 i + 1)/32`, and evaluates the row's
polynomial at `z`.  `RowOK` collects the conditions that the kernel checks for a row: finite words,
the index arithmetic, `ErfcFastMain.MainHyp`, the certificate `ErfcSeriesI.rowCheckI`, and the sum of
the rounding bound and the certificate's bound below `T`.  `row_err` then bounds the distance of
the computed double-double from `erf x` by `T`.
-/

namespace Library.Numerics.Float64.Erfc.ErfcFastRow

open CodeLib.IEEE64 LeanExe.ProofKit ErfcEft ErfcEft2 ErfcOps ErfcTrack ErfcFastMain ErfcSeries
  ErfcRound ErfcSeriesI Library.Numerics.Arithmetic.Fma.FmaSpec PolyBound RealErf

set_option exponentiation.threshold 2200

/-- The coefficients of row `i` of a table of 13 words per row, rows counted from 1. -/
def rowQ (tab : Array UInt64) (i : ℕ) : List ℚ :=
  (List.range 13).map fun k => ratOfWord tab[13 * (i - 1) + k]!

theorem rowQ_getD (tab : Array UInt64) (i k : ℕ) (hk : k < 13) :
    (rowQ tab i).getD k 0 = ratOfWord tab[13 * (i - 1) + k]! := by
  simp [rowQ, List.getD_eq_getElem?_getD, hk]

/-- The conditions of row `i` that the kernel checks. -/
def RowOK (tab : Array UInt64) (i n J : ℕ) (ε : ℚ) (d : ℕ) (T : ℚ) : Prop :=
  1 ≤ i ∧ i ≤ 100 ∧ (∀ k < 13, Finite tab[13 * (i - 1) + k]!) ∧
    (∀ k < 13, (13 * (UInt64.ofNat i - 1) + UInt64.ofNat k).toNat = 13 * (i - 1) + k) ∧
    MainHyp (rowQ tab i) (1 / 32) (mainB (rowQ tab i) (1 / 32)) ∧
    1 ≤ n ∧ rowCheckI n J (2 * i + 1) 32 ε (rowPoly (rowQ tab i)) d = true ∧
    (mainB (rowQ tab i) (1 / 32)).s8e + rowBoundI n J (2 * i + 1) 32 ε ≤ T

set_option synthInstance.maxSize 4096 in
instance (tab : Array UInt64) (i n J : ℕ) (ε : ℚ) (d : ℕ) (T : ℚ) :
    Decidable (RowOK tab i n J ε d T) := by
  unfold RowOK; infer_instance

theorem lit_vals : ff (16.0 : Float) ∧ fv (16.0 : Float) = 16 ∧ ff (0.03125 : Float) ∧
    fv (0.03125 : Float) = 1 / 32 ∧ ff (0.0625 : Float) ∧ fv (0.0625 : Float) = 1 / 16 := by
  have e1 : (16.0 : Float) = Float.ofBits 0x4030000000000000 := by
    rw [← F64Bits.ofBits_toBits (16.0 : Float)]; rfl
  have e2 : (0.03125 : Float) = Float.ofBits 0x3FA0000000000000 := by
    rw [← F64Bits.ofBits_toBits (0.03125 : Float)]; rfl
  have e3 : (0.0625 : Float) = Float.ofBits 0x3FB0000000000000 := by
    rw [← F64Bits.ofBits_toBits (0.0625 : Float)]; rfl
  have k1 : Finite (0x4030000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have k2 : Finite (0x3FA0000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have k3 : Finite (0x3FB0000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  obtain ⟨a1, b1⟩ := ofBits_ff _ k1
  obtain ⟨a2, b2⟩ := ofBits_ff _ k2
  obtain ⟨a3, b3⟩ := ofBits_ff _ k3
  rw [e1, e2, e3]
  refine ⟨a1, ?_, a2, ?_, a3, ?_⟩
  · rw [b1, show ratOfWord 0x4030000000000000 = 16 by decide +kernel]; norm_num
  · rw [b2, show ratOfWord 0x3FA0000000000000 = 1 / 32 by decide +kernel]; norm_num
  · rw [b3, show ratOfWord 0x3FB0000000000000 = 1 / 16 by decide +kernel]; norm_num

theorem entry_ff (tab : Array UInt64) (j : UInt64) (hj : Finite tab[j.toNat]!) :
    ff (Erfc.entry tab j) ∧ fv (Erfc.entry tab j) = ratOfWord tab[j.toNat]! :=
  ofBits_ff _ hj

/-- `Erfc.erfFastMain` on row `i` of `tab` within `T` of `erf x`, when the kernel accepts the row. -/
theorem row_err (hF : FmaNearest) (tab : Array UInt64) (i n J : ℕ) (ε : ℚ) (d : ℕ) (T : ℚ)
    (hok : RowOK tab i n J ε d T) (x : Float) (hx : ff x) (hlo : (i : ℝ) / 16 ≤ fv x)
    (hhi : fv x < ((i : ℝ) + 1) / 16) :
    ff (Erfc.erfFastMain tab x).1 ∧ ff (Erfc.erfFastMain tab x).2 ∧
      |fv (Erfc.erfFastMain tab x).1 + fv (Erfc.erfFastMain tab x).2 - RealErf.erf (fv x)| ≤ T ∧
      |fv (Erfc.erfFastMain tab x).2| ≤ (mainB (rowQ tab i) (1 / 32)).s8L := by
  obtain ⟨hi1, hi2, hfin, hidx, hmain, hn1, hchk, hT⟩ := hok
  obtain ⟨f16, v16, f32, v32, f0625, v0625⟩ := lit_vals
  have hi1r : (1 : ℝ) ≤ i := by exact_mod_cast hi1
  have hi2r : (i : ℝ) ≤ 100 := by exact_mod_cast hi2
  have hx0 : 0 < fv x := by linarith [show (0 : ℝ) < i / 16 by positivity]
  have hx7 : fv x < 7 := by linarith
  -- `16 x` is exact
  have hgx : gx x.toBits ≤ 1024 := gx_le_of_lt _ _ (by
    have : (2 : ℝ) ^ (53 + 1024) / 2 ^ 1074 = 8 := by norm_num
    rw [this]; show |fv x| < 8; rw [abs_of_pos hx0]; linarith)
  obtain ⟨fy, vy⟩ := mul_pow2 16.0 x f16 hx 1078
    (by rw [show (16.0 : Float).toBits = 0x4030000000000000 from rfl]; decide +kernel)
    (by omega) (by omega)
  rw [v16] at vy
  -- `v = ⌊16 x⌋ = i`
  obtain ⟨N, fv1, vv, hN1, hN2⟩ := floorF_spec (16.0 * x) fy (by
    rw [vy, abs_of_pos (by linarith)]; linarith [show (112 : ℝ) < 2 ^ 50 by norm_num])
  have hNi : N = (i : ℤ) := by
    rw [vy] at hN1 hN2
    have h1 : (N : ℝ) < ((i : ℤ) : ℝ) + 1 := by push_cast; linarith
    have h2 : ((i : ℤ) : ℝ) < N + 1 := by push_cast; linarith
    have h1' : N < (i : ℤ) + 1 := by exact_mod_cast h1
    have h2' : (i : ℤ) < N + 1 := by exact_mod_cast h2
    omega
  rw [hNi] at vv
  have vv' : fv (Erfc.floorF (16.0 * x)) = (i : ℝ) := by rw [vv]; push_cast; ring
  have hvU : (Erfc.floorF (16.0 * x)).toUInt64 = UInt64.ofNat i :=
    Library.Numerics.Float64.Sinpi.SinpiFloor.toUInt64_int _ i fv1 vv' hi1 (by omega)
  -- the reduced argument
  have hgrid32 : OnGrid (1 / 32 : ℝ) (gx x.toBits) :=
    onGrid_mono ⟨1, by norm_num⟩ (show gx x.toBits ≤ 1069 by omega)
  have hr1 : Rep (fv x - fv (0.03125 : Float)) := by
    rw [v32]
    refine rep_of_onGrid (onGrid_sub (onGrid_word x.toBits) hgrid32) (by omega) ?_
    have h := word_lt x.toBits
    have : |fv x - 1 / 32| ≤ |fv x| := by
      rw [abs_of_pos hx0, abs_of_pos (by linarith)]; linarith
    have hp : (0 : ℝ) < 2 ^ gx x.toBits / 2 ^ 1074 := by positivity
    calc |fv x - 1 / 32| ≤ |value x.toBits| := this
      _ < 2 ^ (53 + gx x.toBits) / 2 ^ 1074 := h
      _ ≤ (2 ^ 53 + 1) * 2 ^ gx x.toBits / 2 ^ 1074 := by
        rw [pow_add]; gcongr; linarith
  obtain ⟨fw1, vw1⟩ := sub_exact x 0.03125 hx f32
    (by rw [v32, abs_of_pos (by linarith)]; linarith [show (7 : ℝ) ≤ 2 ^ 1022 by norm_num]) hr1
  rw [v32] at vw1
  have hgv : 1022 ≤ gx (Erfc.floorF (16.0 * x)).toBits := gx_ge _ _ (by
    rw [show (2 : ℝ) ^ (52 + 1022) / 2 ^ 1074 = 1 by norm_num]
    show 1 ≤ |fv (Erfc.floorF (16.0 * x))|
    rw [vv', abs_of_pos (by linarith)]; exact hi1r)
  have hgv2 : gx (Erfc.floorF (16.0 * x)).toBits ≤ 1030 := gx_le_of_lt _ _ (by
    rw [show (2 : ℝ) ^ (53 + 1030) / 2 ^ 1074 = 512 by norm_num]
    show |fv (Erfc.floorF (16.0 * x))| < 512
    rw [vv', abs_of_pos (by linarith)]; linarith)
  obtain ⟨fp, vp⟩ := mul_pow2 0.0625 (Erfc.floorF (16.0 * x)) f0625 fv1 1070
    (by rw [show (0.0625 : Float).toBits = 0x3FB0000000000000 from rfl]; decide +kernel)
    (by omega) (by omega)
  rw [v0625, vv'] at vp
  have hw1pos : 1 / 32 ≤ fv (x - 0.03125) := by rw [vw1]; linarith
  have hgw1 : gx (x - 0.03125).toBits ≤ 1070 := by
    have := gx_le_of_lt (x - 0.03125).toBits 1024 (by
      rw [show (2 : ℝ) ^ (53 + 1024) / 2 ^ 1074 = 8 by norm_num]
      show |fv (x - 0.03125)| < 8
      rw [vw1, abs_of_pos (by linarith)]; linarith)
    omega
  have hr2 : Rep (fv (x - 0.03125) - fv (0.0625 * Erfc.floorF (16.0 * x))) := by
    rw [vp]
    refine rep_of_onGrid (onGrid_sub (onGrid_word (x - 0.03125).toBits)
      (onGrid_mono ⟨i, by push_cast; norm_num; ring⟩ hgw1)) (by omega) ?_
    have h := word_lt (x - 0.03125).toBits
    have : |fv (x - 0.03125) - 1 / 16 * i| ≤ |fv (x - 0.03125)| := by
      rw [abs_of_pos (show (0 : ℝ) < fv (x - 0.03125) by linarith), abs_le, vw1]
      constructor <;> linarith
    calc |fv (x - 0.03125) - 1 / 16 * i| ≤ |value (x - 0.03125).toBits| := this
      _ < 2 ^ (53 + gx (x - 0.03125).toBits) / 2 ^ 1074 := h
      _ ≤ (2 ^ 53 + 1) * 2 ^ gx (x - 0.03125).toBits / 2 ^ 1074 := by
        rw [pow_add]; gcongr; linarith
  obtain ⟨fz, vz⟩ := sub_exact (x - 0.03125) (0.0625 * Erfc.floorF (16.0 * x)) fw1 fp
    (by rw [vw1, vp, abs_le]; constructor <;> nlinarith) hr2
  rw [vw1, vp] at vz
  have hzR : |fv (x - 0.03125 - 0.0625 * Erfc.floorF (16.0 * x))| ≤ ((1 / 32 : ℚ) : ℝ) := by
    rw [vz, abs_le]; push_cast; constructor <;> linarith
  -- the coefficients
  have hent : ∀ k < 13, ff (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + UInt64.ofNat k)) ∧
      fv (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + UInt64.ofNat k)) = (rowQ tab i).getD k 0 := by
    intro k hk
    have e := hidx k hk
    obtain ⟨a, b⟩ := entry_ff tab (13 * (UInt64.ofNat i - 1) + UInt64.ofNat k)
      (by rw [e]; exact hfin k hk)
    refine ⟨a, ?_⟩
    rw [b, e, rowQ_getD tab i k hk]
  have h0 : ff (Erfc.entry tab (13 * (UInt64.ofNat i - 1))) ∧
      fv (Erfc.entry tab (13 * (UInt64.ofNat i - 1))) = (rowQ tab i).getD 0 0 := by
    simpa using hent 0 (by norm_num)
  have hc := core_pr hF (Erfc.entry tab (13 * (UInt64.ofNat i - 1)))
    (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 1)) (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 2))
    (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 3)) (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 4))
    (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 5)) (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 6))
    (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 7)) (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 8))
    (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 9))
    (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 10))
    (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 11))
    (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 12))
    (x - 0.03125 - 0.0625 * Erfc.floorF (16.0 * x)) (rowQ tab i) (1 / 32)
    (mainB (rowQ tab i) (1 / 32)) hmain fz hzR h0 (hent 1 (by norm_num)) (hent 2 (by norm_num))
    (hent 3 (by norm_num)) (hent 4 (by norm_num)) (hent 5 (by norm_num)) (hent 6 (by norm_num))
    (hent 7 (by norm_num)) (hent 8 (by norm_num)) (hent 9 (by norm_num)) (hent 10 (by norm_num))
    (hent 11 (by norm_num)) (hent 12 (by norm_num))
  have hs := row_soundI n J (2 * i + 1) 32 ε (rowPoly (rowQ tab i)) d hn1 (by norm_num) hchk _
    (by have := hzR; push_cast at this ⊢; exact this)
  have hcz : (((2 * i + 1 : ℕ) : ℝ) / ((32 : ℕ) : ℝ)) +
      fv (x - 0.03125 - 0.0625 * Erfc.floorF (16.0 * x)) = fv x := by
    rw [vz]; push_cast; ring
  rw [hcz] at hs
  rw [erfFastMain_eq, hvU]
  obtain ⟨c1, c2, ce, -, cl⟩ := hc
  refine ⟨c1, c2, ?_, cl⟩
  have hT' : ((mainB (rowQ tab i) (1 / 32)).s8e : ℝ) +
      (rowBoundI n J (2 * i + 1) 32 ε : ℝ) ≤ T := by exact_mod_cast hT
  have := abs_add_le
    (fv (core (Erfc.entry tab (13 * (UInt64.ofNat i - 1)))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 1))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 2))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 3))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 4))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 5))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 6))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 7))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 8))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 9))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 10))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 11))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 12))
      (x - 0.03125 - 0.0625 * Erfc.floorF (16.0 * x))).1 +
      fv (core (Erfc.entry tab (13 * (UInt64.ofNat i - 1)))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 1))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 2))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 3))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 4))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 5))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 6))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 7))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 8))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 9))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 10))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 11))
      (Erfc.entry tab (13 * (UInt64.ofNat i - 1) + 12))
      (x - 0.03125 - 0.0625 * Erfc.floorF (16.0 * x))).2 -
      eval (rowPoly (rowQ tab i)) (fv (x - 0.03125 - 0.0625 * Erfc.floorF (16.0 * x))))
    (eval (rowPoly (rowQ tab i)) (fv (x - 0.03125 - 0.0625 * Erfc.floorF (16.0 * x))) -
      RealErf.erf (fv x))
  rw [sub_add_sub_cancel] at this
  linarith

#print axioms row_err

end Library.Numerics.Float64.Erfc.ErfcFastRow
