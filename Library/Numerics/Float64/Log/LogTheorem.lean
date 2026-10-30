import Library.Numerics.Float64.Log.LogNear1
import Library.Numerics.Float64.Log.LogMain
import Verified.Call

/-!
The accuracy theorem for `Log.log`.  For every finite binary64 input with positive value, the
result lies within one representable step of the nearest-even rounding of the real `log x`, by the
main path for normal and subnormal arguments and the path near 1.  The exceptional inputs give the
results of IEEE 754: `log (±0) = -∞`, `log (+∞) = +∞`, `log 1 = +0`, and the canonical NaN for a
negative argument, negative infinity included, and for a NaN.  `log_bytes_accuracy` carries the
bound to the decoded bytes of the compiled module and to every call in a sequence of calls to its
export `log`.
-/

namespace Library.Numerics.Float64.Log.LogTheorem
open Verified (Ready)
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- `|log x| ≥ (15/16) |x - 1|` near 1. -/
theorem log_near_lower (R : ℝ) (hlo : -1 / 16 ≤ R) (hhi : R ≤ 1 / 15) :
    15 / 16 * |R| ≤ |Real.log (1 + R)| := by
  have hpos : 0 < 1 + R := by linarith
  rcases le_or_gt 0 R with h | h
  · have h1 := Real.one_sub_inv_le_log_of_pos hpos
    have h2 : 15 / 16 * R ≤ 1 - (1 + R)⁻¹ := by
      rw [show 1 - (1 + R)⁻¹ = R / (1 + R) by field_simp; ring]
      rw [le_div_iff₀ hpos]
      nlinarith
    rw [abs_of_nonneg h, abs_of_nonneg (by linarith)]
    linarith
  · have h1 := Real.log_le_sub_one_of_pos hpos
    rw [abs_of_neg h, abs_of_neg (by linarith)]
    linarith

/-- `Log.log` on the path near 1, arguments from `15/16` to below `1 + 265/4096` other than 1. -/
theorem near1_within (x : Float) (hlo : 4606619468846596096 ≤ x.toBits.toNat)
    (hhi : x.toBits.toNat < 4607473789381378048) (hne : x.toBits.toNat ≠ 4607182418800017408) :
    F64SignedRounding.WithinSteps 1 (Real.log (value x.toBits)) (Log.log x).toBits := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  rw [Log.log, LogBranches.near_selected _ _ x hlo hhi hne, LogNear1.near1_bits,
    LogNear1.near1Word_eq]
  have hlt : x.toBits.toNat < 2 ^ 63 := by simp only [Nat.reducePow]; omega
  have hs : Wasm.IEEE64.sign x.toBits = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]
    exact hlt
  have he : Wasm.IEEE64.exponent x.toBits = 1022 ∨ Wasm.IEEE64.exponent x.toBits = 1023 := by
    simp only [Wasm.IEEE64.exponent]
    omega
  have hxf : Finite x.toBits := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq]
    omega
  obtain ⟨hb1, hb2⟩ := LogMain.bound_values
  have hv1 : 15 / 16 ≤ value x.toBits := by
    rw [← hb1]
    exact (F64PositiveOrder.value_le_iff (by decide) hlt).mpr hlo
  have hv2 : value x.toBits < 1 + 265 / 4096 := by
    rw [← hb2]
    exact F64PositiveOrder.value_strict (by decide) hhi
  have hone : value (0x3FF0000000000000 : UInt64) = 1 := by
    rw [← PolyBound.ratOfWord_cast, (LogNear1.near1_bounds).2.2.2.2.2.2.2.2.2.2.2.2]
    norm_num
  have hvne : value x.toBits ≠ 1 := by
    intro h
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · have := F64PositiveOrder.value_strict (left := x.toBits)
        (right := (0x3FF0000000000000 : UInt64)) (by decide) h1
      rw [hone] at this
      linarith
    · have := F64PositiveOrder.value_strict (left := (0x3FF0000000000000 : UInt64))
        (right := x.toBits) hlt h1
      rw [hone] at this
      linarith
  have hcf : Finite (0x3FF0000000000000 : UInt64) := (LogNear1.near1_constants).2.2.2.2.2.2.2.2.2.2.2.2
  -- `r = x - 1` exactly
  have hgx : (2 : Int) ^ 1021 ∣ Wasm.IEEE64.scaledValue x.toBits := by
    have hne0 : (Wasm.IEEE64.exponent x.toBits == 0) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    simp only [Wasm.IEEE64.scaledValue, hs, Bool.false_eq_true, ite_false,
      Wasm.IEEE64.scaledMagnitude, hne0, ite_false]
    rcases he with h | h <;> rw [h]
    · exact ⟨(2 ^ 52 + Wasm.IEEE64.fraction x.toBits : Nat), by push_cast; ring⟩
    · exact ⟨(2 * (2 ^ 52 + Wasm.IEEE64.fraction x.toBits) : Nat), by push_cast; ring⟩
  have hg1 : (2 : Int) ^ 1021 ∣ Wasm.IEEE64.scaledValue (0x3FF0000000000000 : UInt64) :=
    ⟨2 ^ 53, by decide +kernel⟩
  have hdiff : value x.toBits - value (0x3FF0000000000000 : UInt64) =
      ((Wasm.IEEE64.scaledValue x.toBits - Wasm.IEEE64.scaledValue (0x3FF0000000000000 : UInt64) :
        Int) : ℝ) / 2 ^ 1074 := by
    simp only [value]
    push_cast
    ring
  have hbound : |Wasm.IEEE64.scaledValue x.toBits -
      Wasm.IEEE64.scaledValue (0x3FF0000000000000 : UInt64)| ≤ 2 ^ 53 * 2 ^ 1021 := by
    have h : |((Wasm.IEEE64.scaledValue x.toBits -
        Wasm.IEEE64.scaledValue (0x3FF0000000000000 : UInt64) : Int) : ℝ)| ≤
        ((2 ^ 53 * 2 ^ 1021 : Int) : ℝ) := by
      have heq : ((Wasm.IEEE64.scaledValue x.toBits -
          Wasm.IEEE64.scaledValue (0x3FF0000000000000 : UInt64) : Int) : ℝ) =
          (value x.toBits - value (0x3FF0000000000000 : UInt64)) * 2 ^ 1074 := by
        rw [hdiff]
        field_simp
      rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), hone]
      have h1 : |value x.toBits - 1| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      have h2 : |value x.toBits - 1| * (2 : ℝ) ^ 1074 ≤ 1 * 2 ^ 1074 := by gcongr
      push_cast
      have h3 : (1 : ℝ) * 2 ^ 1074 ≤ 2 ^ 53 * 2 ^ 1021 := by norm_num
      linarith
    exact_mod_cast h
  obtain ⟨hrf, hrv⟩ := F64ErrorTrack.sub_exact_grid _ _ hxf hcf 1021 (by norm_num) hgx hg1 hbound
  rw [hone] at hrv
  -- `2 ^ -53 ≤ |x - 1| ≤ 1/15`
  have hρ0 : 1 / 2 ^ 53 ≤ |value x.toBits - 1| := by
    obtain ⟨m, hm⟩ := dvd_sub hgx hg1
    rw [hm, hone, Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at hdiff
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero, mul_zero, zero_div] at hdiff
      exact hvne (by linarith)
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm0
    rw [hdiff, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1021)]
    rw [le_div_iff₀ (by positivity)]
    have : (1 : ℝ) / 2 ^ 53 * 2 ^ 1074 = 2 ^ 1021 * 1 := by norm_num
    rw [this]
    exact mul_le_mul_of_nonneg_left hm1 (by positivity)
  have hρ1 : |value x.toBits - 1| ≤ 1 / 15 := by
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨hresf, hres⟩ := LogNear1.near1_error _ hrf _ (by rw [hrv]) hρ0 hρ1
    (Real.log (value x.toBits))
  have hker := LogKernelPoly.near1_kernel_error (value x.toBits - 1) (by linarith) (by linarith)
  rw [show 1 + (value x.toBits - 1) = value x.toBits by ring] at hker
  rw [hrv] at hres
  have hlow := log_near_lower (value x.toBits - 1) (by linarith) (by linarith)
  rw [show 1 + (value x.toBits - 1) = value x.toBits by ring] at hlow
  apply F64RelativeStep.within_one_relative _ _ hresf
  · have : (1 : ℝ) / 2 ^ 1000 ≤ 15 / 16 * (1 / 2 ^ 53) := by norm_num
    have h2 := mul_le_mul_of_nonneg_left hρ0 (by norm_num : (0 : ℝ) ≤ 15 / 16)
    linarith
  · set ρ := |value x.toBits - 1|
    have hP : |(value x.toBits - 1) * PolyBound.eval LogKernelPoly.near1Kernel
        (value x.toBits - 1) - Real.log (value x.toBits)| ≤ ρ * ((15 / 16) / 2 ^ 62) := by
      rw [abs_sub_comm]
      exact hker
    have hρpos : 0 ≤ ρ := abs_nonneg _
    have hu0 : (0 : ℝ) ≤ 1 + unitRoundoff64 := by rw [hu]; norm_num
    have h1 := mul_le_mul_of_nonneg_left (add_le_add_left hP (unitRoundoff64 * ρ *
      (1 / 15 + 1 / 13))) hu0
    rw [hu] at h1 hres ⊢
    nlinarith [hlow, hρpos]

/-- `Log.log` on every finite argument with positive value. -/
theorem log_within_one (x : Float) (hf : Finite x.toBits) (hpos : 0 < value x.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.log (value x.toBits)) (Log.log x).toBits := by
  have hmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
    rcases Nat.eq_zero_or_pos (Wasm.IEEE64.scaledMagnitude x.toBits) with h | h
    · exfalso
      have : value x.toBits = 0 := by
        simp only [value, Wasm.IEEE64.scaledValue, h]
        split <;> simp
      linarith
    · exact h
  have hs : Wasm.IEEE64.sign x.toBits = false := by
    cases h : Wasm.IEEE64.sign x.toBits
    · rfl
    · exact absurd ((F64Magnitude.sign_value _ hmag).mp h) (not_lt.mpr hpos.le)
  have hlt : x.toBits.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
    exact hs
  have hfin : Wasm.IEEE64.exponent x.toBits ≠ 2047 := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at hf
    exact hf
  have hnz : 0 < x.toBits.toNat := by
    rcases Nat.eq_zero_or_pos x.toBits.toNat with h | h
    · exfalso
      have h0 : Wasm.IEEE64.scaledMagnitude x.toBits = 0 := by
        simp [Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, h]
      omega
    · exact h
  by_cases hsub : x.toBits.toNat < 4503599627370496
  · exact LogMain.log_subnormal_within x hnz hsub
  · have he : 1 ≤ Wasm.IEEE64.exponent x.toBits := by
      simp only [Wasm.IEEE64.exponent]
      simp only [Nat.reducePow] at hlt
      omega
    by_cases hnear : 4606619468846596096 ≤ x.toBits.toNat ∧ x.toBits.toNat < 4607473789381378048
    · by_cases hone : x.toBits.toNat = 4607182418800017408
      · have hx1 : x.toBits = 0x3FF0000000000000 := UInt64.toNat_inj.mp (by rw [hone]; rfl)
        have hv1 : value x.toBits = 1 := by
          rw [hx1, ← PolyBound.ratOfWord_cast, (LogNear1.near1_bounds).2.2.2.2.2.2.2.2.2.2.2.2]
          norm_num
        rw [hv1, Real.log_one, Log.log, LogBranches.one_selected _ _ x hone]
        have h0 : (0.0 : Float).toBits = 0 := rfl
        rw [h0]
        exact F64SignedRounding.within_of_nonneg 1 0 le_rfl 0 (by decide)
          (by rw [F64SignedRounding.positive_reference_zero]; decide)
          (by rw [F64SignedRounding.positive_reference_zero]; decide)
      · exact near1_within x hnear.1 hnear.2 hone
    · exact LogMain.log_normal_within x hf hs he (by omega)

theorem log_one (x : Float) (h : x.toBits = 0x3FF0000000000000) : (Log.log x).toBits = 0 := by
  rw [Log.log, LogBranches.one_selected _ _ x (by rw [h]; rfl)]
  rfl

theorem log_zero (x : Float) (h : x.toBits = 0 ∨ x.toBits = 0x8000000000000000) :
    (Log.log x).toBits = 0xFFF0000000000000 := by
  have hm : x.toBits.toNat % 9223372036854775808 = 0 := by
    rcases h with h | h <;> rw [h] <;> decide
  rw [Log.log, LogBranches.zero_selected _ _ x hm, F64Bits.toBits_div, F64Bits.toBits_neg]
  decide +kernel

theorem log_pos_infinity (x : Float) (h : x.toBits = 0x7FF0000000000000) :
    (Log.log x).toBits = 0x7FF0000000000000 := by
  rw [Log.log, LogBranches.infinity_selected _ _ x (by rw [h]; rfl), h]

/-- A negative argument other than `-0`, negative infinity included, gives the canonical NaN. -/
theorem log_negative (x : Float) (hs : Wasm.IEEE64.sign x.toBits = true)
    (hz : x.toBits ≠ 0x8000000000000000) :
    (Log.log x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hge : 9223372036854775808 ≤ x.toBits.toNat := by
    simp only [Wasm.IEEE64.sign, decide_eq_true_eq] at hs
    simpa using hs
  have hne : x.toBits.toNat ≠ 9223372036854775808 := by
    intro h
    exact hz (UInt64.toNat_inj.mp (by rw [h]; rfl))
  rw [Log.log, LogBranches.invalid_selected _ _ x (Or.inl ⟨hge, hne⟩)]
  apply LogBranches.invalid_bits
  by_cases he : Wasm.IEEE64.exponent x.toBits = 2047
  · by_cases hfr : Wasm.IEEE64.fraction x.toBits = 0
    · right; right
      apply UInt64.toNat_inj.mp
      have hlt := x.toBits.toNat_lt
      simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction] at he hfr
      simp only [UInt64.reduceToNat]
      simp only [Nat.reducePow] at hlt
      omega
    · left
      simp only [Wasm.IEEE64.isNaN, he, hfr, beq_self_eq_true, bne_iff_ne, ne_eq, not_false_eq_true,
        Bool.and_self, decide_true]
      simpa using hfr
  · right; left
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq]
    exact he

theorem log_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Log.log x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hlt := x.toBits.toNat_lt
  have hnan : Wasm.IEEE64.exponent x.toBits = 2047 ∧ Wasm.IEEE64.fraction x.toBits ≠ 0 := by
    simp only [Wasm.IEEE64.isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    exact ⟨h.1, h.2⟩
  simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction] at hnan
  simp only [Nat.reducePow] at hlt
  by_cases hs : 9223372036854775808 ≤ x.toBits.toNat
  · rw [Log.log, LogBranches.invalid_selected _ _ x (Or.inl ⟨hs, by omega⟩)]
    exact LogBranches.invalid_bits x (Or.inl h)
  · rw [Log.log, LogBranches.invalid_selected _ _ x (Or.inr ⟨by omega, by omega⟩)]
    exact LogBranches.invalid_bits x (Or.inl h)

/-- The store in which the module starts is ready, with the heap that holds its tables. -/
theorem ready_initial :
    Ready Log.compiled.module Log.compiled.tables (Verified.initialHeap Log.compiled.tables)
      Log.compiled.module.initialStore :=
  Verified.Ready.initial rfl Log.compiled.initial

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- A call of the module's `log` entry from a ready store, with the bits of a float `x`: it
returns without a trap the bits of `Log.log x` and leaves a ready store, and every region of the
heap before the call keeps its bytes and stays a region. -/
theorem log_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready Log.compiled.module Log.compiled.tables heap store) :
    Runs false env Log.compiled.module 5 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Log.log x).toBits] ∧ ∃ heap' : Heap,
        Ready Log.compiled.module Log.compiled.tables heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r :=
  (Verified.ImplementsTables.call Log.compiled.log.implements Log.compiled.tables
    (Verified.tables_at [0, 1] (by decide) rfl)
    env heap store [.f64 x.toBits] x h rfl rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by simpa [Scalar.values] using congrArg List.reverse hv, heap', hR, hkeep⟩

/-- Function 5 of the module is its export `log`. -/
theorem log_export : ({ name := "log", funcIdx := 5 } : Wasm.Export) ∈ Log.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled module: its bytes decode to the module, whose function 5
is exported as `log`, and the store in which the module starts is ready.  A call of that entry
from a ready store returns without a trap a single `f64` whose bits are those of `Log.log x`, and
it leaves a ready store in which every region of the heap before the call keeps its bytes.  The
theorem therefore covers every call in a sequence of calls to `log` from the initial store.  For
finite `x` with positive value the bits lie within one representable step of the nearest-even
rounding of `log x`. -/
theorem log_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Log.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Log.compiled.module ∧
      ({ name := "log", funcIdx := 5 } : Wasm.Export) ∈ Log.compiled.module.exports ∧
      Ready Log.compiled.module Log.compiled.tables
        (Verified.initialHeap Log.compiled.tables) Log.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready Log.compiled.module Log.compiled.tables heap store →
        Wasm.Runs false env Log.compiled.module 5 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Log.log x).toBits ∧
            (Finite x.toBits → 0 < value x.toBits →
              F64SignedRounding.WithinSteps 1 (Real.log (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap,
              Ready Log.compiled.module Log.compiled.tables heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Log.compiled.bytes
  refine ⟨bytes, henc, hdec, log_export, ready_initial,
    fun env heap store x h => (log_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Log.log x).toBits, hv, rfl, log_within_one x, hrest⟩

#print axioms log_near_lower
#print axioms near1_within
#print axioms log_within_one
#print axioms log_one
#print axioms log_zero
#print axioms log_pos_infinity
#print axioms log_negative
#print axioms log_nan
#print axioms ready_initial
#print axioms log_entry_call
#print axioms log_export
#print axioms log_bytes_accuracy

end Library.Numerics.Float64.Log.LogTheorem
