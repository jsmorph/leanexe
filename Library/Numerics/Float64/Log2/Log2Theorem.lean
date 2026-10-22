import Library.Numerics.Float64.Log2.Log2Near1
import Library.Numerics.Float64.Log2.Log2Power
import LeanExe.ProofKit.BorrowedKept
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
The accuracy theorem for `Log2.log2`.  For every finite binary64 input with positive value, the
result lies within one representable step of the nearest-even rounding of the real
`Real.logb 2 x = log x / log 2`, by the main path for normal and subnormal arguments and the path
near 1.  The exceptional inputs give the results of IEEE 754: `log2 (±0) = -∞`, `log2 (+∞) = +∞`,
`log2 1 = +0`, and the canonical NaN for a negative argument, negative infinity included, and for
a NaN.  `log2 (2 ^ k)` is exactly `k` for every power of two other than 1, subnormal ones included.
`log2_bytes_accuracy` carries the bound to the decoded bytes of the compiled module and to every
call in a sequence of calls to its export `log2`.
-/

namespace Library.Numerics.Float64.Log2.Log2Theorem
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- `Log2.log2` on the path near 1, arguments from `1 - 0x1.5b51p-5` to below `1 + 0x1.6ab2p-5`
other than 1. -/
theorem near2_within (x : Float) (hlo : 4606800540372828160 ≤ x.toBits.toNat)
    (hhi : x.toBits.toNat < 4607381812656734208) (hne : x.toBits.toNat ≠ 4607182418800017408) :
    F64SignedRounding.WithinSteps 1 (Real.log (value x.toBits) / Real.log 2)
      (Log2.log2 x).toBits := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  rw [Log2.log2, Log2Branches.near_selected _ _ x hlo hhi hne]
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
  obtain ⟨hb1, hb2⟩ := Log2Main.bound2_values
  have hv1 : 2008239 / 2097152 ≤ value x.toBits := by
    rw [← hb1]
    exact (F64PositiveOrder.value_le_iff (by decide) hlt).mpr hlo
  have hv2 : value x.toBits < 1095001 / 1048576 := by
    rw [← hb2]
    exact F64PositiveOrder.value_strict (by decide) hhi
  have hone : value (0x3FF0000000000000 : UInt64) = 1 := (Log2Near1.near2_facts).2.2.2.2.2.2.2.2.2.2.2.2.2
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
  have hcf : Finite (0x3FF0000000000000 : UInt64) := (Log2Near1.near2_constants).2.2.2.2.2.2.2.2.2.2.2.2
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
  -- `2 ^ -53 ≤ |x - 1| ≤ 1/22`
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
  have hρ1 : |value x.toBits - 1| ≤ 1 / 22 := by
    rw [abs_le]
    constructor <;> linarith
  have hrNaN : Wasm.IEEE64.isNaN
      (Wasm.IEEE64.sub x.toBits 0x3FF0000000000000 &&& 0xFFFFFFFF00000000) = false :=
    not_nan_of_finite (F64HighWord.high_finite _ hrf)
  rw [Log2Near1.near2_bits x hrNaN]
  obtain ⟨hresf, hres⟩ := Log2Near1.rest_error _ hrf _ (by rw [hrv]) hρ0 hρ1
    (Real.log (value x.toBits) / Real.log 2)
  have hker := Log2KernelPoly.near2_error (value x.toBits - 1) (by linarith) (by linarith)
  rw [show 1 + (value x.toBits - 1) = value x.toBits by ring] at hker
  rw [hrv] at hres
  have hlow := Library.Numerics.Float64.Log.LogTheorem.log_near_lower (value x.toBits - 1) (by linarith) (by linarith)
  rw [show 1 + (value x.toBits - 1) = value x.toBits by ring] at hlow
  obtain ⟨-, hl2⟩ := Log2KernelPoly.split_bounds
  have hl2pos : (0 : ℝ) < Real.log 2 := by linarith
  have hl2u := Log2CoreStep.log_two_upper
  set ρ := |value x.toBits - 1| with hρdef
  have hρpos : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ0
  have hy : 15 / 16 * ρ / (69315 / 100000) ≤ |Real.log (value x.toBits) / Real.log 2| := by
    rw [abs_div, abs_of_pos hl2pos, le_div_iff₀ hl2pos]
    calc 15 / 16 * ρ / (69315 / 100000) * Real.log 2
        ≤ 15 / 16 * ρ / (69315 / 100000) * (69315 / 100000) :=
          mul_le_mul_of_nonneg_left hl2u (by positivity)
      _ = 15 / 16 * ρ := div_mul_cancel₀ _ (by norm_num)
      _ ≤ _ := hlow
  apply F64RelativeStep.within_one_relative _ _ hresf
  · have h2 : (1 : ℝ) / 2 ^ 1000 ≤ 15 / 16 * (1 / 2 ^ 53) / (69315 / 100000) := by norm_num
    have h3 : 15 / 16 * (1 / 2 ^ 53) / (69315 / 100000) ≤ 15 / 16 * ρ / (69315 / 100000) := by
      gcongr
    linarith
  · have hP : |(value x.toBits - 1) * PolyBound.eval Log2KernelPoly.near2 (value x.toBits - 1) -
        Real.log (value x.toBits) / Real.log 2| ≤ ρ / 2 ^ 61 := hker
    have hu0 : (0 : ℝ) ≤ 1 + unitRoundoff64 := by rw [hu]; norm_num
    have h1 := mul_le_mul_of_nonneg_left (add_le_add_left hP (unitRoundoff64 * ρ / 9)) hu0
    have hb : (1 + unitRoundoff64) * (unitRoundoff64 * ρ / 9 + ρ / 2 ^ 61) ≤
        3 / 8 * unitRoundoff64 * (15 / 16 * ρ / (69315 / 100000)) := by
      rw [hu]
      linarith
    have hm := mul_le_mul_of_nonneg_left hy (by rw [hu]; norm_num : (0 : ℝ) ≤ 3 / 8 * unitRoundoff64)
    linarith

/-- `Log2.log2` on every finite argument with positive value, against `Real.logb 2`. -/
theorem log2_within_one (x : Float) (hf : Finite x.toBits) (hpos : 0 < value x.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.logb 2 (value x.toBits)) (Log2.log2 x).toBits := by
  rw [Real.logb]
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
  have hnz : 0 < x.toBits.toNat := by
    rcases Nat.eq_zero_or_pos x.toBits.toNat with h | h
    · exfalso
      have h0 : Wasm.IEEE64.scaledMagnitude x.toBits = 0 := by
        simp [Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, h]
      omega
    · exact h
  by_cases hsub : x.toBits.toNat < 4503599627370496
  · exact Log2Main.log2_subnormal_within x hnz hsub
  · have he : 1 ≤ Wasm.IEEE64.exponent x.toBits := by
      simp only [Wasm.IEEE64.exponent]
      simp only [Nat.reducePow] at hlt
      omega
    by_cases hnear : 4606800540372828160 ≤ x.toBits.toNat ∧ x.toBits.toNat < 4607381812656734208
    · by_cases hone : x.toBits.toNat = 4607182418800017408
      · have hx1 : x.toBits = 0x3FF0000000000000 := UInt64.toNat_inj.mp (by rw [hone]; rfl)
        have hv1 : value x.toBits = 1 := by
          rw [hx1]
          exact (Log2Near1.near2_facts).2.2.2.2.2.2.2.2.2.2.2.2.2
        rw [hv1, Real.log_one, zero_div, Log2.log2, Log2Branches.one_selected _ _ x hone]
        have h0 : (0.0 : Float).toBits = 0 := rfl
        rw [h0]
        exact F64SignedRounding.within_of_nonneg 1 0 le_rfl 0 (by decide)
          (by rw [F64SignedRounding.positive_reference_zero]; decide)
          (by rw [F64SignedRounding.positive_reference_zero]; decide)
      · exact near2_within x hnear.1 hnear.2 hone
    · exact Log2Main.log2_normal_within x hf hs he (by omega)

theorem log2_one (x : Float) (h : x.toBits = 0x3FF0000000000000) :
    (Log2.log2 x).toBits = 0 := by
  rw [Log2.log2, Log2Branches.one_selected _ _ x (by rw [h]; rfl)]
  rfl

theorem log2_zero (x : Float) (h : x.toBits = 0 ∨ x.toBits = 0x8000000000000000) :
    (Log2.log2 x).toBits = 0xFFF0000000000000 := by
  have hm : x.toBits.toNat % 9223372036854775808 = 0 := by
    rcases h with h | h <;> rw [h] <;> decide
  rw [Log2.log2, Log2Branches.zero_selected _ _ x hm, F64Bits.toBits_div, F64Bits.toBits_neg]
  decide +kernel

theorem log2_pos_infinity (x : Float) (h : x.toBits = 0x7FF0000000000000) :
    (Log2.log2 x).toBits = 0x7FF0000000000000 := by
  rw [Log2.log2, Log2Branches.infinity_selected _ _ x (by rw [h]; rfl), h]

/-- A negative argument other than `-0`, negative infinity included, gives the canonical NaN. -/
theorem log2_negative (x : Float) (hs : Wasm.IEEE64.sign x.toBits = true)
    (hz : x.toBits ≠ 0x8000000000000000) :
    (Log2.log2 x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hge : 9223372036854775808 ≤ x.toBits.toNat := by
    simp only [Wasm.IEEE64.sign, decide_eq_true_eq] at hs
    simpa using hs
  have hne : x.toBits.toNat ≠ 9223372036854775808 := by
    intro h
    exact hz (UInt64.toNat_inj.mp (by rw [h]; rfl))
  rw [Log2.log2, Log2Branches.invalid_selected _ _ x (Or.inl ⟨hge, hne⟩)]
  apply Library.Numerics.Float64.Log.LogBranches.invalid_bits
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

theorem log2_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Log2.log2 x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hlt := x.toBits.toNat_lt
  have hnan : Wasm.IEEE64.exponent x.toBits = 2047 ∧ Wasm.IEEE64.fraction x.toBits ≠ 0 := by
    simp only [Wasm.IEEE64.isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    exact ⟨h.1, h.2⟩
  simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction] at hnan
  simp only [Nat.reducePow] at hlt
  by_cases hs : 9223372036854775808 ≤ x.toBits.toNat
  · rw [Log2.log2, Log2Branches.invalid_selected _ _ x (Or.inl ⟨hs, by omega⟩)]
    exact Library.Numerics.Float64.Log.LogBranches.invalid_bits x (Or.inl h)
  · rw [Log2.log2, Log2Branches.invalid_selected _ _ x (Or.inr ⟨by omega, by omega⟩)]
    exact Library.Numerics.Float64.Log.LogBranches.invalid_bits x (Or.inl h)

open Wasm LeanExe.Pipeline in
/-- A store from which the module's `log2` entry runs, with `heap` the allocator's state: the
allocator invariant holds, the two tables are borrowed arrays at addresses 4096 and 5128, and the
memory cap is at most 65,535 pages. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ heap.Borrowed store 4096 Log2.log2Table ∧
    heap.Borrowed store 5128 Log2.log2Table2 ∧ store.memoryCap Log2.compiled.module 0 ≤ 65535

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- The store in which the module starts is ready, with the heap that holds its tables. -/
theorem ready_initial :
    Ready (Verified.initialHeap Log2.compiled.tables) Log2.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, hBor⟩ := Log2.compiled.initial
  exact ⟨hAt, hBor 0 (by decide), hBor 1 (by decide), hCap⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `log2` entry from a ready store, with the bits of a float `x`: it
returns without a trap the bits of `Log2.log2 x` and leaves a ready store, and every region of the
heap before the call keeps its bytes and stays a region. -/
theorem log2_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Log2.compiled.module 5 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Log2.log2 x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  obtain ⟨hAt, hTab1, hTab2, hCap⟩ := h
  have htab : ∀ t ∈ [((4096 : UInt64), Log2.log2Table), ((5128 : UInt64), Log2.log2Table2)],
      heap.Borrowed store t.1 t.2 ∧ Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with ht | ht <;> subst ht
    · exact ⟨hTab1, Apart.nil⟩
    · exact ⟨hTab2, Apart.nil⟩
  refine (Log2.compiled.log2.implements env store heap [.f64 x.toBits] x hAt trivial htab rfl
    Separate.nil hCap).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Log2.log2 x).toBits] := howned
  have hvs : values = [.f64 (Log2.log2 x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ⟨hAt', BorrowedKept.borrowed_kept hTab1 hAt' hkeep,
    BorrowedKept.borrowed_kept hTab2 hAt' hkeep, memoryCap_le_of_caps hcaps hCap⟩, hkeep⟩

/-- Function 5 of the module is its export `log2`. -/
theorem log2_export :
    ({ name := "log2", funcIdx := 5 } : Wasm.Export) ∈ Log2.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled module: its bytes decode to the module, whose function 5
is exported as `log2`, and the store in which the module starts is ready.  A call of that entry
from a ready store returns without a trap a single `f64` whose bits are those of `Log2.log2 x`,
and it leaves a ready store in which every region of the heap before the call keeps its bytes.
The theorem therefore covers every call in a sequence of calls to `log2` from the initial store.
For finite `x` with positive value the bits lie within one representable step of the nearest-even
rounding of `Real.logb 2 x`. -/
theorem log2_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Log2.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Log2.compiled.module ∧
      ({ name := "log2", funcIdx := 5 } : Wasm.Export) ∈ Log2.compiled.module.exports ∧
      Ready (Verified.initialHeap Log2.compiled.tables) Log2.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Log2.compiled.module 5 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Log2.log2 x).toBits ∧
            (Finite x.toBits → 0 < value x.toBits →
              F64SignedRounding.WithinSteps 1 (Real.logb 2 (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Log2.compiled.bytes
  refine ⟨bytes, henc, hdec, log2_export, ready_initial,
    fun env heap store x h => (log2_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Log2.log2 x).toBits, hv, rfl, log2_within_one x, hrest⟩

#print axioms near2_within
#print axioms log2_within_one
#print axioms log2_one
#print axioms log2_zero
#print axioms log2_pos_infinity
#print axioms log2_negative
#print axioms log2_nan
#print axioms ready_initial
#print axioms log2_entry_call
#print axioms log2_export
#print axioms log2_bytes_accuracy

end Library.Numerics.Float64.Log2.Log2Theorem
