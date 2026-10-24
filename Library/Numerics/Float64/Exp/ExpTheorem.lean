import Library.Numerics.Float64.Exp.ExpFarRange
import LeanExe.ProofKit.F64Magnitude

/-!
The accuracy theorem for `Exp.exp`.  For every finite binary64 input `a`, the result is a
nonnegative word, possibly positive infinity, within one representable step of the nonnegative
nearest-even rounding of the real `exp a`.  The exceptional inputs give the results of IEEE 754:
`exp (±0) = 1`, `exp (+∞) = +∞`, `exp (-∞) = +0`, and the canonical NaN for a NaN.
-/

namespace Library.Numerics.Float64.Exp.ExpTheorem
open CodeLib.IEEE64
open LeanExe.ProofKit F64NearestNonnegative F64Magnitude

set_option exponentiation.threshold 4096

/-- From exponent field 1033 on, the input has magnitude at least 1024. -/
theorem large_magnitude (x : UInt64) (he : 1033 ≤ Wasm.IEEE64.exponent x) : 1024 ≤ |value x| := by
  by_contra h
  have hb := ExpBranches.large_boundary
  have hlt : |value x| < |value (F64ExponentBounds.boundary 1033)| := by
    rw [hb, abs_of_pos (by norm_num : (0 : ℝ) < 1024)]
    exact lt_of_not_ge h
  have := F64ExponentBounds.exponent_lt_of_magnitude_lt x 1033 (by decide) hlt
  omega

private theorem saturated_guard (a : UInt64) (hlo : 1033 ≤ a.toNat) (hhi : a.toNat < 2047) :
    a - 969 ≥ (63 : UInt64) ∧ ¬ a - 969 ≥ (0x80000000 : UInt64) ∧ a ≥ (0x409 : UInt64) ∧
      ¬ a ≥ (0x7ff : UInt64) := by
  have hs : (969 : UInt64) ≤ a := UInt64.le_iff_toNat_le.mpr (by change 969 ≤ a.toNat; omega)
  have hsub : (a - 969).toNat = a.toNat - 969 := UInt64.toNat_sub_of_le _ _ hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply UInt64.le_iff_toNat_le.mpr
    rw [hsub]
    change 63 ≤ a.toNat - 969
    omega
  · intro h
    have hn := UInt64.le_iff_toNat_le.mp h
    rw [hsub] at hn
    change 0x80000000 ≤ a.toNat - 969 at hn
    omega
  · apply UInt64.le_iff_toNat_le.mpr
    change 0x409 ≤ a.toNat
    omega
  · intro h
    have hn := UInt64.le_iff_toNat_le.mp h
    change 0x7ff ≤ a.toNat at hn
    omega

theorem saturated_selected (tab : Array UInt64) (x : Float)
    (he : 1033 ≤ Wasm.IEEE64.exponent x.toBits) (hf : Wasm.IEEE64.exponent x.toBits < 2047) :
    Exp.expWith tab x = if x.toBits >>> 63 == 1 then
        Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000
      else Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000 := by
  obtain ⟨hg1, hg2, hg3, hg4⟩ := saturated_guard (ExpBranches.exponentWord x.toBits)
    (by rw [ExpBranches.exponent_word_spec]; exact he)
    (by rw [ExpBranches.exponent_word_spec]; exact hf)
  have hninf : ¬ (x.toBits == 0xFFF0000000000000) = true := by
    intro h
    have heq : x.toBits = 0xFFF0000000000000 := by simpa using h
    rw [heq] at hf
    exact absurd hf (by decide)
  have hc : (0x408 : UInt64) - 0x3C9 = 63 := by decide
  simp only [Exp.expWith, ExpBranches.exponentWord, hc] at hg1 hg2 hg3 hg4 ⊢
  rw [ite_eq_left hg1, ite_eq_right hg2, ite_eq_left hg3, ite_eq_right hninf, ite_eq_right hg4]

theorem underflow_product :
    (Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000).toBits = 0 := by
  rw [F64Bits.toBits_mul, F64Bits.toBits_ofBits]
  decide +kernel

theorem overflow_product :
    (Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000).toBits =
      0x7FF0000000000000 := by
  rw [F64Bits.toBits_mul, F64Bits.toBits_ofBits]
  decide +kernel

/-- From magnitude 1024 on, `Exp.exp` gives positive infinity for positive inputs and positive
zero for negative ones. -/
theorem saturated_bits (x : Float) (hxf : Finite x.toBits)
    (he : 1033 ≤ Wasm.IEEE64.exponent x.toBits) :
    (Exp.exp x).toBits = if value x.toBits < 0 then 0 else 0x7FF0000000000000 := by
  have hf : Wasm.IEEE64.exponent x.toBits < 2047 := by
    have h := hxf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
    simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq, show Wasm.IEEE64.exponent x.toBits ≠ 0 by
      omega, ite_false]
    positivity
  have hsign : (x.toBits >>> 63 == 1) = Wasm.IEEE64.sign x.toBits := by
    have hlt := x.toBits.toNat_lt
    simp only [Wasm.IEEE64.sign]
    by_cases h : 2 ^ 63 ≤ x.toBits.toNat
    · rw [decide_eq_true h]
      apply beq_iff_eq.mpr
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_shiftRight]
      change x.toBits.toNat >>> 63 = 1
      rw [Nat.shiftRight_eq_div_pow]
      omega
    · rw [decide_eq_false h]
      apply beq_eq_false_iff_ne.mpr
      intro heq
      have := congrArg UInt64.toNat heq
      rw [UInt64.toNat_shiftRight] at this
      change x.toBits.toNat >>> 63 = 1 at this
      rw [Nat.shiftRight_eq_div_pow] at this
      omega
  rw [Exp.exp, saturated_selected _ x he hf, hsign]
  by_cases hs : Wasm.IEEE64.sign x.toBits = true
  · rw [ite_eq_left hs, underflow_product, ite_eq_left ((sign_value _ hmag).mp hs)]
  · have hs' : ¬ value x.toBits < 0 := fun h => hs ((sign_value _ hmag).mpr h)
    rw [ite_eq_right hs, overflow_product, ite_eq_right hs']

private theorem nonfinite_guard (a : UInt64) (ha : a.toNat = 2047) :
    a - 969 ≥ (63 : UInt64) ∧ ¬ a - 969 ≥ (0x80000000 : UInt64) ∧ a ≥ (0x409 : UInt64) ∧
      a ≥ (0x7ff : UInt64) := by
  have hs : (969 : UInt64) ≤ a := UInt64.le_iff_toNat_le.mpr (by change 969 ≤ a.toNat; omega)
  have hsub : (a - 969).toNat = a.toNat - 969 := UInt64.toNat_sub_of_le _ _ hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply UInt64.le_iff_toNat_le.mpr
    rw [hsub]
    change 63 ≤ a.toNat - 969
    omega
  · intro h
    have hn := UInt64.le_iff_toNat_le.mp h
    rw [hsub] at hn
    change 0x80000000 ≤ a.toNat - 969 at hn
    omega
  · apply UInt64.le_iff_toNat_le.mpr
    change 0x409 ≤ a.toNat
    omega
  · apply UInt64.le_iff_toNat_le.mpr
    change 0x7ff ≤ a.toNat
    omega

/-- An infinity or NaN input: `-∞` gives `+0`, and any other gives `1 + x`. -/
theorem nonfinite_selected (tab : Array UInt64) (x : Float)
    (he : Wasm.IEEE64.exponent x.toBits = 2047) :
    Exp.expWith tab x = if x.toBits == 0xFFF0000000000000 then 0.0 else 1.0 + x := by
  obtain ⟨hg1, hg2, hg3, hg4⟩ := nonfinite_guard (ExpBranches.exponentWord x.toBits)
    (by rw [ExpBranches.exponent_word_spec]; exact he)
  have hc : (0x408 : UInt64) - 0x3C9 = 63 := by decide
  simp only [Exp.expWith, ExpBranches.exponentWord, hc] at hg1 hg2 hg3 hg4 ⊢
  rw [ite_eq_left hg1, ite_eq_right hg2, ite_eq_left hg3]
  by_cases h : (x.toBits == 0xFFF0000000000000) = true
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_left hg4]

theorem exp_pos_infinity :
    (Exp.exp (Float.ofBits 0x7FF0000000000000)).toBits = 0x7FF0000000000000 := by
  have hb : (Float.ofBits 0x7FF0000000000000).toBits = 0x7FF0000000000000 := by
    rw [F64Bits.toBits_ofBits]
    decide +kernel
  rw [Exp.exp, nonfinite_selected _ _ (by rw [hb]; decide +kernel), hb,
    ite_eq_right (by decide), ExpTinyError.float_result_bits, hb]
  decide +kernel

theorem exp_neg_infinity : (Exp.exp (Float.ofBits 0xFFF0000000000000)).toBits = 0 := by
  have hb : (Float.ofBits 0xFFF0000000000000).toBits = 0xFFF0000000000000 := by
    rw [F64Bits.toBits_ofBits]
    decide +kernel
  rw [Exp.exp, nonfinite_selected _ _ (by rw [hb]; decide +kernel), hb, ite_eq_left (by decide)]
  rfl

theorem exp_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Exp.exp x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hc := F64Bits.toBits_canonical x
  rw [ite_eq_left h] at hc
  rw [Exp.exp, nonfinite_selected _ _ (by rw [← hc]; decide +kernel), ← hc,
    ite_eq_right (by decide), ExpTinyError.float_result_bits, ← hc]
  decide +kernel

theorem exp_pos_zero : (Exp.exp (Float.ofBits 0)).toBits = 0x3FF0000000000000 := by
  have hb : (Float.ofBits 0).toBits = 0 := by
    rw [F64Bits.toBits_ofBits]
    decide +kernel
  rw [Exp.exp, ExpBranches.tiny_selected _ _ (by rw [hb]; decide +kernel),
    ExpTinyError.float_result_bits, hb]
  decide +kernel

theorem exp_neg_zero :
    (Exp.exp (Float.ofBits 0x8000000000000000)).toBits = 0x3FF0000000000000 := by
  have hb : (Float.ofBits 0x8000000000000000).toBits = 0x8000000000000000 := by
    rw [F64Bits.toBits_ofBits]
    decide +kernel
  rw [Exp.exp, ExpBranches.tiny_selected _ _ (by rw [hb]; decide +kernel),
    ExpTinyError.float_result_bits, hb]
  decide +kernel

/-- Positive zero lies within one step of the reference of a positive number below `2 ^ -1100`. -/
theorem zero_one_step (E : ℝ) (hE : 0 < E) (hEt : E ≤ 1 / (2 : ℝ) ^ 1100) :
    (0 : UInt64).toNat ≤ (F64PositiveRounding.roundNearestEven E).toNat + 1 ∧
      (F64PositiveRounding.roundNearestEven E).toNat ≤ (0 : UInt64).toNat + 1 := by
  have hbnd : value (UInt64.ofNat (2 * 2 ^ 52)) = (2 : ℝ) ^ (-1021 : Int) :=
    F64NearestBinade.boundary_power 2 (-1021) (by norm_num) (by norm_num) (by norm_num)
  have h1 : (1 : ℝ) / 2 ^ 1100 ≤ (2 : ℝ) ^ (-1021 : Int) := by norm_num
  have h2 : (1 : ℝ) / 2 ^ 1100 < 3 * ((2 : ℝ) ^ (0 - 1) / (2 : ℝ) ^ 1074) / 2 := by norm_num
  refine F64FullStep.one_step_binades E 0 0 2 (by norm_num) (by norm_num)
    (by rw [value_zero_boundary]; exact hE.le) (fun _ => by rw [hbnd]; exact hEt.trans h1)
    (by decide) (by rw [value_zero_boundary, value_zero])
    (by rw [hbnd, value_zero]; positivity) ?_
  rw [value_zero, zero_sub, abs_neg, abs_of_pos hE]
  linarith

/-- The accuracy theorem: for every finite input, `Exp.exp` returns a nonnegative word, possibly
positive infinity, within one representable step of the nonnegative nearest-even rounding of
`exp a`. -/
theorem exp_one_step (x : Float) (hxf : Finite x.toBits) :
    (Exp.exp x).toBits.toNat ≤ 0x7FF0000000000000 ∧
      (Exp.exp x).toBits.toNat ≤
        (F64PositiveRounding.roundNearestEven (Real.exp (value x.toBits))).toNat + 1 ∧
      (F64PositiveRounding.roundNearestEven (Real.exp (value x.toBits))).toNat ≤
        (Exp.exp x).toBits.toNat + 1 := by
  have hl : limit = 0x7FF0000000000000 := rfl
  have hf : Wasm.IEEE64.exponent x.toBits < 2047 := by
    have h := hxf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  rcases (show Wasm.IEEE64.exponent x.toBits < 1032 ∨ Wasm.IEEE64.exponent x.toBits = 1032 ∨
      1033 ≤ Wasm.IEEE64.exponent x.toBits by omega) with he | he | he
  · have hx : |value x.toBits| < 512 := by
      have h := magnitude_lt x.toBits 1032 9 (by norm_num) (by norm_num) he
      norm_num at h
      exact h
    obtain ⟨_, h1, h2⟩ := ExpBranches.exp_small_one_step x hxf hx
    have hr : (F64PositiveRounding.roundNearestEven (Real.exp (value x.toBits))).toNat < limit := by
      rw [F64PositiveRounding.reference_finite _ (ExpBranches.exp_small_below_overflow _ hx.le)]
      exact (F64NearestEven.roundNearestEven_spec _).1.1
    refine ⟨?_, h1, h2⟩
    rw [← hl]
    omega
  · have hlo : 512 ≤ |value x.toBits| := by
      have h := magnitude_ge x.toBits 1032 9 (by norm_num) (by norm_num) (by norm_num) he.ge
      norm_num at h
      exact h
    have hhi : |value x.toBits| < 1024 := by
      have h := magnitude_lt x.toBits 1033 10 (by norm_num) (by norm_num) (by omega)
      norm_num at h
      exact h
    by_cases hpos : 0 ≤ value x.toBits
    · rw [abs_of_nonneg hpos] at hlo hhi
      by_cases h768 : value x.toBits ≤ 768
      · obtain ⟨h0, h1, h2⟩ := ExpSpecialPositive.positive_one_step x hxf
          (by rw [abs_of_nonneg hpos]; exact h768) hlo
        exact ⟨by rw [← hl]; exact h0, h1, h2⟩
      · obtain ⟨hc, ht⟩ := ExpFarRange.far_positive x hxf (by rw [abs_of_nonneg hpos]; exact hhi)
          (le_of_lt (lt_of_not_ge h768))
        rw [hc, F64PositiveRounding.reference_overflow _ ht]
        exact ⟨by decide, Nat.le_succ _, Nat.le_succ _⟩
    · have hneg : value x.toBits < 0 := lt_of_not_ge hpos
      rw [abs_of_neg hneg] at hlo hhi
      by_cases h768 : -768 ≤ value x.toBits
      · obtain ⟨h0, h1, h2⟩ := ExpSpecialNegative.negative_one_step x hxf
          (by rw [abs_of_neg hneg]; linarith) (by linarith)
        exact ⟨by rw [← hl]; exact h0, h1, h2⟩
      · obtain ⟨h0, h1, h2⟩ := ExpFarRange.far_negative x hxf
          (by rw [abs_of_neg hneg]; exact hhi) (by linarith)
        exact ⟨by rw [← hl]; exact h0, h1, h2⟩
  · have hbits := saturated_bits x hxf he
    have hbig := large_magnitude x.toBits he
    by_cases hneg : value x.toBits < 0
    · rw [ite_eq_left hneg] at hbits
      rw [abs_of_neg hneg] at hbig
      rw [hbits]
      obtain ⟨h1, h2⟩ := zero_one_step _ (Real.exp_pos _) (ExpFarRange.exp_le_tiny _ (by linarith))
      exact ⟨by decide, h1, h2⟩
    · rw [ite_eq_right hneg] at hbits
      rw [abs_of_nonneg (not_lt.mp hneg)] at hbig
      rw [hbits, F64PositiveRounding.reference_overflow _
        (ExpFarRange.exp_ge_overflow _ (by linarith))]
      exact ⟨le_refl _, Nat.le_succ _, Nat.le_succ _⟩

open Wasm LeanExe.Pipeline in
/-- A store from which the module's `exp` entry runs, with `heap` the allocator's state: the
allocator invariant holds, the table is a borrowed array at address 4096, and the memory cap is at
most 65,535 pages. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ heap.Borrowed store 4096 Exp.expTable ∧
    store.memoryCap Exp.compiled.module 0 ≤ 65535

open Wasm LeanExe.Pipeline in
/-- The store in which the module starts is ready, with the heap that holds its tables. -/
theorem ready_initial :
    Ready (Verified.initialHeap Exp.compiled.tables) Exp.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, hBor⟩ := Exp.compiled.initial
  have hModule : Exp.compiled.module =
      Verified.compileWith Exp.compiled.program Exp.compiled.tables Exp.compiled.wrappers := rfl
  have hAddress : Verified.tableAddr Exp.compiled.tables 0 = 4096 := by
    simp only [Verified.tableAddr, List.take_zero, List.map_nil, List.sum_nil,
      Nat.mul_zero, Nat.add_zero]
  have hTable : Exp.compiled.tables[0] = Exp.expTable := rfl
  have hBorrowed := hBor 0 (by decide)
  rw [hAddress, hTable] at hBorrowed
  unfold Ready
  rw [hModule]
  exact ⟨hAt, hBorrowed, hCap⟩

open Wasm LeanExe.Pipeline in
/-- A borrowed array stays borrowed through a step that keeps the bytes of every region.  Stated
for any array, so that checking it never evaluates the size of a literal table. -/
theorem borrowed_kept {heap heap' : Heap} {store final : Store Unit} {p : UInt64}
    {ws : Array UInt64} (hp : heap.Borrowed store p ws) (hAt : heap'.At final)
    (hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧ heap'.Region r) :
    heap'.Borrowed final p ws := by
  obtain ⟨hb, hr⟩ := hkeep _ hp.region (by show 0 < 8 * (ws.size + 1); omega)
  exact hp.keepIn hAt hb hr

open Wasm LeanExe.Pipeline in
/-- A call of the module's `exp` entry from a ready store, with the bits of a float `x`: it
returns without a trap the bits of `Exp.exp x` and leaves a ready store, and every region of the
heap before the call keeps its bytes and stays a region. -/
theorem exp_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Exp.compiled.module 5 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Exp.exp x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  obtain ⟨hAt, hTab, hCap⟩ := h
  have htab : ∀ t ∈ [((4096 : UInt64), Exp.expTable)],
      heap.Borrowed store t.1 t.2 ∧ Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨hTab, Apart.nil⟩
  refine (Exp.compiled.exp.implements env store heap [.f64 x.toBits] x hAt trivial htab rfl
    Separate.nil hCap).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Exp.exp x).toBits] := howned
  have hvs : values = [.f64 (Exp.exp x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ⟨hAt', borrowed_kept hTab hAt' hkeep, memoryCap_le_of_caps hcaps hCap⟩,
    hkeep⟩

/-- Function 5 of the module is its export `exp`. -/
theorem exp_export : ({ name := "exp", funcIdx := 5 } : Wasm.Export) ∈ Exp.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled module: its bytes decode to the module, whose function 5
is exported as `exp`, and the store in which the module starts is ready.  A call of that entry
from a ready store returns without a trap a single `f64` whose bits are those of `Exp.exp x`, and
it leaves a ready store in which every region of the heap before the call keeps its bytes.  The
theorem therefore covers every call in a sequence of calls to `exp` from the initial store.  For
finite `x` the bits lie within one representable step of the nonnegative nearest-even rounding of
`exp x`. -/
theorem exp_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Exp.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Exp.compiled.module ∧
      ({ name := "exp", funcIdx := 5 } : Wasm.Export) ∈ Exp.compiled.module.exports ∧
      Ready (Verified.initialHeap Exp.compiled.tables) Exp.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Exp.compiled.module 5 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Exp.exp x).toBits ∧
            (Finite x.toBits →
              w.toNat ≤ 0x7FF0000000000000 ∧
              w.toNat ≤ (F64PositiveRounding.roundNearestEven (Real.exp (value x.toBits))).toNat + 1 ∧
              (F64PositiveRounding.roundNearestEven (Real.exp (value x.toBits))).toNat ≤
                w.toNat + 1) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Exp.compiled.bytes
  refine ⟨bytes, henc, hdec, exp_export, ready_initial,
    fun env heap store x h => (exp_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Exp.exp x).toBits, hv, rfl, exp_one_step x, hrest⟩

#print axioms large_magnitude
#print axioms saturated_selected
#print axioms underflow_product
#print axioms overflow_product
#print axioms saturated_bits
#print axioms nonfinite_selected
#print axioms exp_pos_infinity
#print axioms exp_neg_infinity
#print axioms exp_nan
#print axioms exp_pos_zero
#print axioms exp_neg_zero
#print axioms zero_one_step
#print axioms exp_one_step
#print axioms ready_initial
#print axioms borrowed_kept
#print axioms exp_entry_call
#print axioms exp_export
#print axioms exp_bytes_accuracy

end Library.Numerics.Float64.Exp.ExpTheorem
