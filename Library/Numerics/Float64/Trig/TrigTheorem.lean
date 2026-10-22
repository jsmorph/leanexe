import Library.Numerics.Float64.Trig.TrigSinCos
import LeanExe.ProofKit.BorrowedKept

/-!
The accuracy theorems for `Trig.sin` and `Trig.cos`.  For every finite binary64 input, the
result lies within one representable step of the nearest-even rounding of the real `sin x` and
`cos x`.  The exceptional inputs give the results of IEEE 754: `sin (±0) = ±0`, `cos (±0) = 1`,
and the canonical NaN for an infinity or a NaN.  `sin_bytes_accuracy` and `cos_bytes_accuracy`
carry the bounds to the decoded bytes of the compiled module and to every call in a sequence of
calls to its exports `sin` and `cos`, which read the tables of `2/π` and `π/2` at addresses 4096
and 4264.
-/

namespace Library.Numerics.Float64.Trig.TrigTheorem
open CodeLib.IEEE64 LeanExe.ProofKit TrigSinCos

/-- The difference of an infinity or a NaN with itself is the canonical NaN. -/
theorem sub_self_nonfinite (w : UInt64) (h : ¬ Finite w) :
    Wasm.IEEE64.sub w w = Wasm.IEEE64.canonicalNaN := by
  have he : Wasm.IEEE64.exponent w = 2047 := by
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite at h
    simpa using h
  obtain ⟨hne, hnf, hns⟩ := F64Sign.fields_negate w
  unfold Wasm.IEEE64.sub Wasm.IEEE64.add
  by_cases hn : Wasm.IEEE64.isNaN w = true
  · simp [hn]
  · have hf0 : Wasm.IEEE64.fraction w = 0 := by
      simp only [Wasm.IEEE64.isNaN, he, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq,
        not_and, not_not] at hn
      exact hn (by decide)
    have hn' : Wasm.IEEE64.isNaN w = false := Bool.eq_false_iff.mpr hn
    have hnn : Wasm.IEEE64.isNaN (Wasm.IEEE64.negate w) = false := by
      rw [F64Sign.isNaN_negate]
      exact hn'
    have hinf : Wasm.IEEE64.isInfinite w = true := by
      simp [Wasm.IEEE64.isInfinite, he, hf0]
    have hninf : Wasm.IEEE64.isInfinite (Wasm.IEEE64.negate w) = true := by
      simp [Wasm.IEEE64.isInfinite, hne, hnf, he, hf0]
    simp only [hn', hnn, Bool.or_false, Bool.false_eq_true, ite_false, hinf, ite_true, hninf,
      Bool.true_and, hns]
    cases Wasm.IEEE64.sign w <;> rfl

theorem high_nonfinite (x : Float) (h : ¬ Finite x.toBits) :
    2146435072 ≤ x.toBits.toNat % 2 ^ 63 / 2 ^ 32 := by
  unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite Wasm.IEEE64.exponent at h
  simp only [bne_iff_ne, ne_eq, not_not] at h
  omega

/-- `sin` of an infinity or a NaN is the canonical NaN. -/
theorem sin_nonfinite (x : Float) (h : ¬ Finite x.toBits) :
    (Trig.sin x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hix := high_word x.toBits
  have he := high_nonfinite x h
  unfold Trig.sin Trig.sinWith
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hix, UInt64.reduceToNat]
  rw [if_neg (by omega), if_pos he, F64Bits.toBits_sub, sub_self_nonfinite _ h]

/-- `cos` of an infinity or a NaN is the canonical NaN. -/
theorem cos_nonfinite (x : Float) (h : ¬ Finite x.toBits) :
    (Trig.cos x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hix := high_word x.toBits
  have he := high_nonfinite x h
  unfold Trig.cos Trig.cosWith
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hix, UInt64.reduceToNat]
  rw [if_neg (by omega), if_pos he, F64Bits.toBits_sub, sub_self_nonfinite _ h]

theorem zero_bits : (Float.ofBits 0).toBits = 0 ∧
    (Float.ofBits 0x8000000000000000).toBits = 0x8000000000000000 := by
  simp only [F64Bits.toBits_ofBits]
  constructor <;> decide

/-- `sin (+0) = +0`. -/
theorem sin_pos_zero : (Trig.sin (Float.ofBits 0)).toBits = 0 := by
  have hb := zero_bits.1
  have hix := high_word (Float.ofBits 0).toBits
  unfold Trig.sin Trig.sinWith
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hix, UInt64.reduceToNat, hb]
  rw [if_pos (by decide), if_pos (by decide), hb]

/-- `sin (-0) = -0`. -/
theorem sin_neg_zero :
    (Trig.sin (Float.ofBits 0x8000000000000000)).toBits = 0x8000000000000000 := by
  have hb := zero_bits.2
  have hix := high_word (Float.ofBits 0x8000000000000000).toBits
  unfold Trig.sin Trig.sinWith
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hix, UInt64.reduceToNat, hb]
  rw [if_pos (by decide), if_pos (by decide), hb]

/-- `cos (+0) = 1`. -/
theorem cos_pos_zero : (Trig.cos (Float.ofBits 0)).toBits = 0x3FF0000000000000 := by
  have hb := zero_bits.1
  have hix := high_word (Float.ofBits 0).toBits
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h1⟩ := TrigKernelWords.const_bits
  unfold Trig.cos Trig.cosWith
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hix, UInt64.reduceToNat, hb]
  rw [if_pos (by decide), if_pos (by decide), h1]
  rfl

/-- `cos (-0) = 1`. -/
theorem cos_neg_zero :
    (Trig.cos (Float.ofBits 0x8000000000000000)).toBits = 0x3FF0000000000000 := by
  have hb := zero_bits.2
  have hix := high_word (Float.ofBits 0x8000000000000000).toBits
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, h1⟩ := TrigKernelWords.const_bits
  unfold Trig.cos Trig.cosWith
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hix, UInt64.reduceToNat, hb]
  rw [if_pos (by decide), if_pos (by decide), h1]
  rfl

open Wasm LeanExe.Pipeline in
/-- A store from which the module's `sin` and `cos` entries run, with `heap` the allocator's
state: the allocator invariant holds, the tables of `2/π` and `π/2` are borrowed arrays at
addresses 4096 and 4264, and the memory cap is at most 65,535 pages. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ heap.Borrowed store 4096 Trig.invPi ∧ heap.Borrowed store 4264 Trig.halfPi ∧
    store.memoryCap Trig.compiled.module 0 ≤ 65535

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- The store in which the module starts is ready, with the heap that holds its tables. -/
theorem ready_initial :
    Ready (Verified.initialHeap Trig.compiled.tables) Trig.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, hBor⟩ := Trig.compiled.initial
  exact ⟨hAt, hBor 0 (by decide), hBor 1 (by decide), hCap⟩

open Wasm LeanExe.Pipeline in
theorem tables_ready {heap : Heap} {store : Store Unit} (h : Ready heap store) :
    ∀ t ∈ [((4096 : UInt64), Trig.invPi), ((4264 : UInt64), Trig.halfPi)],
      heap.Borrowed store t.1 t.2 ∧ Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with ht | ht <;> subst ht
  · exact ⟨h.2.1, Apart.nil⟩
  · exact ⟨h.2.2.1, Apart.nil⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `sin` entry from a ready store, with the bits of a float `x`: it
returns without a trap the bits of `Trig.sin x` and leaves a ready store, and every region of the
heap before the call keeps its bytes and stays a region. -/
theorem sin_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Trig.compiled.module 15 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Trig.sin x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  obtain ⟨hAt, hTab1, hTab2, hCap⟩ := h
  refine (Trig.compiled.sin.implements env store heap [.f64 x.toBits] x hAt trivial
    (tables_ready ⟨hAt, hTab1, hTab2, hCap⟩) rfl Separate.nil hCap).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Trig.sin x).toBits] := howned
  have hvs : values = [.f64 (Trig.sin x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ⟨hAt', BorrowedKept.borrowed_kept hTab1 hAt' hkeep,
    BorrowedKept.borrowed_kept hTab2 hAt' hkeep, memoryCap_le_of_caps hcaps hCap⟩, hkeep⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `cos` entry from a ready store, as `sin_entry_call`. -/
theorem cos_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Trig.compiled.module 16 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Trig.cos x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  obtain ⟨hAt, hTab1, hTab2, hCap⟩ := h
  refine (Trig.compiled.cos.implements env store heap [.f64 x.toBits] x hAt trivial
    (tables_ready ⟨hAt, hTab1, hTab2, hCap⟩) rfl Separate.nil hCap).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Trig.cos x).toBits] := howned
  have hvs : values = [.f64 (Trig.cos x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ⟨hAt', BorrowedKept.borrowed_kept hTab1 hAt' hkeep,
    BorrowedKept.borrowed_kept hTab2 hAt' hkeep, memoryCap_le_of_caps hcaps hCap⟩, hkeep⟩

/-- Function 15 of the module is its export `sin`. -/
theorem sin_export :
    ({ name := "sin", funcIdx := 15 } : Wasm.Export) ∈ Trig.compiled.module.exports := by
  decide +kernel

/-- Function 16 of the module is its export `cos`. -/
theorem cos_export :
    ({ name := "cos", funcIdx := 16 } : Wasm.Export) ∈ Trig.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled module's `sin`: its bytes decode to the module, whose
function 15 is exported as `sin`, and the store in which the module starts is ready.  A call of
that entry from a ready store returns without a trap a single `f64` whose bits are those of
`Trig.sin x`, and it leaves a ready store in which every region of the heap before the call keeps
its bytes.  The theorem therefore covers every call in a sequence of calls to `sin` and `cos` from
the initial store.  For finite `x` the bits lie within one representable step of the nearest-even
rounding of `sin x`. -/
theorem sin_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Trig.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Trig.compiled.module ∧
      ({ name := "sin", funcIdx := 15 } : Wasm.Export) ∈ Trig.compiled.module.exports ∧
      Ready (Verified.initialHeap Trig.compiled.tables) Trig.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Trig.compiled.module 15 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Trig.sin x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 (Real.sin (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Trig.compiled.bytes
  refine ⟨bytes, henc, hdec, sin_export, ready_initial,
    fun env heap store x h => (sin_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Trig.sin x).toBits, hv, rfl, sin_within x, hrest⟩

/-- The accuracy theorem for the compiled module's `cos`, as `sin_bytes_accuracy`, with function
16 and the nearest-even rounding of `cos x`. -/
theorem cos_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Trig.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Trig.compiled.module ∧
      ({ name := "cos", funcIdx := 16 } : Wasm.Export) ∈ Trig.compiled.module.exports ∧
      Ready (Verified.initialHeap Trig.compiled.tables) Trig.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Trig.compiled.module 16 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Trig.cos x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 (Real.cos (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Trig.compiled.bytes
  refine ⟨bytes, henc, hdec, cos_export, ready_initial,
    fun env heap store x h => (cos_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Trig.cos x).toBits, hv, rfl, cos_within x, hrest⟩

#print axioms sub_self_nonfinite
#print axioms sin_nonfinite
#print axioms cos_nonfinite
#print axioms sin_pos_zero
#print axioms sin_neg_zero
#print axioms cos_pos_zero
#print axioms cos_neg_zero
#print axioms ready_initial
#print axioms sin_entry_call
#print axioms cos_entry_call
#print axioms sin_export
#print axioms cos_export
#print axioms sin_bytes_accuracy
#print axioms cos_bytes_accuracy

end Library.Numerics.Float64.Trig.TrigTheorem
