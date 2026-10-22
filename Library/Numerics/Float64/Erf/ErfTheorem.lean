import Library.Numerics.Float64.Erf.ErfOdd
import LeanExe.ProofKit.BorrowedKept

/-!
The accuracy theorem for `Erf.erf`.  For every finite binary64 input the result lies within one
representable step of the signed nearest-even rounding of the real `erf x` (`erf_within_one`, from
`ErfOdd.erfWith_within_one`).  The exceptional inputs give `erf (±0) = ±0`, `erf (±∞) = ±1`, and
the canonical NaN for a NaN.  `erf_bytes_accuracy` carries the bound to the decoded bytes of the
compiled module and to every call in a sequence of calls to its export `erf`, function 10, whose
store borrows `Exp.expTable` at address 4096.  `erf_module_accuracy` collects the byte theorems of
the module for the file theorem module `ErfFile`.
-/

namespace Library.Numerics.Float64.Erf.ErfTheorem
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- One step for `Erf.erf x` for every finite `x`. -/
theorem erf_within_one (x : Float) (hxf : Finite x.toBits) :
    F64SignedRounding.WithinSteps 1 (RealErf.erf (value x.toBits)) (Erf.erf x).toBits :=
  ErfOdd.erfWith_within_one x hxf

theorem erf_pos_zero : (Erf.erf (Float.ofBits 0)).toBits = 0 := by
  have h : (Float.ofBits 0).toBits = 0 := by rw [F64Bits.toBits_ofBits]; decide
  have n8 : Wasm.IEEE64.isNaN 0x3FF06EBA8214DB69 = false := by decide
  simp only [Erf.erf, Erf.erfWith, h, F64Bits.toBits_div, F64Bits.toBits_add, F64Bits.toBits_mul,
    F64Bits.toBits_ofBits, n8, ErfPositive.eight_bits, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem erf_neg_zero :
    (Erf.erf (Float.ofBits 0x8000000000000000)).toBits = 0x8000000000000000 := by
  have h : (Float.ofBits 0x8000000000000000).toBits = 0x8000000000000000 := by
    rw [F64Bits.toBits_ofBits]; decide
  have n8 : Wasm.IEEE64.isNaN 0x3FF06EBA8214DB69 = false := by decide
  simp only [Erf.erf, Erf.erfWith, h, F64Bits.toBits_div, F64Bits.toBits_add, F64Bits.toBits_mul,
    F64Bits.toBits_ofBits, n8, ErfPositive.eight_bits, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem erf_pos_infinity :
    (Erf.erf (Float.ofBits 0x7FF0000000000000)).toBits = 0x3FF0000000000000 := by
  have h : (Float.ofBits 0x7FF0000000000000).toBits = 0x7FF0000000000000 := by
    rw [F64Bits.toBits_ofBits]; decide
  simp only [Erf.erf, Erf.erfWith, h, F64Bits.toBits_div, F64Bits.toBits_add,
    ErfPositive.one_bits, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

theorem erf_neg_infinity :
    (Erf.erf (Float.ofBits 0xFFF0000000000000)).toBits = 0xBFF0000000000000 := by
  have h : (Float.ofBits 0xFFF0000000000000).toBits = 0xFFF0000000000000 := by
    rw [F64Bits.toBits_ofBits]; decide
  have hm : (-1.0 : Float).toBits = 0xBFF0000000000000 := by
    rw [F64Bits.toBits_neg, ErfPositive.one_bits]; decide +kernel
  simp only [Erf.erf, Erf.erfWith, h, F64Bits.toBits_div, F64Bits.toBits_add, hm,
    ErfPositive.one_bits, Bool.false_eq_true, ↓reduceIte]
  decide +kernel

/-- A NaN gives the canonical NaN. -/
theorem erf_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Erf.erf x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hlt := x.toBits.toNat_lt
  have hsz : UInt64.size = 18446744073709551616 := rfl
  have he : Wasm.IEEE64.exponent x.toBits = 2047 := by
    simp only [Wasm.IEEE64.isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    exact h.1
  have hix : (0x7ff00000 : UInt64) ≤ x.toBits >>> 32 &&& 0x7fffffff := by
    rw [UInt64.le_iff_toNat_le, ← ErfBranches.ix, ErfBranches.ix_toNat]
    simp only [Wasm.IEEE64.exponent] at he
    simp only [UInt64.reduceToNat]
    omega
  simp only [Erf.erf, Erf.erfWith, ge_iff_le, hix, ↓reduceIte, F64Bits.toBits_add,
    F64Bits.toBits_div]
  have hd : Wasm.IEEE64.div (1.0 : Float).toBits x.toBits = Wasm.IEEE64.canonicalNaN := by
    simp [Wasm.IEEE64.div, h]
  rw [hd]
  split <;> simp [Wasm.IEEE64.add, Wasm.IEEE64.isNaN, Wasm.IEEE64.canonicalNaN,
    Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]

open Wasm LeanExe.Pipeline in
/-- A store from which the module's entries run, with `heap` the allocator's state: the allocator
invariant holds, `Exp.expTable` is a borrowed array at address 4096, and the memory cap is at most
65,535 pages. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ heap.Borrowed store 4096 Exp.expTable ∧
    store.memoryCap Erf.compiled.module 0 ≤ 65535

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- The store in which the module starts is ready, with the heap that holds its table. -/
theorem ready_initial :
    Ready (Verified.initialHeap Erf.compiled.tables) Erf.compiled.module.initialStore := by
  obtain ⟨hAt, hCap, hBor⟩ := Erf.compiled.initial
  exact ⟨hAt, hBor 0 (by decide), hCap⟩

open Wasm LeanExe.Pipeline in
/-- A call of the module's `erf` entry from a ready store, with the bits of a float `x`: it
returns without a trap the bits of `Erf.erf x` and leaves a ready store, and every region of the
heap before the call keeps its bytes and stays a region. -/
theorem erf_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready heap store) :
    Runs false env Erf.compiled.module 10 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Erf.erf x).toBits] ∧ ∃ heap' : Heap, Ready heap' final ∧
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
  refine (Erf.compiled.erf.implements env store heap [.f64 x.toBits] x hAt trivial htab rfl
    Separate.nil hCap).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hv : values.reverse = [.f64 (Erf.erf x).toBits] := howned
  have hvs : values = [.f64 (Erf.erf x).toBits] := by
    have := congrArg List.reverse hv
    simpa using this
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨hvs, heap', ⟨hAt', BorrowedKept.borrowed_kept hTab hAt' hkeep,
    memoryCap_le_of_caps hcaps hCap⟩, hkeep⟩

/-- Function 11 of the module is its export `erf`. -/
theorem erf_export : ({ name := "erf", funcIdx := 10 } : Wasm.Export) ∈ Erf.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled module's `erf`: its bytes decode to the module, whose
function 10 is exported as `erf`, and the store in which the module starts is ready.  A call of
that entry from a ready store returns without a trap a single `f64` whose bits are those of
`Erf.erf x`, and it leaves a ready store in which every region of the heap before the call keeps
its bytes.  The theorem therefore covers every call in a sequence of calls from the initial store.
For finite `x` the bits lie within one representable step of the nearest-even rounding of
`erf x`. -/
theorem erf_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Erf.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Erf.compiled.module ∧
      ({ name := "erf", funcIdx := 10 } : Wasm.Export) ∈ Erf.compiled.module.exports ∧
      Ready (Verified.initialHeap Erf.compiled.tables) Erf.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready heap store →
        Wasm.Runs false env Erf.compiled.module 10 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Erf.erf x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 (RealErf.erf (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap, Ready heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Erf.compiled.bytes
  refine ⟨bytes, henc, hdec, erf_export, ready_initial,
    fun env heap store x h => (erf_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Erf.erf x).toBits, hv, rfl, erf_within_one x, hrest⟩

/-- The byte theorems of the module, for the file theorem module. -/
theorem erf_module_accuracy :
    ∃ bytes, Wasm.Encoding.encode Erf.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Erf.compiled.module := by
  obtain ⟨bytes, henc, hdec, _⟩ := erf_bytes_accuracy
  exact ⟨bytes, henc, hdec⟩

#print axioms erf_within_one
#print axioms erf_pos_zero
#print axioms erf_neg_zero
#print axioms erf_pos_infinity
#print axioms erf_neg_infinity
#print axioms erf_nan
#print axioms ready_initial
#print axioms erf_entry_call
#print axioms erf_export
#print axioms erf_bytes_accuracy
#print axioms erf_module_accuracy

end Library.Numerics.Float64.Erf.ErfTheorem
