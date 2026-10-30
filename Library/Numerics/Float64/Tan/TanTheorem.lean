import Library.Numerics.Float64.Tan.TanWith
import Verified.Call

/-!
The accuracy theorem for `Tan.tan`.  For every finite binary64 input, the result lies within one
representable step of the nearest-even rounding of the real `tan x`.  The exceptional inputs give
the results of IEEE 754: `tan (±0) = ±0`, and the canonical NaN for an infinity or a NaN.
`tan_bytes_accuracy` carries the bound to the decoded bytes of the compiled module and to every
call in a sequence of calls to its export `tan`, which reads the tables of `2/π` and `π/2` at
addresses 4096 and 4264.
-/

namespace Library.Numerics.Float64.Tan.TanTheorem
open Verified (Ready)
open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Trig.TrigSinCos TanWith

/-- `tan` of an infinity or a NaN is the canonical NaN. -/
theorem tan_nonfinite (x : Float) (h : ¬ Finite x.toBits) :
    (Tan.tan x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hix := high_word x.toBits
  have he := Library.Numerics.Float64.Trig.TrigTheorem.high_nonfinite x h
  unfold Tan.tan Tan.tanWith
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hix, UInt64.reduceToNat]
  rw [if_neg (by omega), if_pos he, F64Bits.toBits_sub, Library.Numerics.Float64.Trig.TrigTheorem.sub_self_nonfinite _ h]

/-- `tan (+0) = +0`. -/
theorem tan_pos_zero : (Tan.tan (Float.ofBits 0)).toBits = 0 := by
  have hb := Library.Numerics.Float64.Trig.TrigTheorem.zero_bits.1
  have hix := high_word (Float.ofBits 0).toBits
  have hu : (Float.ofBits 0).toUInt64 = 0 :=
    toUInt64_small _ (by rw [hb]; unfold CodeLib.IEEE64.Finite; decide)
      (by rw [hb, TanBigWords.value_zero, abs_zero]; norm_num)
  unfold Tan.tan Tan.tanWith
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hix, UInt64.reduceToNat, hb, hu]
  rw [if_pos (by decide), if_pos (by decide), hb]

/-- `tan (-0) = -0`. -/
theorem tan_neg_zero :
    (Tan.tan (Float.ofBits 0x8000000000000000)).toBits = 0x8000000000000000 := by
  have hb := Library.Numerics.Float64.Trig.TrigTheorem.zero_bits.2
  have hix := high_word (Float.ofBits 0x8000000000000000).toBits
  have hu : (Float.ofBits 0x8000000000000000).toUInt64 = 0 :=
    toUInt64_small _ (by rw [hb]; unfold CodeLib.IEEE64.Finite; decide)
      (by rw [hb, Library.Numerics.Float64.Trig.TrigSmall.value_of_scaled, show Wasm.IEEE64.scaledValue 0x8000000000000000 = 0
        by decide +kernel]; norm_num)
  unfold Tan.tan Tan.tanWith
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, hix, UInt64.reduceToNat, hb, hu]
  rw [if_pos (by decide), if_pos (by decide), hb]

/-- The store in which the module starts is ready, with the heap that holds its tables. -/
theorem ready_initial :
    Ready Tan.compiled.module Tan.compiled.tables (Verified.initialHeap Tan.compiled.tables)
      Tan.compiled.module.initialStore :=
  Verified.Ready.initial rfl Tan.compiled.initial

set_option maxRecDepth 100000 in
open Wasm LeanExe.Pipeline in
/-- A call of the module's `tan` entry from a ready store, with the bits of a float `x`: it
returns without a trap the bits of `Tan.tan x` and leaves a ready store, and every region of the
heap before the call keeps its bytes and stays a region. -/
theorem tan_entry_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (x : Float)
    (h : Ready Tan.compiled.module Tan.compiled.tables heap store) :
    Runs false env Tan.compiled.module 13 store [.f64 x.toBits] fun final values =>
      values = [.f64 (Tan.tan x).toBits] ∧ ∃ heap' : Heap,
        Ready Tan.compiled.module Tan.compiled.tables heap' final ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r :=
  (Verified.ImplementsTables.call Tan.compiled.tan.implements Tan.compiled.tables
    (Verified.tables_at [0, 1] (by decide) rfl)
    env heap store [.f64 x.toBits] x h rfl rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by simpa [Scalar.values] using congrArg List.reverse hv, heap', hR, hkeep⟩

/-- Function 13 of the module is its export `tan`. -/
theorem tan_export :
    ({ name := "tan", funcIdx := 13 } : Wasm.Export) ∈ Tan.compiled.module.exports := by
  decide +kernel

/-- The accuracy theorem for the compiled module's `tan`: its bytes decode to the module, whose
function 13 is exported as `tan`, and the store in which the module starts is ready.  A call of
that entry from a ready store returns without a trap a single `f64` whose bits are those of
`Tan.tan x`, and it leaves a ready store in which every region of the heap before the call keeps
its bytes.  The theorem therefore covers every call in a sequence of calls from the initial
store.  For finite `x` the bits lie within one representable step of the nearest-even rounding of
`tan x`. -/
theorem tan_bytes_accuracy :
    ∃ bytes, Wasm.Encoding.encode Tan.compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok Tan.compiled.module ∧
      ({ name := "tan", funcIdx := 13 } : Wasm.Export) ∈ Tan.compiled.module.exports ∧
      Ready Tan.compiled.module Tan.compiled.tables
        (Verified.initialHeap Tan.compiled.tables) Tan.compiled.module.initialStore ∧
      ∀ (env : Wasm.HostEnv Unit) (heap : LeanExe.Pipeline.Heap) (store : Wasm.Store Unit)
        (x : Float), Ready Tan.compiled.module Tan.compiled.tables heap store →
        Wasm.Runs false env Tan.compiled.module 13 store [.f64 x.toBits] (fun final values =>
          ∃ w : UInt64, values = [.f64 w] ∧ w = (Tan.tan x).toBits ∧
            (Finite x.toBits →
              F64SignedRounding.WithinSteps 1 (Real.tan (value x.toBits)) w) ∧
            ∃ heap' : LeanExe.Pipeline.Heap,
              Ready Tan.compiled.module Tan.compiled.tables heap' final ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := Tan.compiled.bytes
  refine ⟨bytes, henc, hdec, tan_export, ready_initial,
    fun env heap store x h => (tan_entry_call env heap store x h).mono ?_⟩
  intro _ values ⟨hv, hrest⟩
  exact ⟨(Tan.tan x).toBits, hv, rfl, tan_within x, hrest⟩

#print axioms tan_nonfinite
#print axioms tan_pos_zero
#print axioms tan_neg_zero
#print axioms ready_initial
#print axioms tan_entry_call
#print axioms tan_export
#print axioms tan_bytes_accuracy

end Library.Numerics.Float64.Tan.TanTheorem
