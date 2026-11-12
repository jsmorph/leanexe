import Demos.Conjunction.AdaptiveVerified
import Demos.Conjunction.AdaptiveSoundness
import Verified.Call

/-!
Call theorems of the module `adaptive`.  A call of the export `pcAdaptive` or
`circularErrorAdaptive` from a ready store returns without a trap the three words of the
program's result, the status, `lo`, and `hi`, and leaves a ready store in which every region of
the heap before the call keeps its bytes.  When the returned status is 0, the conclusions of
`pcAdaptive_enclosure` or `circularErrorAdaptive_sound` hold for the returned endpoints.  The
store in which the module starts is ready, so the theorems cover every call of a sequence of calls
from it.
-/

namespace Demos.Conjunction.Adaptive

open Verified (Ready)
open Wasm LeanExe.Pipeline
open Library.Numerics.Interval (Contains)
open CodeLib.IEEE64 (value Finite)

/-- The store in which the module starts is ready, with the heap that holds the table of `exp`. -/
theorem ready_initial :
    Ready compiled.module compiled.tables (Verified.initialHeap compiled.tables)
      compiled.module.initialStore :=
  Verified.Ready.initial rfl compiled.initial

theorem pcAdaptive_export :
    ({ name := "pcAdaptive", funcIdx := 68 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem circularErrorAdaptive_export :
    ({ name := "circularErrorAdaptive", funcIdx := 69 } : Wasm.Export) ∈
      compiled.module.exports := by
  decide +kernel

/-- A call of the export `pcAdaptive` from a ready store, with the bits of the floats and the word
of the panel count as arguments, returns without a trap the words of the status, `lo`, and `hi`
of `pcAdaptive`, leaves a ready store in which every region of the heap before the call keeps its
bytes, and, when the status is 0, satisfies the conclusions of `pcAdaptive_enclosure`. -/
theorem pcAdaptive_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (m1 m2 c11 c12 c22 r : Float) (n : UInt64)
    (h : Ready compiled.module compiled.tables heap store) :
    Runs false env compiled.module 68 store
      [.i64 n, .f64 r.toBits, .f64 c22.toBits, .f64 c12.toBits, .f64 c11.toBits,
        .f64 m2.toBits, .f64 m1.toBits]
      fun final values =>
        values = [.f64 (pcAdaptive m1 m2 c11 c12 c22 r n).hi.toBits,
          .f64 (pcAdaptive m1 m2 c11 c12 c22 r n).lo.toBits,
          .i64 (pcAdaptive m1 m2 c11 c12 c22 r n).status] ∧
        (∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          ∀ q, heap.Region q → 0 < q.2 →
            (∀ a, q.1 ≤ a → a < q.1 + q.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region q) ∧
        ((pcAdaptive m1 m2 c11 c12 c22 r n).status = 0 →
          0 < value c11.toBits ∧
            0 < Model.det (value c11.toBits) (value c12.toBits) (value c22.toBits) ∧
            0 < value r.toBits ∧ Finite r.toBits ∧
            Contains (pcAdaptive m1 m2 c11 c12 c22 r n)
              (Model.pc (value m1.toBits) (value m2.toBits) (value c11.toBits) (value c12.toBits)
                (value c22.toBits) (value r.toBits))) :=
  (Verified.ImplementsTables.call compiled.pcAdaptive.implements compiled.tables
    (Verified.tables_at [0] (by decide) rfl) env heap store
    [.f64 m1.toBits, .f64 m2.toBits, .f64 c11.toBits, .f64 c12.toBits, .f64 c22.toBits,
      .f64 r.toBits, .i64 n] (m1, m2, c11, c12, c22, r, n) h rfl rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by
          have hw := congrArg List.reverse hv
          simp only [Scalar.values, List.reverse_reverse, List.cons_append,
            List.nil_append, List.reverse_cons, List.reverse_nil] at hw
          exact hw, ⟨heap', hR, hkeep⟩,
        fun hs => pcAdaptive_enclosure hs⟩

/-- A call of the export `circularErrorAdaptive` from a ready store, with the bits of the floats
and the words of the counts as arguments, returns without a trap the words of the status, `lo`,
and `hi` of `circularErrorAdaptive`, leaves a ready store in which every region of the heap before
the call keeps its bytes, and, when the status is 0, satisfies the conclusions of
`circularErrorAdaptive_sound`. -/
theorem circularErrorAdaptive_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (m1 m2 c11 c12 c22 p : Float) (n k : UInt64)
    (h : Ready compiled.module compiled.tables heap store) :
    Runs false env compiled.module 69 store
      [.i64 k, .i64 n, .f64 p.toBits, .f64 c22.toBits, .f64 c12.toBits, .f64 c11.toBits,
        .f64 m2.toBits, .f64 m1.toBits]
      fun final values =>
        values = [.f64 (circularErrorAdaptive m1 m2 c11 c12 c22 p n k).hi.toBits,
          .f64 (circularErrorAdaptive m1 m2 c11 c12 c22 p n k).lo.toBits,
          .i64 (circularErrorAdaptive m1 m2 c11 c12 c22 p n k).status] ∧
        (∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          ∀ q, heap.Region q → 0 < q.2 →
            (∀ a, q.1 ≤ a → a < q.1 + q.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region q) ∧
        ((circularErrorAdaptive m1 m2 c11 c12 c22 p n k).status = 0 →
          0 < value p.toBits ∧ value p.toBits < 1 ∧ 0 < value c11.toBits ∧
            0 < Model.det (value c11.toBits) (value c12.toBits) (value c22.toBits) ∧
            Finite (circularErrorAdaptive m1 m2 c11 c12 c22 p n k).lo.toBits ∧
            Finite (circularErrorAdaptive m1 m2 c11 c12 c22 p n k).hi.toBits ∧
            Model.RadiusIn (Model.pc (value m1.toBits) (value m2.toBits) (value c11.toBits)
                (value c12.toBits) (value c22.toBits)) (value p.toBits)
              (value (circularErrorAdaptive m1 m2 c11 c12 c22 p n k).lo.toBits)
              (value (circularErrorAdaptive m1 m2 c11 c12 c22 p n k).hi.toBits)) :=
  (Verified.ImplementsTables.call compiled.circularErrorAdaptive.implements compiled.tables
    (Verified.tables_at [0] (by decide) rfl) env heap store
    [.f64 m1.toBits, .f64 m2.toBits, .f64 c11.toBits, .f64 c12.toBits, .f64 c22.toBits,
      .f64 p.toBits, .i64 n, .i64 k] (m1, m2, c11, c12, c22, p, n, k) h rfl rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by
          have hw := congrArg List.reverse hv
          simp only [Scalar.values, List.reverse_reverse, List.cons_append,
            List.nil_append, List.reverse_cons, List.reverse_nil] at hw
          exact hw, ⟨heap', hR, hkeep⟩,
        fun hs => circularErrorAdaptive_sound hs⟩

#print axioms ready_initial
#print axioms pcAdaptive_export
#print axioms circularErrorAdaptive_export
#print axioms pcAdaptive_call
#print axioms circularErrorAdaptive_call

end Demos.Conjunction.Adaptive
