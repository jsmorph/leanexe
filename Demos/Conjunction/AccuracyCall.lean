import Demos.Conjunction.AccuracyVerified
import Demos.Conjunction.AccuracySoundness
import Verified.Call

/-!
Call theorems of the module `accuracy`.  A call of the export `circularError` or `linearError`
from a ready store returns without a trap the three words of the program's result, the status,
`lo`, and `hi`, and leaves a ready store in which every region of the heap before the call keeps
its bytes.  When the returned status is 0, the conclusions of `circularError_sound` or
`linearError_sound` hold for the returned endpoints.  The store in which the module starts is
ready, so the theorems cover every call of a sequence of calls from it.
-/

namespace Demos.Conjunction.Accuracy

open Verified (Ready)
open Wasm LeanExe.Pipeline
open CodeLib.IEEE64 (value Finite)

/-- The store in which the module starts is ready, with the heap that holds the table of `exp`. -/
theorem ready_initial :
    Ready compiled.module compiled.tables (Verified.initialHeap compiled.tables)
      compiled.module.initialStore :=
  Verified.Ready.initial rfl compiled.initial

theorem circularError_export :
    ({ name := "circularError", funcIdx := 70 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem linearError_export :
    ({ name := "linearError", funcIdx := 71 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- A call of the export `circularError` from a ready store, with the bits of the floats and the
words of the counts as arguments, returns without a trap the words of the status, `lo`, and `hi`
of `circularError`, leaves a ready store in which every region of the heap before the call keeps
its bytes, and, when the status is 0, satisfies the conclusions of `circularError_sound`. -/
theorem circularError_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (m1 m2 c11 c12 c22 p : Float) (n k : UInt64)
    (h : Ready compiled.module compiled.tables heap store) :
    Runs false env compiled.module 70 store
      [.i64 k, .i64 n, .f64 p.toBits, .f64 c22.toBits, .f64 c12.toBits, .f64 c11.toBits,
        .f64 m2.toBits, .f64 m1.toBits]
      fun final values =>
        values = [.f64 (circularError m1 m2 c11 c12 c22 p n k).hi.toBits,
          .f64 (circularError m1 m2 c11 c12 c22 p n k).lo.toBits,
          .i64 (circularError m1 m2 c11 c12 c22 p n k).status] ∧
        (∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r) ∧
        ((circularError m1 m2 c11 c12 c22 p n k).status = 0 →
          0 < value p.toBits ∧ value p.toBits < 1 ∧ 0 < value c11.toBits ∧
            0 < Model.det (value c11.toBits) (value c12.toBits) (value c22.toBits) ∧
            Finite (circularError m1 m2 c11 c12 c22 p n k).lo.toBits ∧
            Finite (circularError m1 m2 c11 c12 c22 p n k).hi.toBits ∧
            Model.RadiusIn (Model.pc (value m1.toBits) (value m2.toBits) (value c11.toBits)
                (value c12.toBits) (value c22.toBits)) (value p.toBits)
              (value (circularError m1 m2 c11 c12 c22 p n k).lo.toBits)
              (value (circularError m1 m2 c11 c12 c22 p n k).hi.toBits)) :=
  (Verified.ImplementsTables.call compiled.circularError.implements compiled.tables
    (Verified.tables_at [0] (by decide) rfl) env heap store
    [.f64 m1.toBits, .f64 m2.toBits, .f64 c11.toBits, .f64 c12.toBits, .f64 c22.toBits,
      .f64 p.toBits, .i64 n, .i64 k] (m1, m2, c11, c12, c22, p, n, k) h rfl rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by
          have hw := congrArg List.reverse hv
          simp only [Scalar.values, List.reverse_reverse, List.append_nil, List.cons_append,
            List.nil_append, List.reverse_cons, List.reverse_nil] at hw
          exact hw, ⟨heap', hR, hkeep⟩,
        fun hs => circularError_sound hs⟩

/-- A call of the export `linearError` from a ready store returns without a trap the words of
the status, `lo`, and `hi` of `linearError`, leaves a ready store in which every region of the
heap before the call keeps its bytes, and, when the status is 0, satisfies the conclusions of
`linearError_sound`. -/
theorem linearError_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (b v p : Float) (k : UInt64) (h : Ready compiled.module compiled.tables heap store) :
    Runs false env compiled.module 71 store
      [.i64 k, .f64 p.toBits, .f64 v.toBits, .f64 b.toBits]
      fun final values =>
        values = [.f64 (linearError b v p k).hi.toBits, .f64 (linearError b v p k).lo.toBits,
          .i64 (linearError b v p k).status] ∧
        (∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r) ∧
        ((linearError b v p k).status = 0 →
          0 < value p.toBits ∧ value p.toBits < 1 ∧ 0 < value v.toBits ∧
            Finite (linearError b v p k).lo.toBits ∧ Finite (linearError b v p k).hi.toBits ∧
            Model.RadiusIn (Model.linearProb (value b.toBits) (value v.toBits)) (value p.toBits)
              (value (linearError b v p k).lo.toBits) (value (linearError b v p k).hi.toBits)) :=
  (Verified.ImplementsTables.call compiled.linearError.implements compiled.tables
    (Verified.tables_at [0] (by decide) rfl) env heap store
    [.f64 b.toBits, .f64 v.toBits, .f64 p.toBits, .i64 k] (b, v, p, k) h rfl rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by
          have hw := congrArg List.reverse hv
          simp only [Scalar.values, List.reverse_reverse, List.append_nil, List.cons_append,
            List.nil_append, List.reverse_cons, List.reverse_nil] at hw
          exact hw, ⟨heap', hR, hkeep⟩,
        fun hs => linearError_sound hs⟩

#print axioms ready_initial
#print axioms circularError_export
#print axioms linearError_export
#print axioms circularError_call
#print axioms linearError_call

end Demos.Conjunction.Accuracy
