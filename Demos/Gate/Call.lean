import Demos.Gate.Verified
import Demos.Gate.Soundness
import Verified.Call

/-!
Call theorems of the module `chisquare`.  A call of the export `tail`, `cdf`, or `quantile` from a
ready store returns without a trap the three words of the program's result, the status, `lo`, and
`hi`, and leaves a ready store in which every region of the heap before the call keeps its bytes.
When the returned status is 0, the conclusions of `tail_sound`, `cdf_sound`, or `quantile_sound`
hold for the returned endpoints.  The store in which the module starts is ready, so the theorems
cover every call of a sequence of calls from it.
-/

namespace Demos.Gate

open Verified (Ready)
open Wasm LeanExe.Pipeline Library.Numerics.Interval
open CodeLib.IEEE64 (value Finite)

/-- The store in which the module starts is ready, with the heap that holds the table of `exp` and
the seven tables of `erfc`. -/
theorem ready_initial :
    Ready compiled.module compiled.tables (Verified.initialHeap compiled.tables)
      compiled.module.initialStore :=
  Verified.Ready.initial rfl compiled.initial

theorem tail_export :
    ({ name := "tail", funcIdx := 95 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem cdf_export :
    ({ name := "cdf", funcIdx := 96 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem quantile_export :
    ({ name := "quantile", funcIdx := 97 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- A call of the export `tail` from a ready store, with the word of `k` and the bits of `x` as
arguments, returns without a trap the words of the status, `lo`, and `hi` of `tail k x`, leaves a
ready store in which every region of the heap before the call keeps its bytes, and, when the
status is 0, satisfies the conclusions of `tail_sound`. -/
theorem tail_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (k : UInt64) (x : Float)
    (h : Ready compiled.module compiled.tables heap store) :
    Runs false env compiled.module 95 store [.f64 x.toBits, .i64 k]
      fun final values =>
        values = [.f64 (tail k x).hi.toBits, .f64 (tail k x).lo.toBits, .i64 (tail k x).status] ∧
        (∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r) ∧
        ((tail k x).status = 0 →
          1 ≤ k.toNat ∧ k.toNat ≤ 1000 ∧ Finite x.toBits ∧
            Contains (tail k x) (Model.tail k.toNat (value x.toBits))) :=
  (Verified.ImplementsTables.call compiled.tail.implements compiled.tables
    (Verified.tables_at [0, 1, 2, 3, 4, 5, 6, 7] (by decide) rfl) env heap store [.i64 k, .f64 x.toBits] (k, x) h rfl
    rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by
          have hw := congrArg List.reverse hv
          simp only [Scalar.values, List.reverse_reverse, List.cons_append,
            List.nil_append, List.reverse_cons, List.reverse_nil] at hw
          exact hw, ⟨heap', hR, hkeep⟩,
        fun hs => tail_sound hs⟩

set_option maxRecDepth 100000 in
/-- A call of the export `cdf` from a ready store returns without a trap the words of the status,
`lo`, and `hi` of `cdf k x`, leaves a ready store in which every region of the heap before the
call keeps its bytes, and, when the status is 0, satisfies the conclusions of `cdf_sound`. -/
theorem cdf_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (k : UInt64) (x : Float)
    (h : Ready compiled.module compiled.tables heap store) :
    Runs false env compiled.module 96 store [.f64 x.toBits, .i64 k]
      fun final values =>
        values = [.f64 (cdf k x).hi.toBits, .f64 (cdf k x).lo.toBits, .i64 (cdf k x).status] ∧
        (∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r) ∧
        ((cdf k x).status = 0 →
          1 ≤ k.toNat ∧ k.toNat ≤ 1000 ∧ Finite x.toBits ∧
            Contains (cdf k x) (Model.cdf k.toNat (value x.toBits))) :=
  (Verified.ImplementsTables.call compiled.cdf.implements compiled.tables
    (Verified.tables_at [0, 1, 2, 3, 4, 5, 6, 7] (by decide) rfl) env heap store [.i64 k, .f64 x.toBits] (k, x) h rfl
    rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by
          have hw := congrArg List.reverse hv
          simp only [Scalar.values, List.reverse_reverse, List.cons_append,
            List.nil_append, List.reverse_cons, List.reverse_nil] at hw
          exact hw, ⟨heap', hR, hkeep⟩,
        fun hs => cdf_sound hs⟩

set_option maxRecDepth 100000 in
/-- A call of the export `quantile` from a ready store returns without a trap the words of the
status, `lo`, and `hi` of `quantile k p h`, leaves a ready store in which every region of the heap
before the call keeps its bytes, and, when the status is 0, satisfies the conclusions of
`quantile_sound`. -/
theorem quantile_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (k : UInt64)
    (p : Float) (n : UInt64) (h : Ready compiled.module compiled.tables heap store) :
    Runs false env compiled.module 97 store [.i64 n, .f64 p.toBits, .i64 k]
      fun final values =>
        values = [.f64 (quantile k p n).hi.toBits, .f64 (quantile k p n).lo.toBits,
          .i64 (quantile k p n).status] ∧
        (∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r) ∧
        ((quantile k p n).status = 0 →
          0 < value p.toBits ∧ value p.toBits < 1 ∧ 1 ≤ k.toNat ∧ k.toNat ≤ 1000 ∧
            Finite (quantile k p n).lo.toBits ∧ Finite (quantile k p n).hi.toBits ∧
            Model.QuantileIn k.toNat (value p.toBits) (value (quantile k p n).lo.toBits)
              (value (quantile k p n).hi.toBits)) :=
  (Verified.ImplementsTables.call compiled.quantile.implements compiled.tables
    (Verified.tables_at [0, 1, 2, 3, 4, 5, 6, 7] (by decide) rfl) env heap store [.i64 k, .f64 p.toBits, .i64 n]
    (k, p, n) h rfl rfl trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by
          have hw := congrArg List.reverse hv
          simp only [Scalar.values, List.reverse_reverse, List.cons_append,
            List.nil_append, List.reverse_cons, List.reverse_nil] at hw
          exact hw, ⟨heap', hR, hkeep⟩,
        fun hs => quantile_sound hs⟩

#print axioms ready_initial
#print axioms tail_export
#print axioms cdf_export
#print axioms quantile_export
#print axioms tail_call
#print axioms cdf_call
#print axioms quantile_call

end Demos.Gate
