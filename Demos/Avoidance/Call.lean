import Demos.Avoidance.Verified
import Demos.Avoidance.Soundness
import Demos.Conjunction.BoxSoundness
import Verified.Call

/-! The calls of the compiled authorizer (C1).  `authorize_callSpec` states that the export
`authorize`, function 94, returns `authorize xs n` without a trap from every ready store in which
the allocator's `top` can rise by `compiled.authorize.bound (xs, n)` bytes within the memory cap,
from the generated `compiled.authorize.trapFree` and the tables of `exp`, `sin`, and `cos`.
`avoidance` joins the module's bytes, the export, the readiness of the start store, the call, and
`authorize_model` for status 0.  `pcBox_call` states the call of the export `pcBox` with
`Demos.Conjunction.pcBox_enclosure` for status 0. -/

namespace Demos.Avoidance

open Wasm LeanExe.Pipeline Demos.Orbit
open CodeLib.IEEE64 (value Finite)

theorem authorize_export :
    ({ name := "authorize", funcIdx := 94 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem pcBox_export :
    ({ name := "pcBox", funcIdx := 93 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The store in which the module starts is ready, with the heap that holds the tables. -/
theorem ready_initial :
    _root_.Verified.Ready compiled.module compiled.tables
      (_root_.Verified.initialHeap compiled.tables) compiled.module.initialStore :=
  _root_.Verified.Ready.initial rfl compiled.initial

set_option maxRecDepth 100000 in
/-- **C1.**  Function 94 returns `authorize xs n` from every ready store in which `top` can rise
by `compiled.authorize.bound (xs, n)` bytes within the memory cap, and `top` rises by at most that
much. -/
theorem authorize_callSpec :
    _root_.Verified.CallSpec compiled.module compiled.tables 94
      (fun x : Array Float × UInt64 => authorize x.1 x.2) compiled.authorize.bound :=
  _root_.Verified.ImplementsTables.call compiled.authorize.trapFree compiled.tables
    (_root_.Verified.tables_at [0, 1, 2] (by decide) rfl)

/-- The module's bytes decode to the module, whose export `authorize` is function 94, whose
start store is ready, and whose entry returns `authorize xs n` without a trap from every ready
store with room for its allocation bound.  When the result's status is 0, for every conjunction,
every velocity change of the box, and every displacement within the padding, the two-body
trajectories from the primary's state at the burn solve Newton's equation, the miss vector is the
closest approach of the line, and the model's probability lies below the threshold. -/
theorem avoidance :
    (∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok compiled.module) ∧
      ({ name := "authorize", funcIdx := 94 } : Wasm.Export) ∈ compiled.module.exports ∧
      _root_.Verified.Ready compiled.module compiled.tables
        (_root_.Verified.initialHeap compiled.tables) compiled.module.initialStore ∧
      _root_.Verified.CallSpec compiled.module compiled.tables 94
        (fun x : Array Float × UInt64 => authorize x.1 x.2) compiled.authorize.bound ∧
      ∀ (xs : Array Float) (n : UInt64), (authorize xs n)[0]! = 0.0 →
        valid xs n = true ∧ ∀ j < (count xs).toNat, ∀ dv d : V3, InBox xs dv → InPad xs d →
          Good xs j dv d ∧ pcAfter xs j dv d < val xs 14 := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  exact ⟨⟨bytes, henc, hdec⟩, authorize_export, ready_initial, authorize_callSpec,
    fun _ _ h => authorize_sound h⟩

/-- A call of the export `pcBox` from a ready store, with the bits of the floats and the word of
the panel count as arguments, returns without a trap the words of the status, `lo`, and `hi` of
`pcBox`, leaves a ready store in which every region of the heap before the call keeps its bytes,
and, when the status is 0, satisfies the conclusions of `Demos.Conjunction.pcBox_enclosure` for
every mean and covariance between the given ends. -/
theorem pcBox_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (m1lo m1hi m2lo m2hi c11lo c11hi c12lo c12hi c22lo c22hi r : Float) (n : UInt64)
    (h : _root_.Verified.Ready compiled.module compiled.tables heap store) :
    Runs false env compiled.module 93 store
      [.i64 n, .f64 r.toBits, .f64 c22hi.toBits, .f64 c22lo.toBits, .f64 c12hi.toBits,
        .f64 c12lo.toBits, .f64 c11hi.toBits, .f64 c11lo.toBits, .f64 m2hi.toBits,
        .f64 m2lo.toBits, .f64 m1hi.toBits, .f64 m1lo.toBits]
      fun final values =>
        values = [.f64 (Demos.Conjunction.pcBox m1lo m1hi m2lo m2hi c11lo c11hi c12lo c12hi c22lo
            c22hi r n).hi.toBits,
          .f64 (Demos.Conjunction.pcBox m1lo m1hi m2lo m2hi c11lo c11hi c12lo c12hi c22lo c22hi
            r n).lo.toBits,
          .i64 (Demos.Conjunction.pcBox m1lo m1hi m2lo m2hi c11lo c11hi c12lo c12hi c22lo c22hi
            r n).status] ∧
        (∃ heap' : Heap, _root_.Verified.Ready compiled.module compiled.tables heap' final ∧
          ∀ r', heap.Region r' → 0 < r'.2 →
            (∀ a, r'.1 ≤ a → a < r'.1 + r'.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r') ∧
        ((Demos.Conjunction.pcBox m1lo m1hi m2lo m2hi c11lo c11hi c12lo c12hi c22lo c22hi r
            n).status = 0 →
          ∀ m1 m2 c11 c12 c22 : ℝ,
            value m1lo.toBits ≤ m1 ∧ m1 ≤ value m1hi.toBits →
            value m2lo.toBits ≤ m2 ∧ m2 ≤ value m2hi.toBits →
            value c11lo.toBits ≤ c11 ∧ c11 ≤ value c11hi.toBits →
            value c12lo.toBits ≤ c12 ∧ c12 ≤ value c12hi.toBits →
            value c22lo.toBits ≤ c22 ∧ c22 ≤ value c22hi.toBits →
            0 < c11 ∧ 0 < Demos.Conjunction.Model.det c11 c12 c22 ∧ 0 < value r.toBits ∧
              Library.Numerics.Interval.Contains
                (Demos.Conjunction.pcBox m1lo m1hi m2lo m2hi c11lo c11hi c12lo c12hi c22lo c22hi
                  r n)
                (Demos.Conjunction.Model.pc m1 m2 c11 c12 c22 (value r.toBits))) :=
  (_root_.Verified.ImplementsTables.call compiled.pcBox.implements compiled.tables
    (_root_.Verified.tables_at [0] (by decide) rfl) env heap store
    [.f64 m1lo.toBits, .f64 m1hi.toBits, .f64 m2lo.toBits, .f64 m2hi.toBits, .f64 c11lo.toBits,
      .f64 c11hi.toBits, .f64 c12lo.toBits, .f64 c12hi.toBits, .f64 c22lo.toBits,
      .f64 c22hi.toBits, .f64 r.toBits, .i64 n]
    (m1lo, m1hi, m2lo, m2hi, c11lo, c11hi, c12lo, c12hi, c22lo, c22hi, r, n) h rfl rfl
    trivial).mono
    fun _ values ⟨heap', hv, hR, _, hkeep, _⟩ =>
      ⟨by
          have hw := congrArg List.reverse hv
          simp only [Scalar.values, List.reverse_reverse, List.cons_append,
            List.nil_append, List.reverse_cons, List.reverse_nil] at hw
          exact hw, ⟨heap', hR, hkeep⟩,
        fun hs _ _ _ _ _ h1 h2 h11 h12 h22 =>
          Demos.Conjunction.pcBox_enclosure hs h1 h2 h11 h12 h22⟩

#print axioms authorize_callSpec
#print axioms avoidance
#print axioms pcBox_call

end Demos.Avoidance
