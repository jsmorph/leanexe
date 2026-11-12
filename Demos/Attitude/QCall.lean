import Demos.Attitude.QVerified
import Verified.Call

/-! The call of the compiled q-method (Q5).  `qmethod_bound` bounds the bytes by which a call can
raise the allocator's `top` by a constant, since the program allocates only its result.
`qmethod_callSpec` states that function 102, the export `qmethod`, returns `qmethod xs` without a
trap from every ready store in which `top` can rise by that constant within the memory cap.
`qmethod_call` states it for a host: the module's bytes decode to the module, its start store is
ready, and from a ready store with the input's bit patterns borrowed, the export returns a new
array that holds the bit patterns of `qmethod xs`, to which `qmethod_sound` applies. -/

namespace Demos.Attitude.QMethod

open Wasm LeanExe.Pipeline

theorem qmethod_export :
    ({ name := "qmethod", funcIdx := 102 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The literal of eight values: the empty block and eight pushes. -/
theorem rejectWith_bound (status : Float) : compiled.rejectWith.bound status = 712 := by
  rw [compiled.rejectWith.bound_eq]
  decide

theorem certify_bound (inv half : Array UInt64) (K : M4) (rt mt : Library.Numerics.Interval.Interval)
    (c : Float) (q : Q4) : compiled.certify.bound (inv, half, K, rt, mt, c, q) = 712 := by
  rw [compiled.certify.bound_eq, rejectWith_bound]
  split
  · decide
  · rfl

/-- A call of `qmethod` raises `top` by at most 712 bytes, the block of its result, an array
literal of eight values. -/
theorem qmethod_bound (xs : Array Float) : compiled.qmethod.bound xs ≤ 712 := by
  rw [compiled.qmethod.bound_eq, compiled.qmethodWith.bound_eq, rejectWith_bound]
  split
  · split
    · rw [certify_bound]
    · exact Nat.le_refl _
  · exact Nat.le_refl _

/-- **Q5.**  Function 102 returns `qmethod xs` from every ready store in which `top` can rise by
712 bytes within the memory cap, and `top` rises by at most that much. -/
theorem qmethod_callSpec :
    _root_.Verified.CallSpec compiled.module compiled.tables 102 qmethod fun _ => 712 :=
  _root_.Verified.Call.spec
    (_root_.Verified.ImplementsTables.call compiled.qmethod.trapFree compiled.tables
      (_root_.Verified.tables_at [0, 1] (by decide) rfl))
    (fun x _ _ h => h.mono (qmethod_bound x))
    (fun x _ _ _ _ h => h.trans (Nat.add_le_add_left (qmethod_bound x) _))
    (fun _ _ _ _ _ => rfl)

/-- Q5 over the bit patterns: an `Array Float` is represented by the array of its elements' bit
patterns, so function 102 returns the bit patterns of `qmethod xs`. -/
theorem qmethod_callBits :
    _root_.Verified.CallSpec compiled.module compiled.tables 102
      (fun xs : Array Float => (qmethod xs).map Float.toBits) fun _ => 712 :=
  qmethod_callSpec

/-- The bytes of `compiled.module` decode to the module, whose export `qmethod` is function 102
and whose start store is ready.  Called from a ready store with the bit patterns of an input `xs`
borrowed at `ptr` and room for `top` to rise by 712 bytes, function 102 returns without a trap the
address of a new array that holds the bit patterns of `qmethod xs`, and it leaves a ready store in
which the input stays borrowed and `top` has risen by at most 712 bytes. -/
theorem qmethod_call :
    (∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok compiled.module) ∧
    ({ name := "qmethod", funcIdx := 102 } : Wasm.Export) ∈ compiled.module.exports ∧
    _root_.Verified.Ready compiled.module compiled.tables
      (_root_.Verified.initialHeap compiled.tables) compiled.module.initialStore ∧
    ∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (xs : Array Float) (ptr : UInt64),
      _root_.Verified.Ready compiled.module compiled.tables heap store →
      heap.Borrowed store ptr (xs.map Float.toBits) →
      heap.Within store compiled.module 712 →
      Runs false env compiled.module 102 store [.i64 ptr] fun final values =>
        ∃ optr : UInt64, values = [.i64 optr] ∧ ∃ heap' : Heap,
          heap'.Owned final optr ((qmethod xs).map Float.toBits) ∧
          _root_.Verified.Ready compiled.module compiled.tables heap' final ∧
          heap'.Borrowed final ptr (xs.map Float.toBits) ∧
          heap'.top.toNat ≤ heap.top.toNat + 712 := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  refine ⟨⟨bytes, henc, hdec⟩, qmethod_export, _root_.Verified.Ready.initial rfl compiled.initial,
    fun env heap store xs ptr hR hb hroom => ?_⟩
  exact (_root_.Verified.Call.array qmethod_callBits env heap store [.i64 ptr] xs hR
    ⟨ptr, rfl, hb⟩ rfl hroom).mono fun _ _ ⟨optr, hv, heap', hown, hR', hkept, _, hrise⟩ =>
      ⟨optr, hv, heap', hown, hR', hkept _ _ hb, hrise⟩

end Demos.Attitude.QMethod
