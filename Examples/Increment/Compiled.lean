import Examples.ArrayCall
import Examples.Increment.Proof
import Verified.Reflect.Command

/-! The verified compiler's module of `compute`.  `increment_call` composes the generated
`compiled.compute.trapFree` with `compute_eq`: from a store in which `top` can rise by 120 bytes,
the export `compute` returns the words of `expected` without a trap.  `compute_callSpec` states the
call as an instance of `Verified.CallSpec`, with the generated bound as the room. -/

namespace Examples.Increment

open Wasm LeanExe.Pipeline LeanExe.Runtime

verified_compile compiled := [compute]

/-- `compute` allocates one block for its result of at most eight words: at most 120 bytes. -/
theorem compute_bound (xs : Array UInt64) : compiled.compute.bound xs ≤ 120 := by
  rw [compiled.compute.bound_eq, Verified.blockCost_eq]
  split
  · rename_i h
    have h8 : xs.size.toUInt64.toNat ≤ 8 := UInt64.le_iff_toNat_le.mp h
    omega
  · simp

theorem compute_export :
    ({ name := "compute", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 2, the export `compute`, called with the borrowed array `xs` at `ptr` from a store with
the allocator invariant, a memory cap of at most 65,535 pages, and room for `top` to rise by 120
bytes, returns without a trap the address of an owned array that holds `expected xs`.  The input
stays borrowed, every region of the heap before the call keeps its bytes and lies apart from the
result, and `top` rises by at most 120 bytes. -/
theorem increment_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (xs : Array UInt64) (ptr : UInt64) (hAt : heap.At store)
    (hCap : store.memoryCap compiled.module 0 ≤ 65535) (hb : heap.Borrowed store ptr xs)
    (hroom : heap.Within store compiled.module 120) :
    Runs false env compiled.module 2 store [.i64 ptr] fun final values =>
      ∃ optr : UInt64, values = [.i64 optr] ∧ ∃ heap' : Heap, heap'.At final ∧
        final.memoryCap compiled.module 0 ≤ 65535 ∧ heap'.Owned final optr (expected xs) ∧
        heap'.Borrowed final ptr xs ∧
        (∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r ∧ regionsDisjoint r (block final optr)) ∧
        heap'.top.toNat ≤ heap.top.toNat + 120 :=
  arrayCall compiled.compute.trapFree compute_bound (fun xs h => compute_eq xs h) env heap store
    xs ptr hAt hCap hb hroom

/-- `Verified.CallSpec` for function 2 and `expected`, with the generated bound as the room: from a
ready store in which `top` can rise by `compiled.compute.bound xs` bytes, the call with the
borrowed array `xs` returns an owned array that holds `expected xs`, leaves a ready store, and
raises `top` by at most that bound. -/
theorem compute_callSpec :
    Verified.CallSpec compiled.module compiled.tables 2 expected compiled.compute.bound :=
  (Verified.ImplementsTables.call (.ofA compiled.compute.trapFree) compiled.tables nofun).spec
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs ⟨_, _, hxs⟩ => compute_eq xs hxs.values.size_lt

#print axioms increment_call
#print axioms compute_callSpec

end Examples.Increment
