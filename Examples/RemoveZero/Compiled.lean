import Examples.ArrayCall
import Examples.RemoveZero.Proof
import Verified.Reflect.Command

/-! The verified compiler's module of the library's `firstZero` and of `compute`.
`removeZero_call` composes the generated `compiled.compute.trapFree` with `compute_eq`: from a
store in which `top` can rise by 120 bytes, the export `compute` returns the words of `expected`
without a trap. -/

namespace Examples.RemoveZero

open Wasm LeanExe.Pipeline LeanExe.Runtime

verified_compile compiled := [firstZero, compute]

/-- `compute` allocates one block for its result of at most eight words: at most 120 bytes. -/
theorem compute_bound (xs : Array UInt64) : compiled.compute.bound xs ≤ 120 := by
  have h8 : (if xs.size.toUInt64 ≤ 8 then xs.size.toUInt64 else 0).toNat ≤ 8 := by
    split
    · rename_i h
      exact UInt64.le_iff_toNat_le.mp h
    · simp
  rw [compiled.compute.bound_eq, Verified.blockCost_eq]
  generalize (if xs.size.toUInt64 ≤ 8 then xs.size.toUInt64 else 0) = c at h8 ⊢
  split
  · rename_i h
    have hlt := UInt64.lt_iff_toNat_lt.mp h
    have h1 : (1 : UInt64) ≤ c := UInt64.le_iff_toNat_le.mpr (by simp only [UInt64.reduceToNat]; omega)
    rw [UInt64.toNat_sub_of_le _ _ h1]
    simp only [UInt64.reduceToNat]
    omega
  · omega

theorem compute_export :
    ({ name := "compute", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 3, the export `compute`, called with the borrowed array `xs` at `ptr` from a store with
the allocator invariant, a memory cap of at most 65,535 pages, and room for `top` to rise by 120
bytes, returns without a trap the address of an owned array that holds `expected xs`.  The input
stays borrowed, every region of the heap before the call keeps its bytes and lies apart from the
result, and `top` rises by at most 120 bytes. -/
theorem removeZero_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (xs : Array UInt64) (ptr : UInt64) (hAt : heap.At store)
    (hCap : store.memoryCap compiled.module 0 ≤ 65535) (hb : heap.Borrowed store ptr xs)
    (hroom : heap.Within store compiled.module 120) :
    Runs false env compiled.module 3 store [.i64 ptr] fun final values =>
      ∃ optr : UInt64, values = [.i64 optr] ∧ ∃ heap' : Heap, heap'.At final ∧
        final.memoryCap compiled.module 0 ≤ 65535 ∧ heap'.Owned final optr (expected xs) ∧
        heap'.Borrowed final ptr xs ∧
        (∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r ∧ regionsDisjoint r (block final optr)) ∧
        heap'.top.toNat ≤ heap.top.toNat + 120 :=
  arrayCall compiled.compute.trapFree compute_bound (fun xs h => compute_eq xs h) env heap store
    xs ptr hAt hCap hb hroom

#print axioms removeZero_call

end Examples.RemoveZero
