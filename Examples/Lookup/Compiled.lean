import Examples.ArrayCall
import Examples.Lookup.Proof
import Verified.Reflect.Command

/-! The verified compiler's module of `compute`, whose result is a two-word literal, which the
reflector reads as two pushes onto `#[]`.  `lookup_call` composes the generated
`compiled.compute.trapFree` with `compute_eq`: from a store in which `top` can rise by 232
bytes, the export `compute` returns the words of `expected` without a trap. -/

namespace Examples.Lookup

open Wasm LeanExe.Pipeline LeanExe.Runtime

verified_compile compiled := [compute]

/-- `compute` allocates the literal's empty block and its two pushes: 232 bytes. -/
theorem compute_bound (xs : Array UInt64) : compiled.compute.bound xs = 232 := by
  rw [compiled.compute.bound_eq]
  decide

theorem compute_export :
    ({ name := "compute", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 2, the export `compute`, called with the borrowed array `xs` at `ptr` from a store with
the allocator invariant, a memory cap of at most 65,535 pages, and room for `top` to rise by 232
bytes, returns without a trap the address of an owned array that holds `expected xs`.  The input
stays borrowed, every region of the heap before the call keeps its bytes and lies apart from the
result, and `top` rises by at most 232 bytes. -/
theorem lookup_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (xs : Array UInt64) (ptr : UInt64) (hAt : heap.At store)
    (hCap : store.memoryCap compiled.module 0 ≤ 65535) (hb : heap.Borrowed store ptr xs)
    (hroom : heap.Within store compiled.module 232) :
    Runs false env compiled.module 2 store [.i64 ptr] fun final values =>
      ∃ optr : UInt64, values = [.i64 optr] ∧ ∃ heap' : Heap, heap'.At final ∧
        final.memoryCap compiled.module 0 ≤ 65535 ∧ heap'.Owned final optr (expected xs) ∧
        heap'.Borrowed final ptr xs ∧
        (∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r ∧ regionsDisjoint r (block final optr)) ∧
        heap'.top.toNat ≤ heap.top.toNat + 232 :=
  arrayCall compiled.compute.trapFree (fun xs => (compute_bound xs).le)
    (fun xs h => compute_eq xs h) env heap store xs ptr hAt hCap hb hroom

#print axioms lookup_call

end Examples.Lookup
