import Examples.ArrayCall
import Examples.Below100.Proof
import Verified.Reflect.Command

/-! The verified compiler's module of `keep` and `compute`.  `below100_call` composes the generated
`compiled.compute.trapFree` with `compute_eq`: from a store in which `top` can rise by 712 bytes,
the export `compute` returns the words of `expected` without a trap. -/

namespace Examples.Below100

open Wasm LeanExe.Pipeline LeanExe.Runtime

verified_compile compiled := [keep, compute]

/-- `compute` allocates at most 712 bytes: the empty output array of 56 bytes, its credit of 16
bytes, and at most 80 bytes for each of at most eight pushes. -/
theorem compute_bound (xs : Array UInt64) : compiled.compute.bound xs ≤ 712 := by
  rw [compiled.compute.bound_eq]
  refine (min_le_right _ _).trans ?_
  have hkeep : ∀ i out, compiled.keep.cost (xs, i, ⟨out⟩) ≤ 80 := fun i out => by
    rw [compiled.keep.cost_eq, Verified.paidGrowCost_eq]
    split <;> omega
  refine Nat.le_trans (Nat.add_le_add_left
    (Verified.loopCost_le (fun _ _ => True) (fun _ => 80) ?_ (fun _ _ _ _ => trivial) trivial) _) ?_
  · have hif : ∀ (c : Bool) (a : Nat), a ≤ 80 → (if c = true then a else 0) ≤ 80 := by
      intro c a h
      cases c <;> simp [h]
    intro _ s _
    simp only
    exact Nat.le_trans (Nat.le_of_eq (Nat.zero_add _)) (hif _ _ (hkeep s.1 s.2))
  · rw [Verified.sumBelow_const, Verified.blockCost_eq]
    simp [Verified.creditCost]

theorem compute_export :
    ({ name := "compute", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 3, the export `compute`, called with the borrowed array `xs` at `ptr` from a store with
the allocator invariant, a memory cap of at most 65,535 pages, and room for `top` to rise by 712
bytes, returns without a trap the address of an owned array that holds `expected xs`.  The input
stays borrowed, every region of the heap before the call keeps its bytes and lies apart from the
result, and `top` rises by at most 712 bytes. -/
theorem below100_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (xs : Array UInt64) (ptr : UInt64) (hAt : heap.At store)
    (hCap : store.memoryCap compiled.module 0 ≤ 65535) (hb : heap.Borrowed store ptr xs)
    (hroom : heap.Within store compiled.module 712) :
    Runs false env compiled.module 3 store [.i64 ptr] fun final values =>
      ∃ optr : UInt64, values = [.i64 optr] ∧ ∃ heap' : Heap, heap'.At final ∧
        final.memoryCap compiled.module 0 ≤ 65535 ∧ heap'.Owned final optr (expected xs) ∧
        heap'.Borrowed final ptr xs ∧
        (∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r ∧ regionsDisjoint r (block final optr)) ∧
        heap'.top.toNat ≤ heap.top.toNat + 712 :=
  arrayCall compiled.compute.trapFree compute_bound (fun xs h => compute_eq xs h) env heap store
    xs ptr hAt hCap hb hroom

#print axioms below100_call

end Examples.Below100
