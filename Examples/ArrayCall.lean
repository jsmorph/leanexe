import LeanExe.Pipeline.Implements
import LeanExe.ProofKit.BorrowedKept
import Verified.RuntimeFacts

/-! The call of an entry that maps a borrowed array of words to an owned array of words without a
trap, stated for a function `g` that the entry's function equals on every array that memory can
hold.  The compiled examples state their call theorems with it. -/

namespace Examples

open Wasm LeanExe.Pipeline LeanExe.Runtime

/-- From a `trapFree` theorem of `f`, a constant `B` at least its allocation bound, and `g` equal to
`f` on every array of fewer than `2 ^ 64` words: a call with the borrowed array `xs` at `ptr`, from
a store with the allocator invariant, a memory cap of at most 65,535 pages, and room for `top` to
rise by `B` bytes, returns without a trap the address of an owned array that holds `g xs`.  The
input stays borrowed, the cap stays at most 65,535 pages, every region of the heap before the call
keeps its bytes and lies apart from the result's block, and `top` rises by at most `B`. -/
theorem arrayCall {m : Module} {k : Nat} {f g : Array UInt64 → Array UInt64}
    {bound : Array UInt64 → Nat} {B : Nat}
    (hI : ImplementsA false m k f (fun x heap store => heap.Within store m (bound x))
      (fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + bound x))
    (hB : ∀ xs, bound xs ≤ B) (hg : ∀ xs : Array UInt64, xs.size < 2 ^ 64 → f xs = g xs)
    (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (xs : Array UInt64) (ptr : UInt64)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535) (hb : heap.Borrowed store ptr xs)
    (hroom : heap.Within store m B) :
    Runs false env m k store [.i64 ptr] fun final values =>
      ∃ optr : UInt64, values = [.i64 optr] ∧ ∃ heap' : Heap, heap'.At final ∧
        final.memoryCap m 0 ≤ 65535 ∧ heap'.Owned final optr (g xs) ∧
        heap'.Borrowed final ptr xs ∧
        (∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r ∧ regionsDisjoint r (block final optr)) ∧
        heap'.top.toNat ≤ heap.top.toNat + B := by
  have hargs : Represent.borrowed heap store [.i64 ptr] xs := ⟨ptr, rfl, hb⟩
  refine (hI env store heap [.i64 ptr] xs hAt (hroom.mono (hB xs)) hargs Separate.nil
    hCap).mono ?_
  intro final values ⟨heap', hAt', howned, hcaps, hframe, htop⟩
  obtain ⟨optr, hv, hown⟩ : ∃ optr, values.reverse = [.i64 optr] ∧
      heap'.Owned final optr (f xs) := howned
  have hvs : values = [.i64 optr] := by simpa using congrArg List.reverse hv
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  refine ⟨optr, hvs, heap', hAt', memoryCap_le_of_caps hcaps hCap, ?_,
    LeanExe.ProofKit.BorrowedKept.borrowed_kept hb hAt' hkeep, fun r hr hpos => ?_,
    htop.trans (Nat.add_le_add_left (hB xs) _)⟩
  · rw [← hg xs hb.values.size_lt]
    exact hown
  · obtain ⟨h1, h2, h3⟩ := hframe r hr hpos Apart.nil
    refine ⟨h1, h2, h3 _ ?_⟩
    rw [hv]
    exact List.mem_singleton_self _

#print axioms arrayCall

end Examples
