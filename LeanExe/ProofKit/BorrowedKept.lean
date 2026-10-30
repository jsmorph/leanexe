import LeanExe.Pipeline.Allocation

/-!
A borrowed array stays borrowed through a call that keeps the bytes and regions of the heap.  The
lemma is stated for any array, so that checking it never evaluates the size of a literal table.
`Verified.ImplementsTables.call` applies it to every array borrowed before a call, the program's
tables among them.
-/

namespace LeanExe.ProofKit.BorrowedKept
open Wasm LeanExe.Pipeline

theorem borrowed_kept {heap heap' : Heap} {store final : Store Unit} {p : UInt64}
    {ws : Array UInt64} (hp : heap.Borrowed store p ws) (hAt : heap'.At final)
    (hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧ heap'.Region r) :
    heap'.Borrowed final p ws := by
  obtain ⟨hb, hr⟩ := hkeep _ hp.region (by show 0 < 8 * (ws.size + 1); omega)
  exact hp.keepIn hAt hb hr

#print axioms borrowed_kept

end LeanExe.ProofKit.BorrowedKept
