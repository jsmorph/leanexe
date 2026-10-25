import Library.Hashing.XxHash64.Compiled
import Library.Hashing.XxHash64.Proof

/-! The bytes of the module `xxhash64` compute XXH64.  The entry, called from a ready store with a
borrowed array `msg`, a byte count `n`, and a seed, returns without a trap the word that the
transcription `Library.Hashing.XxHash64.Spec` gives for the first `n` bytes of `msg` and the seed.
The array stays borrowed, the store stays ready, and every region of the heap before the call
keeps its bytes.  The store in which the module starts is ready. -/

namespace Library.Hashing.XxHash64

open Wasm LeanExe.Pipeline LeanExe.Runtime Library.Bytes

/-- A store from which the module's entry runs, with `heap` the allocator's state: the allocator
invariant holds and the memory cap is at most 65,535 pages. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ store.memoryCap compiled.module 0 ≤ 65535

/-- The store in which the module starts is ready. -/
theorem ready_initial :
    Ready (Verified.initialHeap compiled.tables) compiled.module.initialStore := by
  obtain ⟨hAt, hCap, _⟩ := compiled.initial
  exact ⟨hAt, hCap⟩

/-- A borrowed array stays borrowed through a step that keeps the bytes of every region. -/
theorem borrowed_kept {heap heap' : Heap} {store final : Store Unit} {p : UInt64}
    {ws : Array UInt64} (hp : heap.Borrowed store p ws) (hAt : heap'.At final)
    (hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧ heap'.Region r) :
    heap'.Borrowed final p ws := by
  obtain ⟨hb, hr⟩ := hkeep _ hp.region (by show 0 < 8 * (ws.size + 1); omega)
  exact hp.keepIn hAt hb hr

theorem xxh64_export :
    ({ name := "xxh64", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 5, the export `xxh64`, returns XXH64 of the first `n` bytes of `msg` with the seed
`seed`. -/
theorem xxh64_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (msg : Array UInt64)
    (n seed ptr : UInt64) (h : Ready heap store) (hb : heap.Borrowed store ptr msg) :
    Runs false env compiled.module 5 store [.i64 seed, .i64 n, .i64 ptr] fun final values =>
      ∃ d : UInt64, values.reverse = [.i64 d] ∧
        d = Spec.xxh64 ((List.range n.toNat).map (byteAt msg)) seed ∧
        ∃ heap' : Heap, Ready heap' final ∧ heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r := by
  obtain ⟨hAt, hCap⟩ := h
  have hargs : Represent.borrowed heap store [.i64 ptr, .i64 n, .i64 seed] (msg, n, seed) :=
    ⟨[.i64 ptr], [.i64 n, .i64 seed], rfl, ⟨ptr, rfl, hb⟩, rfl⟩
  refine (compiled.xxh64.implements env store heap [.i64 ptr, .i64 n, .i64 seed] (msg, n, seed)
    hAt trivial hargs Separate.nil hCap).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨xxh64 msg n seed, howned, Proof.xxh64_eq msg n seed, heap',
    ⟨hAt', memoryCap_le_of_caps hcaps hCap⟩, borrowed_kept hb hAt' hkeep, hkeep⟩

#print axioms xxh64_call

end Library.Hashing.XxHash64
