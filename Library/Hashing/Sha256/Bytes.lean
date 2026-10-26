import Library.Hashing.Sha256.Compiled
import Library.Hashing.Sha256.Proof

/-! The bytes of the module `sha256` compute SHA-256 and SHA-224 of FIPS 180-4.  Each entry, called
from a ready store with a borrowed array `msg` and a byte count `n < 2 ^ 61`, returns without a
trap the four words of a digest whose bytes, read most significant bit first, are the digest of
the first `n` bytes of `msg` in `Library.Hashing.Sha2.Spec`.  The array stays borrowed, the store
stays ready, and every region of the heap before the call keeps its bytes.  The store in which the
module starts is ready.  `sha256_module` combines the two entries. -/

namespace Library.Hashing.Sha256

open Wasm LeanExe.Pipeline Library.Hashing.Words Library.Bytes
open SHS.Equiv.SHA256.Digest SHS.Equiv.SHA256.Padding.ByteDecoding SHS.Equiv.SHA256.Pipeline

/-- A store from which the module's entries run, with `heap` the allocator's state: the allocator
invariant holds, the round constants are a borrowed array at address 4096, and the memory cap is
at most 65,535 pages. -/
def Ready (heap : Heap) (store : Store Unit) : Prop :=
  heap.At store ∧ heap.Borrowed store 4096 roundConstants ∧
    store.memoryCap compiled.module 0 ≤ 65535

/-- The store in which the module starts is ready, with the heap that holds its table. -/
theorem ready_initial :
    Ready (Verified.initialHeap compiled.tables) compiled.module.initialStore := by
  obtain ⟨hAt, hCap, hBor⟩ := compiled.initial
  exact ⟨hAt, hBor 0 (by decide), hCap⟩

/-- A borrowed array stays borrowed through a step that keeps the bytes of every region. -/
theorem borrowed_kept {heap heap' : Heap} {store final : Store Unit} {p : UInt64}
    {ws : Array UInt64} (hp : heap.Borrowed store p ws) (hAt : heap'.At final)
    (hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧ heap'.Region r) :
    heap'.Borrowed final p ws := by
  obtain ⟨hb, hr⟩ := hkeep _ hp.region (by show 0 < 8 * (ws.size + 1); omega)
  exact hp.keepIn hAt hb hr

/-- A call of an entry that computes `f` from the round constants, from a ready store with the
borrowed array `msg` at `ptr` and the word `n`. -/
theorem entry_call {β : Type} [Scalar β] {k : Nat} {f : Array UInt64 → UInt64 → β}
    (hI : Verified.ImplementsTables false compiled.module k
      (fun x : Array UInt64 × UInt64 => f x.1 x.2) [(4096, roundConstants)]
      (fun _ _ _ => True) (fun _ _ _ _ _ => True))
    (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (msg : Array UInt64) (n ptr : UInt64)
    (h : Ready heap store) (hb : heap.Borrowed store ptr msg) :
    Runs false env compiled.module k store [.i64 n, .i64 ptr] fun final values =>
      values.reverse = Scalar.values (f msg n) ∧
      ∃ heap' : Heap, Ready heap' final ∧ heap'.Borrowed final ptr msg ∧
        ∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r := by
  obtain ⟨hAt, hTab, hCap⟩ := h
  have htab : ∀ t ∈ [((4096 : UInt64), roundConstants)],
      heap.Borrowed store t.1 t.2 ∧ Apart store [] (t.1.toNat, 8 * (t.2.size + 1)) := by
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨hTab, Apart.nil⟩
  have hargs : Represent.borrowed heap store [.i64 ptr, .i64 n] (msg, n) :=
    ⟨[.i64 ptr], [.i64 n], rfl, ⟨ptr, rfl, hb⟩, rfl⟩
  refine (hI env store heap [.i64 ptr, .i64 n] (msg, n) hAt trivial htab hargs Separate.nil
    hCap).mono ?_
  intro final values hpost
  obtain ⟨heap', hAt', howned, hcaps, hframe, _⟩ := hpost
  have hkeep : ∀ r, heap.Region r → 0 < r.2 →
      (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
        heap'.Region r :=
    fun r hr hpos => ⟨(hframe r hr hpos Apart.nil).1, (hframe r hr hpos Apart.nil).2.1⟩
  exact ⟨howned, heap', ⟨hAt', borrowed_kept hTab hAt' hkeep, memoryCap_le_of_caps hcaps hCap⟩,
    borrowed_kept hb hAt' hkeep, hkeep⟩

theorem sha256_export :
    ({ name := "sha256", funcIdx := 11 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem sha224_export :
    ({ name := "sha224", funcIdx := 12 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 11, the export `sha256`, returns the four words of the SHA-256 digest. -/
theorem sha256_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (msg : Array UInt64) (n ptr : UInt64) (h : Ready heap store)
    (hb : heap.Borrowed store ptr msg) (hn : n.toNat < 2 ^ 61) :
    Runs false env compiled.module 11 store [.i64 n, .i64 ptr] fun final values =>
      ∃ d : Words4,
        values.reverse = [.i64 d.w0, .i64 d.w1, .i64 d.w2, .i64 d.w3] ∧
        digestBitVec (d.bytes 32) = SHS.SHA256.sha256 (bytesToBitMessage (bytes msg n.toNat))
          (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact hn)) ∧
        ∃ heap' : Heap, Ready heap' final ∧ heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (entry_call compiled.sha256.implements env heap store msg n ptr h hb).mono
    fun _ _ ⟨hv, hrest⟩ => ⟨sha256 msg n, hv, sha256_spec msg n hn, hrest⟩

/-- Function 12, the export `sha224`, returns four words whose first 28 bytes are the SHA-224
digest. -/
theorem sha224_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (msg : Array UInt64) (n ptr : UInt64) (h : Ready heap store)
    (hb : heap.Borrowed store ptr msg) (hn : n.toNat < 2 ^ 61) :
    Runs false env compiled.module 12 store [.i64 n, .i64 ptr] fun final values =>
      ∃ d : Words4,
        values.reverse = [.i64 d.w0, .i64 d.w1, .i64 d.w2, .i64 d.w3] ∧
        digestBitVec224 (d.bytes 28) = SHS.SHA256.sha224 (bytesToBitMessage (bytes msg n.toNat))
          (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact hn)) ∧
        ∃ heap' : Heap, Ready heap' final ∧ heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (entry_call compiled.sha224.implements env heap store msg n ptr h hb).mono
    fun _ _ ⟨hv, hrest⟩ => ⟨sha224 msg n, hv, sha224_spec msg n hn, hrest⟩

/-- The module's bytes decode to the module, whose exports `sha256` and `sha224` are functions 11
and 12, whose start store is ready, and whose two entries compute their digests from every ready
store, as the two call theorems state. -/
theorem sha256_module :
    (∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok compiled.module) ∧
      ({ name := "sha256", funcIdx := 11 } : Wasm.Export) ∈ compiled.module.exports ∧
      ({ name := "sha224", funcIdx := 12 } : Wasm.Export) ∈ compiled.module.exports ∧
      Ready (Verified.initialHeap compiled.tables) compiled.module.initialStore ∧
      (∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (msg : Array UInt64)
        (n ptr : UInt64), Ready heap store → heap.Borrowed store ptr msg →
        (hn : n.toNat < 2 ^ 61) →
        Runs false env compiled.module 11 store [.i64 n, .i64 ptr] fun final values =>
          ∃ d : Words4, values.reverse = [.i64 d.w0, .i64 d.w1, .i64 d.w2, .i64 d.w3] ∧
            digestBitVec (d.bytes 32) = SHS.SHA256.sha256 (bytesToBitMessage (bytes msg n.toNat))
              (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact hn)) ∧
            ∃ heap' : Heap, Ready heap' final ∧ heap'.Borrowed final ptr msg ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) ∧
      (∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (msg : Array UInt64)
        (n ptr : UInt64), Ready heap store → heap.Borrowed store ptr msg →
        (hn : n.toNat < 2 ^ 61) →
        Runs false env compiled.module 12 store [.i64 n, .i64 ptr] fun final values =>
          ∃ d : Words4, values.reverse = [.i64 d.w0, .i64 d.w1, .i64 d.w2, .i64 d.w3] ∧
            digestBitVec224 (d.bytes 28) = SHS.SHA256.sha224 (bytesToBitMessage (bytes msg n.toNat))
              (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact hn)) ∧
            ∃ heap' : Heap, Ready heap' final ∧ heap'.Borrowed final ptr msg ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  exact ⟨⟨bytes, henc, hdec⟩, sha256_export, sha224_export, ready_initial,
    fun env heap store msg n ptr h hb hn => sha256_call env heap store msg n ptr h hb hn,
    fun env heap store msg n ptr h hb hn => sha224_call env heap store msg n ptr h hb hn⟩

#print axioms sha256_call
#print axioms sha224_call
#print axioms sha256_module

end Library.Hashing.Sha256
