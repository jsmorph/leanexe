import Library.Hashing.Sha256.Compiled
import Library.Hashing.Sha256.Proof
import Verified.Call

/-! The bytes of the module `sha256` compute SHA-256 and SHA-224 of FIPS 180-4.  Each entry, called
from a ready store with a borrowed array `msg` and a byte count `n < 2 ^ 61`, returns without a
trap the four words of a digest whose bytes, read most significant bit first, are the digest of
the first `n` bytes of `msg` in `Library.Hashing.Sha2.Spec`.  A store is ready, as `Verified.Ready`
states, when the allocator invariant holds, the round constants are a borrowed array at their
address, and the memory cap is at most 65,535 pages.  The array stays borrowed, the store stays
ready, and every region of the heap before the call keeps its bytes.  The store in which the
module starts is ready.  `sha256_module` combines the two entries. -/

namespace Library.Hashing.Sha256

open Wasm LeanExe.Pipeline Library.Hashing.Words Library.Bytes
open SHS.Equiv.SHA256.Digest SHS.Equiv.SHA256.Padding.ByteDecoding SHS.Equiv.SHA256.Pipeline
open Verified (Ready)

theorem sha256_export :
    ({ name := "sha256", funcIdx := 11 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem sha224_export :
    ({ name := "sha224", funcIdx := 12 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 11, the export `sha256`, returns the four words of the SHA-256 digest. -/
theorem sha256_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (msg : Array UInt64) (n ptr : UInt64) (h : Ready compiled.module compiled.tables heap store)
    (hb : heap.Borrowed store ptr msg) (hn : n.toNat < 2 ^ 61) :
    Runs false env compiled.module 11 store [.i64 n, .i64 ptr] fun final values =>
      ∃ d : Words4,
        values.reverse = [.i64 d.w0, .i64 d.w1, .i64 d.w2, .i64 d.w3] ∧
        digestBitVec (d.bytes 32) = SHS.SHA256.sha256 (bytesToBitMessage (bytes msg n.toNat))
          (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact hn)) ∧
        ∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (Verified.ImplementsTables.call compiled.sha256.implements compiled.tables
    (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩) env heap store [.i64 ptr, .i64 n]
    (msg, n) h ⟨[.i64 ptr], [.i64 n], rfl, ⟨ptr, rfl, hb⟩, rfl⟩ rfl trivial).mono
    fun _ _ ⟨heap', hv, hR, hkept, hkeep, _⟩ =>
      ⟨sha256 msg n, hv, sha256_spec msg n hn, heap', hR, hkept _ _ hb, hkeep⟩

/-- Function 12, the export `sha224`, returns four words whose first 28 bytes are the SHA-224
digest. -/
theorem sha224_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (msg : Array UInt64) (n ptr : UInt64) (h : Ready compiled.module compiled.tables heap store)
    (hb : heap.Borrowed store ptr msg) (hn : n.toNat < 2 ^ 61) :
    Runs false env compiled.module 12 store [.i64 n, .i64 ptr] fun final values =>
      ∃ d : Words4,
        values.reverse = [.i64 d.w0, .i64 d.w1, .i64 d.w2, .i64 d.w3] ∧
        digestBitVec224 (d.bytes 28) = SHS.SHA256.sha224 (bytesToBitMessage (bytes msg n.toNat))
          (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact hn)) ∧
        ∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (Verified.ImplementsTables.call compiled.sha224.implements compiled.tables
    (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩) env heap store [.i64 ptr, .i64 n]
    (msg, n) h ⟨[.i64 ptr], [.i64 n], rfl, ⟨ptr, rfl, hb⟩, rfl⟩ rfl trivial).mono
    fun _ _ ⟨heap', hv, hR, hkept, hkeep, _⟩ =>
      ⟨sha224 msg n, hv, sha224_spec msg n hn, heap', hR, hkept _ _ hb, hkeep⟩

/-- The module's bytes decode to the module, whose exports `sha256` and `sha224` are functions 11
and 12, whose start store is ready, and whose two entries compute their digests from every ready
store, as the two call theorems state. -/
theorem sha256_module :
    (∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok compiled.module) ∧
      ({ name := "sha256", funcIdx := 11 } : Wasm.Export) ∈ compiled.module.exports ∧
      ({ name := "sha224", funcIdx := 12 } : Wasm.Export) ∈ compiled.module.exports ∧
      Ready compiled.module compiled.tables (Verified.initialHeap compiled.tables)
        compiled.module.initialStore ∧
      (∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (msg : Array UInt64)
        (n ptr : UInt64), Ready compiled.module compiled.tables heap store →
        heap.Borrowed store ptr msg → (hn : n.toNat < 2 ^ 61) →
        Runs false env compiled.module 11 store [.i64 n, .i64 ptr] fun final values =>
          ∃ d : Words4, values.reverse = [.i64 d.w0, .i64 d.w1, .i64 d.w2, .i64 d.w3] ∧
            digestBitVec (d.bytes 32) = SHS.SHA256.sha256 (bytesToBitMessage (bytes msg n.toNat))
              (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact hn)) ∧
            ∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
              heap'.Borrowed final ptr msg ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) ∧
      (∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (msg : Array UInt64)
        (n ptr : UInt64), Ready compiled.module compiled.tables heap store →
        heap.Borrowed store ptr msg → (hn : n.toNat < 2 ^ 61) →
        Runs false env compiled.module 12 store [.i64 n, .i64 ptr] fun final values =>
          ∃ d : Words4, values.reverse = [.i64 d.w0, .i64 d.w1, .i64 d.w2, .i64 d.w3] ∧
            digestBitVec224 (d.bytes 28) = SHS.SHA256.sha224 (bytesToBitMessage (bytes msg n.toNat))
              (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact hn)) ∧
            ∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
              heap'.Borrowed final ptr msg ∧
              ∀ r, heap.Region r → 0 < r.2 →
                (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                  heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled.bytes
  exact ⟨⟨bytes, henc, hdec⟩, sha256_export, sha224_export,
    Verified.Ready.initial rfl compiled.initial,
    fun env heap store msg n ptr h hb hn => sha256_call env heap store msg n ptr h hb hn,
    fun env heap store msg n ptr h hb hn => sha224_call env heap store msg n ptr h hb hn⟩

#print axioms sha256_call
#print axioms sha224_call
#print axioms sha256_module

end Library.Hashing.Sha256
