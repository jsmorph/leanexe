import Library.Hashing.Hmac.Compiled
import Library.Hashing.Hmac.Proof256
import Library.Hashing.Hmac.Proof512
import Verified.Call

/-! The bytes of the modules `hmac_sha256` and `hmac_sha512` compute HMAC-SHA-256 and
HMAC-SHA-512 of FIPS 198-1.  Each entry, called from a ready store with a borrowed key array `key`
of `kn < 2 ^ 61` bytes and a borrowed message array `msg` of `n` bytes, returns without a trap the
words of a digest whose bytes, read most significant bit first, are the HMAC of
`Library.Hashing.Hmac.Spec` for the bits of the first `kn` bytes of `key` and the first `n` bytes
of `msg`.  The message count satisfies `n + 64 < 2 ^ 61` for SHA-256 and `n + 128 < 2 ^ 61` for
SHA-512, the limit of FIPS 180-4 for the inner message.  A store is ready, as `Verified.Ready`
states, when the allocator invariant holds, the module's round constants are a borrowed array at
their address, and the memory cap is at most 65,535 pages.  The arrays stay borrowed, the store
stays ready, and every region of the heap before the call keeps its bytes.  The store in which each
module starts is ready. -/

namespace Library.Hashing.Hmac

open Wasm LeanExe.Pipeline Library.Hashing.Words Library.Bytes
open Verified (Ready)

theorem hmacSha256_export :
    ({ name := "hmacSha256", funcIdx := 13 } : Wasm.Export) ∈ compiled256.module.exports := by
  decide +kernel

theorem hmacSha512_export :
    ({ name := "hmacSha512", funcIdx := 13 } : Wasm.Export) ∈ compiled512.module.exports := by
  decide +kernel

/-- Function 13 of `hmac_sha256`, the export `hmacSha256`, returns the four words of the
HMAC-SHA-256 digest. -/
theorem hmacSha256_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (key : Array UInt64) (kn kptr : UInt64) (msg : Array UInt64) (n mptr : UInt64)
    (h : Ready compiled256.module compiled256.tables heap store)
    (hk : heap.Borrowed store kptr key) (hm : heap.Borrowed store mptr msg)
    (hkn : kn.toNat < 2 ^ 61) (hn : n.toNat + 64 < 2 ^ 61) :
    Runs false env compiled256.module 13 store [.i64 n, .i64 mptr, .i64 kn, .i64 kptr]
      fun final values =>
        ∃ d : Words4,
          values.reverse = [.i64 d.w0, .i64 d.w1, .i64 d.w2, .i64 d.w3] ∧
          SHS.Equiv.SHA256.Digest.digestBitVec (d.bytes 32) =
            Spec.hmacSha256 (bits (bytes key kn.toNat)) (bits (bytes msg n.toNat)) ∧
          ∃ heap' : Heap, Ready compiled256.module compiled256.tables heap' final ∧
            heap'.Borrowed final kptr key ∧ heap'.Borrowed final mptr msg ∧
            ∀ r, heap.Region r → 0 < r.2 →
              (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                heap'.Region r :=
  (Verified.ImplementsTables.call compiled256.hmacSha256.implements compiled256.tables
    (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩) env heap store
    [.i64 kptr, .i64 kn, .i64 mptr, .i64 n] (key, kn, msg, n) h
    ⟨[.i64 kptr], [.i64 kn, .i64 mptr, .i64 n], rfl, ⟨kptr, rfl, hk⟩,
      ⟨[.i64 kn], [.i64 mptr, .i64 n], rfl, rfl,
        ⟨[.i64 mptr], [.i64 n], rfl, ⟨mptr, rfl, hm⟩, rfl⟩⟩⟩
    rfl trivial).mono fun _ _ ⟨heap', hv, hR, hkept, hkeep, _⟩ =>
      ⟨hmacSha256 key kn msg n, hv, hmacSha256_spec key kn msg n hkn hn, heap', hR,
        hkept _ _ hk, hkept _ _ hm, hkeep⟩

/-- Function 13 of `hmac_sha512`, the export `hmacSha512`, returns the eight words of the
HMAC-SHA-512 digest. -/
theorem hmacSha512_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (key : Array UInt64) (kn kptr : UInt64) (msg : Array UInt64) (n mptr : UInt64)
    (h : Ready compiled512.module compiled512.tables heap store)
    (hk : heap.Borrowed store kptr key) (hm : heap.Borrowed store mptr msg)
    (hkn : kn.toNat < 2 ^ 61) (hn : n.toNat + 128 < 2 ^ 61) :
    Runs false env compiled512.module 13 store [.i64 n, .i64 mptr, .i64 kn, .i64 kptr]
      fun final values =>
        ∃ d : Words8,
          values.reverse = [.i64 d.w0, .i64 d.w1, .i64 d.w2, .i64 d.w3, .i64 d.w4, .i64 d.w5,
            .i64 d.w6, .i64 d.w7] ∧
          SHS.Equiv.SHA512.Digest.digestBitVec512 d.bytes =
            Spec.hmacSha512 (bits (bytes key kn.toNat)) (bits (bytes msg n.toNat)) ∧
          ∃ heap' : Heap, Ready compiled512.module compiled512.tables heap' final ∧
            heap'.Borrowed final kptr key ∧ heap'.Borrowed final mptr msg ∧
            ∀ r, heap.Region r → 0 < r.2 →
              (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                heap'.Region r :=
  (Verified.ImplementsTables.call compiled512.hmacSha512.implements compiled512.tables
    (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩) env heap store
    [.i64 kptr, .i64 kn, .i64 mptr, .i64 n] (key, kn, msg, n) h
    ⟨[.i64 kptr], [.i64 kn, .i64 mptr, .i64 n], rfl, ⟨kptr, rfl, hk⟩,
      ⟨[.i64 kn], [.i64 mptr, .i64 n], rfl, rfl,
        ⟨[.i64 mptr], [.i64 n], rfl, ⟨mptr, rfl, hm⟩, rfl⟩⟩⟩
    rfl trivial).mono fun _ _ ⟨heap', hv, hR, hkept, hkeep, _⟩ =>
      ⟨hmacSha512 key kn msg n, hv, hmacSha512_spec key kn msg n hkn hn, heap', hR,
        hkept _ _ hk, hkept _ _ hm, hkeep⟩

/-- The bytes of `hmac_sha256` decode to the module, whose export `hmacSha256` is function 13,
whose start store is ready, and whose entry computes HMAC-SHA-256 from every ready store, as
`hmacSha256_call` states. -/
theorem hmacSha256_module :
    (∃ bytes, Wasm.Encoding.encode compiled256.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok compiled256.module) ∧
      ({ name := "hmacSha256", funcIdx := 13 } : Wasm.Export) ∈ compiled256.module.exports ∧
      Ready compiled256.module compiled256.tables (Verified.initialHeap compiled256.tables)
        compiled256.module.initialStore ∧
      (∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (key : Array UInt64)
        (kn kptr : UInt64) (msg : Array UInt64) (n mptr : UInt64),
        Ready compiled256.module compiled256.tables heap store →
        heap.Borrowed store kptr key → heap.Borrowed store mptr msg →
        kn.toNat < 2 ^ 61 → n.toNat + 64 < 2 ^ 61 →
        Runs false env compiled256.module 13 store [.i64 n, .i64 mptr, .i64 kn, .i64 kptr]
          fun final values =>
            ∃ d : Words4, values.reverse = [.i64 d.w0, .i64 d.w1, .i64 d.w2, .i64 d.w3] ∧
              SHS.Equiv.SHA256.Digest.digestBitVec (d.bytes 32) =
                Spec.hmacSha256 (bits (bytes key kn.toNat)) (bits (bytes msg n.toNat)) ∧
              ∃ heap' : Heap, Ready compiled256.module compiled256.tables heap' final ∧
                heap'.Borrowed final kptr key ∧ heap'.Borrowed final mptr msg ∧
                ∀ r, heap.Region r → 0 < r.2 →
                  (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                    heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled256.bytes
  exact ⟨⟨bytes, henc, hdec⟩, hmacSha256_export, Verified.Ready.initial rfl compiled256.initial,
    fun env heap store key kn kptr msg n mptr h hk hm hkn hn =>
      hmacSha256_call env heap store key kn kptr msg n mptr h hk hm hkn hn⟩

/-- The bytes of `hmac_sha512` decode to the module, whose export `hmacSha512` is function 13,
whose start store is ready, and whose entry computes HMAC-SHA-512 from every ready store, as
`hmacSha512_call` states. -/
theorem hmacSha512_module :
    (∃ bytes, Wasm.Encoding.encode compiled512.module = .ok bytes ∧
      Wasm.Encoding.decode bytes = .ok compiled512.module) ∧
      ({ name := "hmacSha512", funcIdx := 13 } : Wasm.Export) ∈ compiled512.module.exports ∧
      Ready compiled512.module compiled512.tables (Verified.initialHeap compiled512.tables)
        compiled512.module.initialStore ∧
      (∀ (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (key : Array UInt64)
        (kn kptr : UInt64) (msg : Array UInt64) (n mptr : UInt64),
        Ready compiled512.module compiled512.tables heap store →
        heap.Borrowed store kptr key → heap.Borrowed store mptr msg →
        kn.toNat < 2 ^ 61 → n.toNat + 128 < 2 ^ 61 →
        Runs false env compiled512.module 13 store [.i64 n, .i64 mptr, .i64 kn, .i64 kptr]
          fun final values =>
            ∃ d : Words8, values.reverse = [.i64 d.w0, .i64 d.w1, .i64 d.w2, .i64 d.w3,
                .i64 d.w4, .i64 d.w5, .i64 d.w6, .i64 d.w7] ∧
              SHS.Equiv.SHA512.Digest.digestBitVec512 d.bytes =
                Spec.hmacSha512 (bits (bytes key kn.toNat)) (bits (bytes msg n.toNat)) ∧
              ∃ heap' : Heap, Ready compiled512.module compiled512.tables heap' final ∧
                heap'.Borrowed final kptr key ∧ heap'.Borrowed final mptr msg ∧
                ∀ r, heap.Region r → 0 < r.2 →
                  (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
                    heap'.Region r) := by
  obtain ⟨bytes, henc, hdec, _⟩ := compiled512.bytes
  exact ⟨⟨bytes, henc, hdec⟩, hmacSha512_export, Verified.Ready.initial rfl compiled512.initial,
    fun env heap store key kn kptr msg n mptr h hk hm hkn hn =>
      hmacSha512_call env heap store key kn kptr msg n mptr h hk hm hkn hn⟩

#print axioms hmacSha256_call
#print axioms hmacSha512_call
#print axioms hmacSha256_module
#print axioms hmacSha512_module

end Library.Hashing.Hmac
