import Library.Hashing.Sha3.Compiled
import Library.Hashing.Sha3.ShakeProof
import Verified.Call

/-! The bytes of the module `sha3` compute the SHA-3 functions of FIPS 202.  A hash entry, called
from a ready store with a borrowed array `msg` and a byte count `n < 2 ^ 61`, returns without a
trap and without allocating the words of a digest whose bytes, read least significant bit first,
are the digest of the transcription `Library.Hashing.Sha3.Spec` for the first `n` bytes of `msg`
read in the same order.  A SHAKE entry, called also with an output length `d < 2 ^ 61` in bytes
and room in the heap for one block of `⌈d / 8⌉` words, returns without a trap an owned array of
`⌈d / 8⌉` words whose first `d` bytes are the transcription's output of `8 d` bits and whose other
bytes are zero.  A store is ready, as `Verified.Ready` states for a module without tables, when the
allocator invariant holds and the memory cap is at most 65,535 pages.  The message stays borrowed,
the store stays ready, and every region of the heap before the call keeps its bytes.  The store in
which the module starts is ready. -/

namespace Library.Hashing.Sha3

open Wasm LeanExe.Pipeline LeanExe.Runtime Library.Hashing.Words Library.Bytes
open Library.Hashing.Sha3.SpongeProof Library.Hashing.Sha3.Proof Library.Hashing.Sha3.ShakeProof
open Verified (Ready)

theorem sha3_224_export :
    ({ name := "sha3_224", funcIdx := 12 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem sha3_256_export :
    ({ name := "sha3_256", funcIdx := 13 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem sha3_384_export :
    ({ name := "sha3_384", funcIdx := 14 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem sha3_512_export :
    ({ name := "sha3_512", funcIdx := 15 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem shake128_export :
    ({ name := "shake128", funcIdx := 19 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem shake256_export :
    ({ name := "shake256", funcIdx := 20 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 12, the export `sha3_224`, returns four words whose first 28 bytes are the SHA3-224
digest. -/
theorem sha3_224_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (msg : Array UInt64) (n ptr : UInt64) (h : Ready compiled.module compiled.tables heap store)
    (hb : heap.Borrowed store ptr msg) (hn : n.toNat < 2 ^ 61) :
    Runs false env compiled.module 12 store [.i64 n, .i64 ptr] fun final values =>
      ∃ d : Words4,
        values.reverse = [.i64 d.w0, .i64 d.w1, .i64 d.w2, .i64 d.w3] ∧
        bitsOfBytes (d.bytes 28).toList = Spec.sha3_224 (messageBits msg n.toNat) ∧
        ∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (Verified.ImplementsTables.call (.ofA compiled.sha3_224.implements) compiled.tables nofun env
    heap store [.i64 ptr, .i64 n] (msg, n) h ⟨[.i64 ptr], [.i64 n], rfl, ⟨ptr, rfl, hb⟩, rfl⟩ rfl
    trivial).mono
    fun _ _ ⟨heap', hv, hR, hkept, hkeep, _⟩ =>
      ⟨sha3_224 msg n, hv, sha3_224_spec msg n hn, heap', hR, hkept _ _ hb, hkeep⟩

/-- Function 13, the export `sha3_256`, returns the four words of the SHA3-256 digest. -/
theorem sha3_256_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (msg : Array UInt64) (n ptr : UInt64) (h : Ready compiled.module compiled.tables heap store)
    (hb : heap.Borrowed store ptr msg) (hn : n.toNat < 2 ^ 61) :
    Runs false env compiled.module 13 store [.i64 n, .i64 ptr] fun final values =>
      ∃ d : Words4,
        values.reverse = [.i64 d.w0, .i64 d.w1, .i64 d.w2, .i64 d.w3] ∧
        bitsOfBytes (d.bytes 32).toList = Spec.sha3_256 (messageBits msg n.toNat) ∧
        ∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (Verified.ImplementsTables.call (.ofA compiled.sha3_256.implements) compiled.tables nofun env
    heap store [.i64 ptr, .i64 n] (msg, n) h ⟨[.i64 ptr], [.i64 n], rfl, ⟨ptr, rfl, hb⟩, rfl⟩ rfl
    trivial).mono
    fun _ _ ⟨heap', hv, hR, hkept, hkeep, _⟩ =>
      ⟨sha3_256 msg n, hv, sha3_256_spec msg n hn, heap', hR, hkept _ _ hb, hkeep⟩

/-- Function 14, the export `sha3_384`, returns the six words of the SHA3-384 digest. -/
theorem sha3_384_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (msg : Array UInt64) (n ptr : UInt64) (h : Ready compiled.module compiled.tables heap store)
    (hb : heap.Borrowed store ptr msg) (hn : n.toNat < 2 ^ 61) :
    Runs false env compiled.module 14 store [.i64 n, .i64 ptr] fun final values =>
      ∃ d : Words6,
        values.reverse = [.i64 d.w0, .i64 d.w1, .i64 d.w2, .i64 d.w3, .i64 d.w4, .i64 d.w5] ∧
        bitsOfBytes d.bytes.toList = Spec.sha3_384 (messageBits msg n.toNat) ∧
        ∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (Verified.ImplementsTables.call (.ofA compiled.sha3_384.implements) compiled.tables nofun env
    heap store [.i64 ptr, .i64 n] (msg, n) h ⟨[.i64 ptr], [.i64 n], rfl, ⟨ptr, rfl, hb⟩, rfl⟩ rfl
    trivial).mono
    fun _ _ ⟨heap', hv, hR, hkept, hkeep, _⟩ =>
      ⟨sha3_384 msg n, hv, sha3_384_spec msg n hn, heap', hR, hkept _ _ hb, hkeep⟩

/-- Function 15, the export `sha3_512`, returns the eight words of the SHA3-512 digest. -/
theorem sha3_512_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (msg : Array UInt64) (n ptr : UInt64) (h : Ready compiled.module compiled.tables heap store)
    (hb : heap.Borrowed store ptr msg) (hn : n.toNat < 2 ^ 61) :
    Runs false env compiled.module 15 store [.i64 n, .i64 ptr] fun final values =>
      ∃ d : Words8,
        values.reverse = [.i64 d.w0, .i64 d.w1, .i64 d.w2, .i64 d.w3, .i64 d.w4, .i64 d.w5,
          .i64 d.w6, .i64 d.w7] ∧
        bitsOfBytes d.bytes.toList = Spec.sha3_512 (messageBits msg n.toNat) ∧
        ∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (Verified.ImplementsTables.call (.ofA compiled.sha3_512.implements) compiled.tables nofun env
    heap store [.i64 ptr, .i64 n] (msg, n) h ⟨[.i64 ptr], [.i64 n], rfl, ⟨ptr, rfl, hb⟩, rfl⟩ rfl
    trivial).mono
    fun _ _ ⟨heap', hv, hR, hkept, hkeep, _⟩ =>
      ⟨sha3_512 msg n, hv, sha3_512_spec msg n hn, heap', hR, hkept _ _ hb, hkeep⟩

theorem words_toNat (d : UInt64) (hd : d.toNat < 2 ^ 61) :
    ((d + 7) / 8).toNat = (d.toNat + 7) / 8 :=
  (output_arith d 1 hd (by decide) (by decide)).1

/-- Function 19, the export `shake128`, returns an owned array of `⌈d / 8⌉` words whose first `d`
bytes are SHAKE128 of the message to `8 d` bits and whose other bytes are zero. -/
theorem shake128_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (msg : Array UInt64) (n d ptr : UInt64) (h : Ready compiled.module compiled.tables heap store)
    (hb : heap.Borrowed store ptr msg) (hn : n.toNat < 2 ^ 61) (hd : d.toNat < 2 ^ 61)
    (hroom : heap.Within store compiled.module (8 * ((d.toNat + 7) / 8) + 56)) :
    Runs false env compiled.module 19 store [.i64 d, .i64 n, .i64 ptr] fun final values =>
      ∃ optr : UInt64, values = [.i64 optr] ∧ ∃ heap' : Heap, ∃ out : Array UInt64,
        Ready compiled.module compiled.tables heap' final ∧ heap'.Owned final optr out ∧
        out.size = (d.toNat + 7) / 8 ∧
        bitsOfBytes ((List.range d.toNat).map (byteAt out)) =
          Spec.shake128 (messageBits msg n.toNat) (8 * d.toNat) ∧
        (∀ i, d.toNat ≤ i → byteAt out i = 0) ∧ heap'.Borrowed final ptr msg ∧
        (∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r ∧ regionsDisjoint r (block final optr)) ∧
        heap'.top.toNat ≤ heap.top.toNat + (8 * ((d.toNat + 7) / 8) + 56) :=
  have hbound : compiled.shake128.bound (msg, n, d) = 8 * ((d.toNat + 7) / 8) + 56 := by
    rw [compiled.shake128.bound_eq, compiled.shakeWith.bound_eq, Verified.blockCost_eq,
      words_toNat d hd]
  (Verified.Call.array
    (Verified.ImplementsTables.call (.ofA compiled.shake128.trapFree) compiled.tables nofun) env
    heap store [.i64 ptr, .i64 n, .i64 d] (msg, n, d) h
    ⟨[.i64 ptr], [.i64 n, .i64 d], rfl, ⟨ptr, rfl, hb⟩, rfl⟩ rfl (hbound ▸ hroom)).mono
    fun _ _ ⟨optr, hv, heap', hown, hR, hkept, hreg, htop⟩ =>
      ⟨optr, hv, heap', shake128 msg n d, hR, hown,
        shakeWith_size msg n d 21 hd (by decide) (by decide), shake128_spec msg n d hn hd,
        fun _ hi => shakeWith_tail msg n d 21 hd (by decide) (by decide) hi, hkept _ _ hb, hreg,
        hbound ▸ htop⟩

/-- Function 20, the export `shake256`, returns an owned array of `⌈d / 8⌉` words whose first `d`
bytes are SHAKE256 of the message to `8 d` bits and whose other bytes are zero. -/
theorem shake256_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (msg : Array UInt64) (n d ptr : UInt64) (h : Ready compiled.module compiled.tables heap store)
    (hb : heap.Borrowed store ptr msg) (hn : n.toNat < 2 ^ 61) (hd : d.toNat < 2 ^ 61)
    (hroom : heap.Within store compiled.module (8 * ((d.toNat + 7) / 8) + 56)) :
    Runs false env compiled.module 20 store [.i64 d, .i64 n, .i64 ptr] fun final values =>
      ∃ optr : UInt64, values = [.i64 optr] ∧ ∃ heap' : Heap, ∃ out : Array UInt64,
        Ready compiled.module compiled.tables heap' final ∧ heap'.Owned final optr out ∧
        out.size = (d.toNat + 7) / 8 ∧
        bitsOfBytes ((List.range d.toNat).map (byteAt out)) =
          Spec.shake256 (messageBits msg n.toNat) (8 * d.toNat) ∧
        (∀ i, d.toNat ≤ i → byteAt out i = 0) ∧ heap'.Borrowed final ptr msg ∧
        (∀ r, heap.Region r → 0 < r.2 →
          (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
            heap'.Region r ∧ regionsDisjoint r (block final optr)) ∧
        heap'.top.toNat ≤ heap.top.toNat + (8 * ((d.toNat + 7) / 8) + 56) :=
  have hbound : compiled.shake256.bound (msg, n, d) = 8 * ((d.toNat + 7) / 8) + 56 := by
    rw [compiled.shake256.bound_eq, compiled.shakeWith.bound_eq, Verified.blockCost_eq,
      words_toNat d hd]
  (Verified.Call.array
    (Verified.ImplementsTables.call (.ofA compiled.shake256.trapFree) compiled.tables nofun) env
    heap store [.i64 ptr, .i64 n, .i64 d] (msg, n, d) h
    ⟨[.i64 ptr], [.i64 n, .i64 d], rfl, ⟨ptr, rfl, hb⟩, rfl⟩ rfl (hbound ▸ hroom)).mono
    fun _ _ ⟨optr, hv, heap', hown, hR, hkept, hreg, htop⟩ =>
      ⟨optr, hv, heap', shake256 msg n d, hR, hown,
        shakeWith_size msg n d 17 hd (by decide) (by decide), shake256_spec msg n d hn hd,
        fun _ hi => shakeWith_tail msg n d 17 hd (by decide) (by decide) hi, hkept _ _ hb, hreg,
        hbound ▸ htop⟩

#print axioms sha3_224_call
#print axioms sha3_256_call
#print axioms sha3_384_call
#print axioms sha3_512_call
#print axioms shake128_call
#print axioms shake256_call

end Library.Hashing.Sha3
