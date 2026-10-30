import Library.Hashing.SipHash.Compiled
import Library.Hashing.SipHash.Proof
import Verified.Call

/-! The bytes of the module `siphash` compute SipHash-2-4 and SipHash-1-3.  An entry, called from a
ready store with the key words `k0` and `k1`, a borrowed array `msg`, and a byte count `n`, returns
without a trap the word that the transcription `Library.Hashing.SipHash.Spec` gives for the key
whose 16 bytes are those of `k0` and then `k1`, least significant first, and for the first `n`
bytes of `msg`.  A store is ready, as `Verified.Ready` states for a module without tables, when the
allocator invariant holds and the memory cap is at most 65,535 pages.  The array stays borrowed,
the store stays ready, and every region of the heap before the call keeps its bytes.  The store in
which the module starts is ready. -/

namespace Library.Hashing.SipHash

open Wasm LeanExe.Pipeline LeanExe.Runtime Library.Bytes
open Verified (Ready)

theorem siphash24_export :
    ({ name := "siphash24", funcIdx := 7 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem siphash13_export :
    ({ name := "siphash13", funcIdx := 8 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 7, the export `siphash24`, returns SipHash-2-4 of the key bytes of `k0` and `k1` and
the first `n` bytes of `msg`. -/
theorem siphash24_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (k0 k1 : UInt64)
    (msg : Array UInt64) (n ptr : UInt64) (h : Ready compiled.module compiled.tables heap store)
    (hb : heap.Borrowed store ptr msg) :
    Runs false env compiled.module 7 store [.i64 n, .i64 ptr, .i64 k1, .i64 k0] fun final values =>
      ∃ t : UInt64, values.reverse = [.i64 t] ∧
        t = Spec.sipHash 2 4 ((List.range 16).map (byteAt #[k0, k1]))
          ((List.range n.toNat).map (byteAt msg)) ∧
        ∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (Verified.ImplementsTables.call (.ofA compiled.siphash24.implements) compiled.tables nofun env
    heap store [.i64 k0, .i64 k1, .i64 ptr, .i64 n] (k0, k1, msg, n) h
    ⟨[.i64 k0], [.i64 k1, .i64 ptr, .i64 n], rfl, rfl, [.i64 k1], [.i64 ptr, .i64 n], rfl, rfl,
      [.i64 ptr], [.i64 n], rfl, ⟨ptr, rfl, hb⟩, rfl⟩ rfl trivial).mono
    fun _ _ ⟨heap', hv, hR, hkept, hkeep, _⟩ =>
      ⟨siphash24 k0 k1 msg n, hv, Proof.siphash24_spec k0 k1 msg n, heap', hR, hkept _ _ hb,
        hkeep⟩

/-- Function 8, the export `siphash13`, returns SipHash-1-3 of the key bytes of `k0` and `k1` and
the first `n` bytes of `msg`. -/
theorem siphash13_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (k0 k1 : UInt64)
    (msg : Array UInt64) (n ptr : UInt64) (h : Ready compiled.module compiled.tables heap store)
    (hb : heap.Borrowed store ptr msg) :
    Runs false env compiled.module 8 store [.i64 n, .i64 ptr, .i64 k1, .i64 k0] fun final values =>
      ∃ t : UInt64, values.reverse = [.i64 t] ∧
        t = Spec.sipHash 1 3 ((List.range 16).map (byteAt #[k0, k1]))
          ((List.range n.toNat).map (byteAt msg)) ∧
        ∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (Verified.ImplementsTables.call (.ofA compiled.siphash13.implements) compiled.tables nofun env
    heap store [.i64 k0, .i64 k1, .i64 ptr, .i64 n] (k0, k1, msg, n) h
    ⟨[.i64 k0], [.i64 k1, .i64 ptr, .i64 n], rfl, rfl, [.i64 k1], [.i64 ptr, .i64 n], rfl, rfl,
      [.i64 ptr], [.i64 n], rfl, ⟨ptr, rfl, hb⟩, rfl⟩ rfl trivial).mono
    fun _ _ ⟨heap', hv, hR, hkept, hkeep, _⟩ =>
      ⟨siphash13 k0 k1 msg n, hv, Proof.siphash13_spec k0 k1 msg n, heap', hR, hkept _ _ hb,
        hkeep⟩

#print axioms siphash24_call
#print axioms siphash13_call

end Library.Hashing.SipHash
