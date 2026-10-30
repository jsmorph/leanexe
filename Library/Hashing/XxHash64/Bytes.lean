import Library.Hashing.XxHash64.Compiled
import Library.Hashing.XxHash64.Proof
import Verified.Call

/-! The bytes of the module `xxhash64` compute XXH64.  The entry, called from a ready store with a
borrowed array `msg`, a byte count `n`, and a seed, returns without a trap the word that the
transcription `Library.Hashing.XxHash64.Spec` gives for the first `n` bytes of `msg` and the seed.
A store is ready, as `Verified.Ready` states for a module without tables, when the allocator
invariant holds and the memory cap is at most 65,535 pages.  The array stays borrowed, the store
stays ready, and every region of the heap before the call keeps its bytes.  The store in which the
module starts is ready. -/

namespace Library.Hashing.XxHash64

open Wasm LeanExe.Pipeline LeanExe.Runtime Library.Bytes
open Verified (Ready)

theorem xxh64_export :
    ({ name := "xxh64", funcIdx := 5 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- Function 5, the export `xxh64`, returns XXH64 of the first `n` bytes of `msg` with the seed
`seed`. -/
theorem xxh64_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit) (msg : Array UInt64)
    (n seed ptr : UInt64) (h : Ready compiled.module compiled.tables heap store)
    (hb : heap.Borrowed store ptr msg) :
    Runs false env compiled.module 5 store [.i64 seed, .i64 n, .i64 ptr] fun final values =>
      ∃ d : UInt64, values.reverse = [.i64 d] ∧
        d = Spec.xxh64 ((List.range n.toNat).map (byteAt msg)) seed ∧
        ∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          heap'.Borrowed final ptr msg ∧
          ∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r :=
  (Verified.ImplementsTables.call (.ofA compiled.xxh64.implements) compiled.tables nofun env heap
    store [.i64 ptr, .i64 n, .i64 seed] (msg, n, seed) h
    ⟨[.i64 ptr], [.i64 n, .i64 seed], rfl, ⟨ptr, rfl, hb⟩, rfl⟩ rfl trivial).mono
    fun _ _ ⟨heap', hv, hR, hkept, hkeep, _⟩ =>
      ⟨xxh64 msg n seed, hv, Proof.xxh64_eq msg n seed, heap', hR, hkept _ _ hb, hkeep⟩

#print axioms xxh64_call

end Library.Hashing.XxHash64
