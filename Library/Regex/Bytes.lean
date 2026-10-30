import Library.Regex.Compiled
import Library.Regex.Proof
import Verified.Call

/-! The bytes of the module `regex` match regular expressions given at run time.  The entry
`matchWith`, called from a ready store with a borrowed pattern array `pat`, a word count `pn` with
`3 pn < 2 ^ 64`, a borrowed input array `msg`, a byte count `n`, and room in the heap for
`24 pn + 21272` bytes, returns without a trap the code of `Library.Regex.Spec.answer` for the
first `pn` words of `pat` and the first `n` bytes of `msg`: 2 when the pattern does not decode,
3 when it has more than 63 sets of bytes, and 1 or 0 for whether the input is in the pattern's
language.  A read past the end of either array gives zero, as in the specification's words and
bytes.  A store is ready, as `Verified.Ready` states for a module without tables, when the
allocator invariant holds and the memory cap is at most 65,535 pages.  The arrays stay borrowed,
the store stays ready, every region of the heap before the call keeps its bytes, and the heap's
top grows by at most `24 pn + 21272` bytes.  The store in which the module starts is ready. -/

namespace Library.Regex

open Wasm LeanExe.Pipeline Library.Bytes
open Verified (Ready)

theorem matchWith_export :
    ({ name := "matchWith", funcIdx := 8 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The allocation bound of `matchWith`: blocks for the scan's stack of `3 pn` words, its follow
table of 64 words, and its 256 words of sets, and, for a pattern that decodes with at most 63
sets, the 2,048 words of `steps` and the 256 of `masks`, each block with a header of 48 bytes and
a length word. -/
theorem matchWith_bound (pat msg : Array UInt64) (pn n : UInt64) (hpn : 3 * pn.toNat < 2 ^ 64) :
    compiled.matchWith.bound (pat, pn, msg, n) ≤ 24 * pn.toNat + 21272 := by
  have h3 : (3 * pn).toNat = 3 * pn.toNat := by
    rw [UInt64.toNat_mul, show (3 : UInt64).toNat = 3 from rfl]; omega
  rw [compiled.matchWith.bound_eq, compiled.scan.bound_eq, compiled.steps.bound_eq,
    compiled.masks.bound_eq]
  simp only [Verified.blockCost_eq, h3, show UInt64.toNat 64 = 64 from rfl,
    show UInt64.toNat 256 = 256 from rfl, show UInt64.toNat 2048 = 2048 from rfl]
  split
  · omega
  · split <;> omega

/-- Function 8, the export `matchWith`, returns the answer of the specification. -/
theorem matchWith_call (env : HostEnv Unit) (heap : Heap) (store : Store Unit)
    (pat : Array UInt64) (pn pptr : UInt64) (msg : Array UInt64) (n mptr : UInt64)
    (h : Ready compiled.module compiled.tables heap store) (hp : heap.Borrowed store pptr pat)
    (hm : heap.Borrowed store mptr msg)
    (hroom : heap.Within store compiled.module (24 * pn.toNat + 21272))
    (hpn : 3 * pn.toNat < 2 ^ 64) :
    Runs false env compiled.module 8 store [.i64 n, .i64 mptr, .i64 pn, .i64 pptr]
      fun final values =>
        values.reverse = [.i64 (Spec.answer ((List.range pn.toNat).map (fun j => pat[j]!))
          ((List.range n.toNat).map (byteAt msg)))] ∧
        ∃ heap' : Heap, Ready compiled.module compiled.tables heap' final ∧
          heap'.Borrowed final pptr pat ∧ heap'.Borrowed final mptr msg ∧
          (∀ r, heap.Region r → 0 < r.2 →
            (∀ a, r.1 ≤ a → a < r.1 + r.2 → final.mem.bytes a = store.mem.bytes a) ∧
              heap'.Region r) ∧
          heap'.top.toNat ≤ heap.top.toNat + (24 * pn.toNat + 21272) :=
  have hbound := matchWith_bound pat msg pn n hpn
  (Verified.ImplementsTables.call (.ofA compiled.matchWith.trapFree) compiled.tables nofun env
    heap store [.i64 pptr, .i64 pn, .i64 mptr, .i64 n] (pat, pn, msg, n) h
    ⟨[.i64 pptr], [.i64 pn, .i64 mptr, .i64 n], rfl, ⟨pptr, rfl, hp⟩,
      ⟨[.i64 pn], [.i64 mptr, .i64 n], rfl, rfl,
        ⟨[.i64 mptr], [.i64 n], rfl, ⟨mptr, rfl, hm⟩, rfl⟩⟩⟩
    rfl (hroom.mono hbound)).mono fun _ _ ⟨heap', hv, hR, hkept, hkeep, _, htop⟩ =>
      ⟨Proof.matchWith_eq pat msg pn n hpn ▸ hv, heap', hR, hkept _ _ hp, hkept _ _ hm, hkeep,
        by omega⟩

#print axioms matchWith_bound
#print axioms matchWith_call

end Library.Regex
