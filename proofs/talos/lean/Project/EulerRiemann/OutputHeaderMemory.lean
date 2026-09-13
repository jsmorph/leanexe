import Project.ProofKit.ArrayPrefix
import Project.ProofKit.FixedArrayResult

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

def outputHeaderWords (n time status : UInt64) : Array UInt64 := #[status, time, n, n]

def outputHeaderWrites (store : Store Unit) (root n time status : UInt64) : Store Unit :=
  UInt64Array.writeElement
    (UInt64Array.writeElement
      (UInt64Array.writeElement (UInt64Array.writeElement store root 0 status) root 1 time) root 2 n)
    root 3 n

theorem output_header_words (store : Store Unit) (root n time status : UInt64)
    (hFit : root.toNat + 40 ≤ 4294967296)
    (hMemory : root.toNat + 40 ≤ store.mem.pages * 65536)
    (hLength : store.mem.read64 root.toUInt32 = 4) :
    UInt64Array.At (outputHeaderWrites store root n time status) root (outputHeaderWords n time status) := by
  have h0 := UInt64Array.PrefixAt.empty store root (outputHeaderWords n time status) hFit hMemory hLength
  have h1 := h0.write_next (by simp [outputHeaderWords])
  have h2 := h1.write_next (by simp [outputHeaderWords])
  have h3 := h2.write_next (by simp [outputHeaderWords])
  have h4 := h3.write_next (by simp [outputHeaderWords])
  exact h4.complete

theorem output_header_writes_frame (store : Store Unit) (root n time status : UInt64)
    (hFit : root.toNat + 40 ≤ 4294967296) :
    ProofKit.Memory.WritesRange store (outputHeaderWrites store root n time status)
      root.toNat (root.toNat + 40) := by
  have h0 := UInt64Array.writeElement_frame store root 4 0 status hFit (by decide)
  have h1 := h0.trans (UInt64Array.writeElement_frame _ root 4 1 time hFit (by decide))
  have h2 := h1.trans (UInt64Array.writeElement_frame _ root 4 2 n hFit (by decide))
  exact h2.trans (UInt64Array.writeElement_frame _ root 4 3 n hFit (by decide))

def outputHeaderStore (store : Store Unit) (root n time status : UInt64) : Store Unit :=
  outputHeaderWrites (FixedArrayResult.writeLength store root 4) root n time status

theorem output_header_store_words (store : Store Unit) (root n time status : UInt64)
    (hFit : root.toNat + 40 ≤ 4294967296)
    (hMemory : root.toNat + 40 ≤ store.mem.pages * 65536) :
    UInt64Array.At (outputHeaderStore store root n time status) root (outputHeaderWords n time status) :=
  output_header_words _ root n time status hFit hMemory (ProofKit.Memory.read64_write64 ..)

theorem output_header_store_frame (store : Store Unit) (root n time status : UInt64)
    (hFit : root.toNat + 40 ≤ 4294967296) :
    ProofKit.Memory.WritesRange store (outputHeaderStore store root n time status)
      root.toNat (root.toNat + 40) := by
  have hAddress : root.toUInt32.toNat = root.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have hLength := ProofKit.Memory.WritesRange.write64 store root.toUInt32 4
    root.toNat (root.toNat + 40) (by rw [hAddress]) (by rw [hAddress]; omega)
  exact hLength.trans (output_header_writes_frame _ root n time status hFit)

#print axioms output_header_words
#print axioms output_header_writes_frame
#print axioms output_header_store_words
#print axioms output_header_store_frame

end Project.EulerRiemann.Execution
