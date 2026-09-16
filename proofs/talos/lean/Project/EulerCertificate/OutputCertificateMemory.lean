import Project.EulerCertificate.OutputSpec
import Project.ProofKit.ArrayPrefix
import Project.ProofKit.FixedArrayResult

namespace Project.EulerCertificate.Execution
open Wasm Project.ProofKit
open Project.EulerCertificate.Flux (Vector)

def outputCertificateWords (r : Vector) : Array UInt64 := (Solve.certificateWords r).toArray

def outputCertificateWrites (store : Store Unit) (root : UInt64) (r : Vector) : Store Unit :=
  let written0 := UInt64Array.writeElement store root 0 r.mass.status
  let written1 := UInt64Array.writeElement written0 root 1 r.mass.lower
  let written2 := UInt64Array.writeElement written1 root 2 r.mass.upper
  let written3 := UInt64Array.writeElement written2 root 3 r.momentum.status
  let written4 := UInt64Array.writeElement written3 root 4 r.momentum.lower
  let written5 := UInt64Array.writeElement written4 root 5 r.momentum.upper
  let written6 := UInt64Array.writeElement written5 root 6 r.transverse.status
  let written7 := UInt64Array.writeElement written6 root 7 r.transverse.lower
  let written8 := UInt64Array.writeElement written7 root 8 r.transverse.upper
  let written9 := UInt64Array.writeElement written8 root 9 r.energy.status
  let written10 := UInt64Array.writeElement written9 root 10 r.energy.lower
  let written11 := UInt64Array.writeElement written10 root 11 r.energy.upper
  written11

theorem output_certificate_words (store : Store Unit) (root : UInt64) (r : Vector)
    (hFit : root.toNat + 104 ≤ 4294967296)
    (hMemory : root.toNat + 104 ≤ store.mem.pages * 65536)
    (hLength : store.mem.read64 root.toUInt32 = 12) :
    UInt64Array.At (outputCertificateWrites store root r) root (outputCertificateWords r) := by
  have h0 := UInt64Array.PrefixAt.empty store root (outputCertificateWords r) hFit hMemory hLength
  have h1 := h0.write_next (by simp [outputCertificateWords, Solve.certificateWords])
  have h2 := h1.write_next (by simp [outputCertificateWords, Solve.certificateWords])
  have h3 := h2.write_next (by simp [outputCertificateWords, Solve.certificateWords])
  have h4 := h3.write_next (by simp [outputCertificateWords, Solve.certificateWords])
  have h5 := h4.write_next (by simp [outputCertificateWords, Solve.certificateWords])
  have h6 := h5.write_next (by simp [outputCertificateWords, Solve.certificateWords])
  have h7 := h6.write_next (by simp [outputCertificateWords, Solve.certificateWords])
  have h8 := h7.write_next (by simp [outputCertificateWords, Solve.certificateWords])
  have h9 := h8.write_next (by simp [outputCertificateWords, Solve.certificateWords])
  have h10 := h9.write_next (by simp [outputCertificateWords, Solve.certificateWords])
  have h11 := h10.write_next (by simp [outputCertificateWords, Solve.certificateWords])
  have h12 := h11.write_next (by simp [outputCertificateWords, Solve.certificateWords])
  exact h12.complete

theorem output_certificate_writes_frame (store : Store Unit) (root : UInt64) (r : Vector)
    (hFit : root.toNat + 104 ≤ 4294967296) :
    ProofKit.Memory.WritesRange store (outputCertificateWrites store root r)
      root.toNat (root.toNat + 104) := by
  have h0 := UInt64Array.writeElement_frame store root 12 0 r.mass.status hFit (by decide)
  have h1 := h0.trans (UInt64Array.writeElement_frame _ root 12 1 r.mass.lower hFit (by decide))
  have h2 := h1.trans (UInt64Array.writeElement_frame _ root 12 2 r.mass.upper hFit (by decide))
  have h3 := h2.trans (UInt64Array.writeElement_frame _ root 12 3 r.momentum.status hFit (by decide))
  have h4 := h3.trans (UInt64Array.writeElement_frame _ root 12 4 r.momentum.lower hFit (by decide))
  have h5 := h4.trans (UInt64Array.writeElement_frame _ root 12 5 r.momentum.upper hFit (by decide))
  have h6 := h5.trans (UInt64Array.writeElement_frame _ root 12 6 r.transverse.status hFit (by decide))
  have h7 := h6.trans (UInt64Array.writeElement_frame _ root 12 7 r.transverse.lower hFit (by decide))
  have h8 := h7.trans (UInt64Array.writeElement_frame _ root 12 8 r.transverse.upper hFit (by decide))
  have h9 := h8.trans (UInt64Array.writeElement_frame _ root 12 9 r.energy.status hFit (by decide))
  have h10 := h9.trans (UInt64Array.writeElement_frame _ root 12 10 r.energy.lower hFit (by decide))
  have h11 := h10.trans (UInt64Array.writeElement_frame _ root 12 11 r.energy.upper hFit (by decide))
  exact h11

def outputCertificateStore (store : Store Unit) (root : UInt64) (r : Vector) : Store Unit :=
  outputCertificateWrites (FixedArrayResult.writeLength store root 12) root r

theorem output_certificate_store_words (store : Store Unit) (root : UInt64) (r : Vector)
    (hFit : root.toNat + 104 ≤ 4294967296)
    (hMemory : root.toNat + 104 ≤ store.mem.pages * 65536) :
    UInt64Array.At (outputCertificateStore store root r) root (outputCertificateWords r) :=
  output_certificate_words _ root r hFit hMemory (ProofKit.Memory.read64_write64 ..)

theorem output_certificate_store_frame (store : Store Unit) (root : UInt64) (r : Vector)
    (hFit : root.toNat + 104 ≤ 4294967296) :
    ProofKit.Memory.WritesRange store (outputCertificateStore store root r)
      root.toNat (root.toNat + 104) := by
  have hAddress : root.toUInt32.toNat = root.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have hLength := ProofKit.Memory.WritesRange.write64 store root.toUInt32 12
    root.toNat (root.toNat + 104) (by rw [hAddress]) (by rw [hAddress]; omega)
  exact hLength.trans (output_certificate_writes_frame _ root r hFit)

#print axioms output_certificate_words
#print axioms output_certificate_writes_frame
#print axioms output_certificate_store_words
#print axioms output_certificate_store_frame
end Project.EulerCertificate.Execution
