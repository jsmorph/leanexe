import Library.Hashing.Sha256.Bytes
import Verified.Master

namespace Library.Hashing.Sha256

open Library.Hashing.Words Library.Bytes
open SHS.Equiv.SHA256.Digest SHS.Equiv.SHA256.Padding.ByteDecoding SHS.Equiv.SHA256.Pipeline

/-- The export `sha256`, called on an array `msg` and a byte count `n < 2 ^ 61`, returns four
words whose 32 bytes are the SHA-256 digest of FIPS 180-4 of the first `n` bytes of `msg`. -/
theorem sha256_master :
    Verified.Master compiled.module compiled.tables "sha256" compiled.sha256.bound
      (fun x : Array UInt64 × UInt64 => x.2.toNat < 2 ^ 61)
      (fun x (d : Words4) => ∀ h : x.2.toNat < 2 ^ 61,
        digestBitVec (d.bytes 32) = SHS.SHA256.sha256 (bytesToBitMessage (bytes x.1 x.2.toNat))
          (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact h))) :=
  .of_trapFree compiled.sha256.trapFree (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩) sha256_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ h => sha256_spec x.1 x.2 h

#print axioms sha256_master

theorem sha224_w3 (msg : Array UInt64) (n : UInt64) : (sha224 msg n).w3.toNat < 2 ^ 32 := by
  show (bswap _ >>> 32).toNat < 2 ^ 32
  rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  have := (bswap (hashFrom roundConstants iv224 msg n n).w6).toNat_lt
  simp only [UInt64.reduceToNat, Nat.reduceMod]
  omega

/-- The export `sha224`, called on an array `msg` and a byte count `n < 2 ^ 61`, returns four
words whose first 28 bytes are the SHA-224 digest of FIPS 180-4 of the first `n` bytes of `msg`
and whose fourth word is below `2 ^ 32`, so that its last four bytes are zero. -/
theorem sha224_master :
    Verified.Master compiled.module compiled.tables "sha224" compiled.sha224.bound
      (fun x : Array UInt64 × UInt64 => x.2.toNat < 2 ^ 61)
      (fun x (d : Words4) => (∀ h : x.2.toNat < 2 ^ 61,
        digestBitVec224 (d.bytes 28) = SHS.SHA256.sha224 (bytesToBitMessage (bytes x.1 x.2.toNat))
          (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact h))) ∧ d.w3.toNat < 2 ^ 32) :=
  .of_trapFree compiled.sha224.trapFree (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩)
    sha224_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => ⟨fun h => sha224_spec x.1 x.2 h, sha224_w3 x.1 x.2⟩

#print axioms sha224_master

end Library.Hashing.Sha256
