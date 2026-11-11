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
    (fun _ _ _ _ h => by first | exact h | trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ h => sha256_spec x.1 x.2 h

#print axioms sha256_master

end Library.Hashing.Sha256
