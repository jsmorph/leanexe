import Library.Hashing.Sha512.Bytes
import Verified.Master

namespace Library.Hashing.Sha512

open Library.Hashing.Words Library.Bytes
open SHS.Equiv.SHA512.Digest SHS.Equiv.SHA512.Padding.ByteDecoding SHS.Equiv.SHA512.Pipeline

/-- The export `sha512`, called on an array `msg` and a byte count `n < 2 ^ 61`, returns eight
words whose 64 bytes are the SHA-512 digest of FIPS 180-4 of the first `n` bytes of `msg`. -/
theorem sha512_master :
    Verified.Master compiled.module compiled.tables "sha512" compiled.sha512.bound
      (fun x : Array UInt64 × UInt64 => x.2.toNat < 2 ^ 61)
      (fun x (d : Words8) => ∀ h : x.2.toNat < 2 ^ 61,
        digestBitVec512 d.bytes = SHS.SHA512.sha512 (bytesToBitMessage (bytes x.1 x.2.toNat))
          (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact h))) :=
  .of_trapFree compiled.sha512.trapFree (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩)
    sha512_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ h => sha512_spec x.1 x.2 h

#print axioms sha512_master

/-- The export `sha384`, called on an array `msg` and a byte count `n < 2 ^ 61`, returns six
words whose 48 bytes are the SHA-384 digest of FIPS 180-4 of the first `n` bytes of `msg`. -/
theorem sha384_master :
    Verified.Master compiled.module compiled.tables "sha384" compiled.sha384.bound
      (fun x : Array UInt64 × UInt64 => x.2.toNat < 2 ^ 61)
      (fun x (d : Words6) => ∀ h : x.2.toNat < 2 ^ 61,
        digestBitVec384 d.bytes = SHS.SHA512.sha384 (bytesToBitMessage (bytes x.1 x.2.toNat))
          (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact h))) :=
  .of_trapFree compiled.sha384.trapFree (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩)
    sha384_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ h => sha384_spec x.1 x.2 h

#print axioms sha384_master

/-- The export `sha512_256`, called on an array `msg` and a byte count `n < 2 ^ 61`, returns four
words whose 32 bytes are the SHA-512/256 digest of FIPS 180-4 of the first `n` bytes of `msg`. -/
theorem sha512_256_master :
    Verified.Master compiled.module compiled.tables "sha512_256" compiled.sha512_256.bound
      (fun x : Array UInt64 × UInt64 => x.2.toNat < 2 ^ 61)
      (fun x (d : Words4) => ∀ h : x.2.toNat < 2 ^ 61,
        digestBitVec512_256 (d.bytes 32) =
          SHS.SHA512.sha512_256 (bytesToBitMessage (bytes x.1 x.2.toNat))
            (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact h))) :=
  .of_trapFree compiled.sha512_256.trapFree
    (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩) sha512_256_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ h => sha512_256_spec x.1 x.2 h

#print axioms sha512_256_master

theorem sha512_224_w3 (msg : Array UInt64) (n : UInt64) :
    (sha512_224 msg n).w3.toNat < 2 ^ 32 := by
  show (bswap _ &&& 0xFFFFFFFF).toNat < 2 ^ 32
  rw [UInt64.toNat_and]
  exact Nat.and_lt_two_pow _ (by decide)

/-- The export `sha512_224`, called on an array `msg` and a byte count `n < 2 ^ 61`, returns four
words whose first 28 bytes are the SHA-512/224 digest of FIPS 180-4 of the first `n` bytes of
`msg` and whose fourth word is below `2 ^ 32`, so that its last four bytes are zero. -/
theorem sha512_224_master :
    Verified.Master compiled.module compiled.tables "sha512_224" compiled.sha512_224.bound
      (fun x : Array UInt64 × UInt64 => x.2.toNat < 2 ^ 61)
      (fun x (d : Words4) => (∀ h : x.2.toNat < 2 ^ 61,
        digestBitVec512_224 (d.bytes 28) =
          SHS.SHA512.sha512_224 (bytesToBitMessage (bytes x.1 x.2.toNat))
            (bitLen_lt_of_size_lt _ (by rw [bytes_size]; exact h))) ∧ d.w3.toNat < 2 ^ 32) :=
  .of_trapFree compiled.sha512_224.trapFree
    (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩) sha512_224_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => ⟨fun h => sha512_224_spec x.1 x.2 h, sha512_224_w3 x.1 x.2⟩

#print axioms sha512_224_master

end Library.Hashing.Sha512
