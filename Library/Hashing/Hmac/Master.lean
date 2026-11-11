import Library.Hashing.Hmac.Bytes
import Verified.Master

namespace Library.Hashing.Hmac

open Library.Hashing.Words Library.Bytes

/-- The export `hmacSha256`, called on a key array `key` with a byte count `kn < 2 ^ 61` and a
message array `msg` with a byte count `n` such that `n + 64 < 2 ^ 61`, returns four words whose 32
bytes are HMAC-SHA-256 of FIPS 198-1 with the first `kn` bytes of `key` as the key and the first
`n` bytes of `msg` as the text. -/
theorem hmacSha256_master :
    Verified.Master compiled256.module compiled256.tables "hmacSha256" compiled256.hmacSha256.bound
      (fun x : Array UInt64 × UInt64 × Array UInt64 × UInt64 =>
        x.2.1.toNat < 2 ^ 61 ∧ x.2.2.2.toNat + 64 < 2 ^ 61)
      (fun x (d : Words4) =>
        SHS.Equiv.SHA256.Digest.digestBitVec (d.bytes 32) =
          Spec.hmacSha256
            (SHS.Equiv.SHA256.Padding.ByteDecoding.bytesToBitMessage (bytes x.1 x.2.1.toNat))
            (SHS.Equiv.SHA256.Padding.ByteDecoding.bytesToBitMessage
              (bytes x.2.2.1 x.2.2.2.toNat))) :=
  .of_trapFree compiled256.hmacSha256.trapFree
    (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩) hmacSha256_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ ⟨hk, hn⟩ => hmacSha256_spec x.1 x.2.1 x.2.2.1 x.2.2.2 hk hn

#print axioms hmacSha256_master

/-- The export `hmacSha512`, called on a key array `key` with a byte count `kn < 2 ^ 61` and a
message array `msg` with a byte count `n` such that `n + 128 < 2 ^ 61`, returns eight words whose
64 bytes are HMAC-SHA-512 of FIPS 198-1 with the first `kn` bytes of `key` as the key and the
first `n` bytes of `msg` as the text. -/
theorem hmacSha512_master :
    Verified.Master compiled512.module compiled512.tables "hmacSha512" compiled512.hmacSha512.bound
      (fun x : Array UInt64 × UInt64 × Array UInt64 × UInt64 =>
        x.2.1.toNat < 2 ^ 61 ∧ x.2.2.2.toNat + 128 < 2 ^ 61)
      (fun x (d : Words8) =>
        SHS.Equiv.SHA512.Digest.digestBitVec512 d.bytes =
          Spec.hmacSha512
            (SHS.Equiv.SHA512.Padding.ByteDecoding.bytesToBitMessage (bytes x.1 x.2.1.toNat))
            (SHS.Equiv.SHA512.Padding.ByteDecoding.bytesToBitMessage
              (bytes x.2.2.1 x.2.2.2.toNat))) :=
  .of_trapFree compiled512.hmacSha512.trapFree
    (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩) hmacSha512_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ ⟨hk, hn⟩ => hmacSha512_spec x.1 x.2.1 x.2.2.1 x.2.2.2 hk hn

#print axioms hmacSha512_master

end Library.Hashing.Hmac
