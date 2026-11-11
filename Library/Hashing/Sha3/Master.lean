import Library.Hashing.Sha3.Bytes
import Verified.Master

namespace Library.Hashing.Sha3

open Library.Hashing.Words Library.Bytes
open Library.Hashing.Sha3.SpongeProof Library.Hashing.Sha3.Proof Library.Hashing.Sha3.ShakeProof

theorem sha3_224_w3 (msg : Array UInt64) (n : UInt64) : (sha3_224 msg n).w3.toNat < 2 ^ 32 := by
  show ((_ : UInt64) &&& 0xFFFFFFFF).toNat < 2 ^ 32
  rw [UInt64.toNat_and]
  exact Nat.and_lt_two_pow _ (by decide)

/-- The export `sha3_224`, called on an array `msg` and a byte count `n < 2 ^ 61`, returns four
words whose first 28 bytes, read least significant bit first, are the SHA3-224 digest of FIPS 202
of the first `n` bytes of `msg`, read in the same order, and whose fourth word is below `2 ^ 32`,
so that its last four bytes are zero. -/
theorem sha3_224_master :
    Verified.Master compiled.module compiled.tables "sha3_224" compiled.sha3_224.bound
      (fun x : Array UInt64 × UInt64 => x.2.toNat < 2 ^ 61)
      (fun x (d : Words4) =>
        bitsOfBytes (d.bytes 28).toList = Spec.sha3_224 (messageBits x.1 x.2.toNat) ∧
          d.w3.toNat < 2 ^ 32) :=
  .of_trapFree (.ofA compiled.sha3_224.trapFree) nofun sha3_224_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ hn => ⟨sha3_224_spec x.1 x.2 hn, sha3_224_w3 x.1 x.2⟩

#print axioms sha3_224_master

/-- The export `sha3_256`, called on an array `msg` and a byte count `n < 2 ^ 61`, returns four
words whose 32 bytes, read least significant bit first, are the SHA3-256 digest of FIPS 202 of
the first `n` bytes of `msg`, read in the same order. -/
theorem sha3_256_master :
    Verified.Master compiled.module compiled.tables "sha3_256" compiled.sha3_256.bound
      (fun x : Array UInt64 × UInt64 => x.2.toNat < 2 ^ 61)
      (fun x (d : Words4) =>
        bitsOfBytes (d.bytes 32).toList = Spec.sha3_256 (messageBits x.1 x.2.toNat)) :=
  .of_trapFree (.ofA compiled.sha3_256.trapFree) nofun sha3_256_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ hn => sha3_256_spec x.1 x.2 hn

#print axioms sha3_256_master

/-- The export `sha3_384`, called on an array `msg` and a byte count `n < 2 ^ 61`, returns six
words whose 48 bytes, read least significant bit first, are the SHA3-384 digest of FIPS 202 of
the first `n` bytes of `msg`, read in the same order. -/
theorem sha3_384_master :
    Verified.Master compiled.module compiled.tables "sha3_384" compiled.sha3_384.bound
      (fun x : Array UInt64 × UInt64 => x.2.toNat < 2 ^ 61)
      (fun x (d : Words6) =>
        bitsOfBytes d.bytes.toList = Spec.sha3_384 (messageBits x.1 x.2.toNat)) :=
  .of_trapFree (.ofA compiled.sha3_384.trapFree) nofun sha3_384_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ hn => sha3_384_spec x.1 x.2 hn

#print axioms sha3_384_master

/-- The export `sha3_512`, called on an array `msg` and a byte count `n < 2 ^ 61`, returns eight
words whose 64 bytes, read least significant bit first, are the SHA3-512 digest of FIPS 202 of
the first `n` bytes of `msg`, read in the same order. -/
theorem sha3_512_master :
    Verified.Master compiled.module compiled.tables "sha3_512" compiled.sha3_512.bound
      (fun x : Array UInt64 × UInt64 => x.2.toNat < 2 ^ 61)
      (fun x (d : Words8) =>
        bitsOfBytes d.bytes.toList = Spec.sha3_512 (messageBits x.1 x.2.toNat)) :=
  .of_trapFree (.ofA compiled.sha3_512.trapFree) nofun sha3_512_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ hn => sha3_512_spec x.1 x.2 hn

#print axioms sha3_512_master

/-- The export `shake128`, called on an array `msg`, a byte count `n < 2 ^ 61`, and an output
length `d < 2 ^ 61` in bytes, returns an array of `⌈d / 8⌉` words whose first `d` bytes, read
least significant bit first, are the `8 d` bits of SHAKE128 of FIPS 202 of the first `n` bytes of
`msg`, read in the same order, and whose other bytes are zero. -/
theorem shake128_master :
    Verified.Master compiled.module compiled.tables "shake128" compiled.shake128.bound
      (fun x : Array UInt64 × UInt64 × UInt64 => x.2.1.toNat < 2 ^ 61 ∧ x.2.2.toNat < 2 ^ 61)
      (fun x (y : Array UInt64) =>
        bitsOfBytes ((List.range x.2.2.toNat).map (byteAt y)) =
            Spec.shake128 (messageBits x.1 x.2.1.toNat) (8 * x.2.2.toNat) ∧
          y.size = (x.2.2.toNat + 7) / 8 ∧ ∀ i, x.2.2.toNat ≤ i → byteAt y i = 0) :=
  .of_trapFree (.ofA compiled.shake128.trapFree) nofun shake128_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ ⟨hn, hd⟩ => ⟨shake128_spec x.1 x.2.1 x.2.2 hn hd,
      shakeWith_size x.1 x.2.1 x.2.2 21 hd (by decide) (by decide),
      fun _ hi => shakeWith_tail x.1 x.2.1 x.2.2 21 hd (by decide) (by decide) hi⟩

#print axioms shake128_master

/-- The export `shake256`, called on an array `msg`, a byte count `n < 2 ^ 61`, and an output
length `d < 2 ^ 61` in bytes, returns an array of `⌈d / 8⌉` words whose first `d` bytes, read
least significant bit first, are the `8 d` bits of SHAKE256 of FIPS 202 of the first `n` bytes of
`msg`, read in the same order, and whose other bytes are zero. -/
theorem shake256_master :
    Verified.Master compiled.module compiled.tables "shake256" compiled.shake256.bound
      (fun x : Array UInt64 × UInt64 × UInt64 => x.2.1.toNat < 2 ^ 61 ∧ x.2.2.toNat < 2 ^ 61)
      (fun x (y : Array UInt64) =>
        bitsOfBytes ((List.range x.2.2.toNat).map (byteAt y)) =
            Spec.shake256 (messageBits x.1 x.2.1.toNat) (8 * x.2.2.toNat) ∧
          y.size = (x.2.2.toNat + 7) / 8 ∧ ∀ i, x.2.2.toNat ≤ i → byteAt y i = 0) :=
  .of_trapFree (.ofA compiled.shake256.trapFree) nofun shake256_export
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ ⟨hn, hd⟩ => ⟨shake256_spec x.1 x.2.1 x.2.2 hn hd,
      shakeWith_size x.1 x.2.1 x.2.2 17 hd (by decide) (by decide),
      fun _ hi => shakeWith_tail x.1 x.2.1 x.2.2 17 hd (by decide) (by decide) hi⟩

#print axioms shake256_master

end Library.Hashing.Sha3
