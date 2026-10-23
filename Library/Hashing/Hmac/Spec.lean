import Library.Hashing.Sha2.Spec

/-! HMAC of FIPS 198-1, *The Keyed-Hash Message Authentication Code*, July 2008, transcribed from
§2.3 and from Table 1 of §4.  Messages are the bit strings of `Library.Hashing.Sha2.Spec`, most
significant bit first, and the hash functions are its SHA-256 and SHA-512.  A key is a string of
whole bytes, and `B` and `L` count bytes in the standard.  Here `B` counts bytes and the digest
width `L` counts bits, so the zeros of step 2 number `8 B - L` bits. -/

namespace Library.Hashing.Hmac.Spec

open SHS

/-- The eight bits of the byte `b`, most significant first. -/
def byteBits (b : UInt8) : Message := (List.range 8).reverse.map b.toNat.testBit

/-- The bits of `d`, most significant first. -/
def bitsOf {n : Nat} (d : BitVec n) : Message := (List.range n).reverse.map d.getLsbD

/-- `ipad` of §2.3: the byte `x'36'` repeated `B` times. -/
def ipad (B : Nat) : Message := (List.replicate B (byteBits 0x36)).flatten

/-- `opad` of §2.3: the byte `x'5c'` repeated `B` times. -/
def opad (B : Nat) : Message := (List.replicate B (byteBits 0x5c)).flatten

/-- `⊕` of §2.3 on two bit strings of one length. -/
def xorBits (x y : Message) : Message := List.zipWith (· ^^ ·) x y

/-- `K_0` of Table 1, steps 1 to 3, for the hash function `H` on blocks of `B` bytes. -/
def keyBlock {L : Nat} (B : Nat) (H : Message → BitVec L) (K : Message) : Message :=
  if K.length = 8 * B then K
  else if 8 * B < K.length then bitsOf (H K) ++ List.replicate (8 * B - L) false
  else K ++ List.replicate (8 * B - K.length) false

/-- `HMAC(K, text) = H((K_0 ⊕ opad) || H((K_0 ⊕ ipad) || text))` of §4, Table 1 steps 4 to 9. -/
def hmac {L : Nat} (B : Nat) (H : Message → BitVec L) (K text : Message) : BitVec L :=
  let K0 := keyBlock B H K
  H (xorBits K0 (opad B) ++ bitsOf (H (xorBits K0 (ipad B) ++ text)))

/-- SHA-256 of FIPS 180-4 §6.2, with the value zero outside its domain of messages of fewer than
`2 ^ 64` bits. -/
def sha256 (M : Message) : BitVec 256 :=
  if h : M.length < 2 ^ 64 then SHA256.sha256 M h else 0

/-- SHA-512 of FIPS 180-4 §6.4, with the value zero outside its domain of messages of fewer than
`2 ^ 128` bits. -/
def sha512 (M : Message) : BitVec 512 :=
  if h : M.length < 2 ^ 128 then SHA512.sha512 M h else 0

/-- HMAC-SHA-256: HMAC with SHA-256, whose blocks have `B = 64` bytes. -/
def hmacSha256 (K text : Message) : BitVec 256 := hmac 64 sha256 K text

/-- HMAC-SHA-512: HMAC with SHA-512, whose blocks have `B = 128` bytes. -/
def hmacSha512 (K text : Message) : BitVec 512 := hmac 128 sha512 K text

end Library.Hashing.Hmac.Spec
