import Library.Hashing.Hmac.Program
import Library.Hashing.Hmac.Spec
import TestSupport.Hashing.Packing

/-! A native check of HMAC-SHA-256 and HMAC-SHA-512 in `Library.Hashing.Hmac` on the seven test
cases of RFC 4231 §4, whose case 5 gives the first 16 bytes of each MAC, and of the transcription
`Library.Hashing.Hmac.Spec` on the same cases.  A second check compares the programs with the
transcription for keys of 0 to 140 bytes and a few longer keys, with messages whose inner
lengths cross the padding boundaries of both hash functions.  Keys and messages are packed eight
bytes to a word and followed by a word of nonzero bytes, which the MAC must ignore.  The check
exits with an error at the first difference.  Run with `lake env lean --run` after building
`TestSupport.Hashing.Packing`. -/

namespace TestSupport.Hashing.HmacVectors

open TestSupport.Hashing.Packing

/-- A test case of RFC 4231 §4: its number, key, data, HMAC-SHA-256, and HMAC-SHA-512. -/
structure Case where
  number : Nat
  key : String
  data : String
  sha256 : String
  sha512 : String

def cases : List Case := [
  ⟨1, "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b",
    "4869205468657265",
    "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7",
    "87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cde" ++
      "daa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854"⟩,
  ⟨2, "4a656665",
    "7768617420646f2079612077616e7420666f72206e6f7468696e673f",
    "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843",
    "164b7a7bfcf819e2e395fbe73b56e0a387bd64222e831fd610270cd7ea250554" ++
      "9758bf75c05a994a6d034f65f8f0e6fdcaeab1a34d4a6b4b636e070a38bce737"⟩,
  ⟨3, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
    "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd" ++
      "dddddddddddddddddddddddddddddddddddd",
    "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe",
    "fa73b0089d56a284efb0f0756c890be9b1b5dbdd8ee81a3655f83e33b2279d39" ++
      "bf3e848279a722c806b485a47e67c807b946a337bee8942674278859e13292fb"⟩,
  ⟨4, "0102030405060708090a0b0c0d0e0f10111213141516171819",
    "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd" ++
      "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd",
    "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b",
    "b0ba465637458c6990e5a8c5f61d4af7e576d97ff94b872de76f8050361ee3db" ++
      "a91ca5c11aa25eb4d679275cc5788063a5f19741120c4f2de2adebeb10a298dd"⟩,
  ⟨5, "0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c",
    "546573742057697468205472756e636174696f6e",
    "a3b6167473100ee06e0c796c2955552b",
    "415fad6271580a531d4179bc891d87a6"⟩,
  ⟨6, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" ++
      "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" ++
      "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" ++
      "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" ++
      "aaaaaa",
    "54657374205573696e67204c6172676572205468616e20426c6f636b2d53697a" ++
      "65204b6579202d2048617368204b6579204669727374",
    "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54",
    "80b24263c7c1a3ebb71493c1dd7be8b49b46d1f41b4aeec1121b013783f8f352" ++
      "6b56d037e05f2598bd0fd2215d6a1e5295e64f73f63f0aec8b915a985d786598"⟩,
  ⟨7, "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" ++
      "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" ++
      "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" ++
      "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa" ++
      "aaaaaa",
    "5468697320697320612074657374207573696e672061206c6172676572207468" ++
      "616e20626c6f636b2d73697a65206b657920616e642061206c61726765722074" ++
      "68616e20626c6f636b2d73697a6520646174612e20546865206b6579206e6565" ++
      "647320746f20626520686173686564206265666f7265206265696e6720757365" ++
      "642062792074686520484d414320616c676f726974686d2e",
    "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2",
    "e37b6a775dc87dbaa4dfa9f96e5e3ffddebd71f8867289865df5a32d20cdc944" ++
      "b6022cac3c4982b10d5eeb55c3e4de15134676fb6de0446065c97440fa8c6a58"⟩]

def program256 (key msg : List UInt8) : List UInt8 :=
  let d := Library.Hashing.Hmac.hmacSha256 (pack key) key.length.toUInt64 (pack msg)
    msg.length.toUInt64
  unpack [d.w0, d.w1, d.w2, d.w3] 32

def program512 (key msg : List UInt8) : List UInt8 :=
  let d := Library.Hashing.Hmac.hmacSha512 (pack key) key.length.toUInt64 (pack msg)
    msg.length.toUInt64
  unpack [d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7] 64

def spec256 (key msg : List UInt8) : List UInt8 :=
  bytesOfNat 32 (Library.Hashing.Hmac.Spec.hmacSha256 (toBits key) (toBits msg)).toNat

def spec512 (key msg : List UInt8) : List UInt8 :=
  bytesOfNat 64 (Library.Hashing.Hmac.Spec.hmacSha512 (toBits key) (toBits msg)).toNat

def expect (what : String) (got want : List UInt8) : IO Unit :=
  if got.take want.length != want then
    throw <| IO.userError s!"{what}: {hexOfBytes got} ≠ {hexOfBytes want}"
  else pure ()

/-- The byte `i` of a test key or message with seed `s`. -/
def byte (s i : Nat) : UInt8 := ((i * 89 + s * 41 + i / 5) % 256).toUInt8

def main : IO Unit := do
  for c in cases do
    let key := bytesOfHex c.key
    let data := bytesOfHex c.data
    expect s!"case {c.number}, HMAC-SHA-256 program" (program256 key data) (bytesOfHex c.sha256)
    expect s!"case {c.number}, HMAC-SHA-256 specification" (spec256 key data) (bytesOfHex c.sha256)
    expect s!"case {c.number}, HMAC-SHA-512 program" (program512 key data) (bytesOfHex c.sha512)
    expect s!"case {c.number}, HMAC-SHA-512 specification" (spec512 key data) (bytesOfHex c.sha512)
  IO.println s!"RFC 4231: {cases.length} cases"
  let keyLengths := List.range 141 ++ [200, 255, 256, 1000]
  let msgLengths := [0, 1, 55, 56, 63, 64, 111, 112, 127, 128, 300]
  let mut count := 0
  for kl in keyLengths do
    for ml in msgLengths do
      let key := (List.range kl).map (byte 1)
      let msg := (List.range ml).map (byte 2)
      expect s!"key {kl}, message {ml}, HMAC-SHA-256" (program256 key msg) (spec256 key msg)
      expect s!"key {kl}, message {ml}, HMAC-SHA-512" (program512 key msg) (spec512 key msg)
      count := count + 1
  IO.println s!"specification: {count} pairs of key and message"

end TestSupport.Hashing.HmacVectors

def main : IO Unit := TestSupport.Hashing.HmacVectors.main
