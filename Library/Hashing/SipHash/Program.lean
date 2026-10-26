import LeanExe.Dialect.Loop
import Library.Hashing.SipHash.Spec

/-! SipHash-2-4 and SipHash-1-3 of `Library.Hashing.SipHash.Spec` for a 16-byte key given as its
two little-endian words and a message of `n` bytes packed eight to a word as
`Library.Hashing.Words` describes.  The packing makes word `i` of the array the message word
`m_i` of the specification for `i < n / 8`, and `lastWord` forms the final word from the
remaining bytes and `n mod 256` in the top byte.  The state is the specification's structure of
four words, and no function allocates. -/

namespace Library.Hashing.SipHash

open Library.Hashing.SipHash.Spec (State)

/-- `x` rotated left by `k` bits, for `k` from 1 to 63. -/
@[inline] def rotl (x k : UInt64) : UInt64 := (x <<< k) ||| (x >>> (64 - k))

/-- SipRound. -/
def sipRound (v : State) : State :=
  let v0 := v.v0 + v.v1
  let v2 := v.v2 + v.v3
  let v1 := rotl v.v1 13 ^^^ v0
  let v3 := rotl v.v3 16 ^^^ v2
  let v0 := rotl v0 32
  let v2 := v2 + v1
  let v0 := v0 + v3
  let v1 := rotl v1 17 ^^^ v2
  let v3 := rotl v3 21 ^^^ v0
  ⟨v0, v1, rotl v2 32, v3⟩

/-- `k` iterations of SipRound. -/
def rounds (k : UInt64) (v : State) : State := LeanExe.loop k v fun _ v => sipRound v

/-- The processing of the message word `m` with `c` rounds. -/
def compress (c : UInt64) (v : State) (m : UInt64) : State :=
  let v := rounds c { v with v3 := v.v3 ^^^ m }
  { v with v0 := v.v0 ^^^ m }

/-- The last message word: the `n % 8` bytes after the full words, null bytes, and `n mod 256`
in the top byte. -/
def lastWord (msg : Array UInt64) (n : UInt64) : UInt64 :=
  let mask : UInt64 := ((1 : UInt64) <<< ((n &&& 7) <<< 3)) - 1
  (msg[(n >>> 3).toNat]! &&& mask) ||| (n <<< 56)

/-- SipHash-c-d of the key words `k0` and `k1` and the `n` bytes of `msg`. -/
def sipHashWith (c d k0 k1 : UInt64) (msg : Array UInt64) (n : UInt64) : UInt64 :=
  let v : State := ⟨k0 ^^^ 0x736f6d6570736575, k1 ^^^ 0x646f72616e646f6d,
    k0 ^^^ 0x6c7967656e657261, k1 ^^^ 0x7465646279746573⟩
  let v := LeanExe.loop (n >>> 3) v fun i v => compress c v msg[i.toNat]!
  let v := compress c v (lastWord msg n)
  let v := rounds d { v with v2 := v.v2 ^^^ 0xff }
  v.v0 ^^^ v.v1 ^^^ v.v2 ^^^ v.v3

/-- SipHash-2-4 of the key words `k0` and `k1` and the `n` bytes of `msg`. -/
def siphash24 (k0 k1 : UInt64) (msg : Array UInt64) (n : UInt64) : UInt64 :=
  sipHashWith 2 4 k0 k1 msg n

/-- SipHash-1-3 of the key words `k0` and `k1` and the `n` bytes of `msg`. -/
def siphash13 (k0 k1 : UInt64) (msg : Array UInt64) (n : UInt64) : UInt64 :=
  sipHashWith 1 3 k0 k1 msg n

end Library.Hashing.SipHash
