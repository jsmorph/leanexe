module

public import LeanExe.Base

@[expose] public section

/-! The record of an integer: a sign and a magnitude of base-`2^32` limbs, least significant first.
A canonical integer has a canonical magnitude and no negative zero, as `Spec.lean` states. -/

namespace Library.Numerics.Bignum

structure BigInt where
  neg : Bool
  mag : Array UInt64
  deriving Inhabited, Repr, DecidableEq

end Library.Numerics.Bignum
