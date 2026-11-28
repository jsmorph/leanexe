module

public import Library.Numerics.Bignum.Types
public import LeanExe.Pipeline.Implements

@[expose] public section

/-! The flattening of `BigInt` to its sign and magnitude, which the verified compiler reads, as
leanexe's running sum flattens its `Decimal`. -/

namespace Library.Numerics.Bignum

open LeanExe.Pipeline

instance : Flat BigInt (Bool × Array UInt64) := ⟨fun x => (x.neg, x.mag)⟩

end Library.Numerics.Bignum
