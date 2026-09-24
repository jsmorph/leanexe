import Project.LebU32.RecyclingMemory

namespace Project.LebU32.Recycling
open Wasm Project.ProofKit

structure Shape (frame : Locals) : Prop where
  params : frame.params.length = 5
  locals : frame.locals.length = 36
  values : frame.values = []
  typed : I64Values frame.locals

structure Running (frame : Locals) (fuel v root : UInt64) (size : Nat) : Prop extends Shape frame where
  fuel : frame.get 0 = some (.i64 fuel)
  input : frame.get 1 = some (.i64 v)
  owner : frame.get 2 = some (.i64 root)
  pointer : frame.get 3 = some (.i64 root)
  size : frame.get 4 = some (.i64 (UInt64.ofNat size))
  tracked : frame.get 5 = some (.i64 root)
  done : frame.get 9 = some (.i64 0)

structure Finished (frame : Locals) (fuel root : UInt64) (size : Nat) : Prop extends Shape frame where
  fuel : frame.get 0 = some (.i64 fuel)
  owner : frame.get 6 = some (.i64 root)
  pointer : frame.get 7 = some (.i64 root)
  size : frame.get 8 = some (.i64 (UInt64.ofNat size))
  done : frame.get 9 = some (.i64 1)

theorem byte_mask (word : UInt64) : word &&& 255 = word.toUInt8.toUInt64 := by
  apply UInt64.toNat.inj
  simp only [UInt64.toNat_and, UInt8.toNat_toUInt64, UInt64.toNat_toUInt8]
  change word.toNat &&& (2^8 - 1) = word.toNat % 2^8
  exact Nat.and_two_pow_sub_one_eq_mod ..

#print axioms byte_mask
end Project.LebU32.Recycling
