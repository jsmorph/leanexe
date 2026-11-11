import Library.Hashing.XxHash64.Bytes
import Verified.Master

namespace Library.Hashing.XxHash64

open Library.Bytes

/-- The export `xxh64`, called on an array `msg`, a byte count `n`, and a seed, returns XXH64 of
Collet's xxHash specification for the first `n` bytes of `msg` and the seed. -/
theorem xxh64_master :
    Verified.Master compiled.module compiled.tables "xxh64" compiled.xxh64.bound (fun _ => True)
      (fun (x : Array UInt64 × UInt64 × UInt64) (y : UInt64) =>
        y = Spec.xxh64 ((List.range x.2.1.toNat).map (byteAt x.1)) x.2.2) :=
  .of_trapFree (.ofA compiled.xxh64.trapFree) nofun xxh64_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => Proof.xxh64_eq x.1 x.2.1 x.2.2

#print axioms xxh64_master

end Library.Hashing.XxHash64
