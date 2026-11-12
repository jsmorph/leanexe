import Library.Hashing.SipHash.Bytes
import Verified.Master

namespace Library.Hashing.SipHash

open Library.Bytes

/-- The export `siphash24`, called on key words `k0` and `k1`, an array `msg`, and a byte count
`n`, returns SipHash-2-4 of Aumasson and Bernstein with the 16 key bytes of `k0` and `k1`, least
significant first, and the first `n` bytes of `msg`. -/
theorem siphash24_master :
    Verified.Master compiled.module compiled.tables "siphash24" compiled.siphash24.bound
      (fun _ => True)
      (fun (x : UInt64 × UInt64 × Array UInt64 × UInt64) (y : UInt64) =>
        y = Spec.sipHash 2 4 ((List.range 16).map (byteAt #[x.1, x.2.1]))
          ((List.range x.2.2.2.toNat).map (byteAt x.2.2.1))) :=
  .of_trapFree (.ofA compiled.siphash24.trapFree) nofun siphash24_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => Proof.siphash24_spec x.1 x.2.1 x.2.2.1 x.2.2.2

#print axioms siphash24_master

/-- The export `siphash13`, called on key words `k0` and `k1`, an array `msg`, and a byte count
`n`, returns SipHash-1-3 of Aumasson and Bernstein with the 16 key bytes of `k0` and `k1`, least
significant first, and the first `n` bytes of `msg`. -/
theorem siphash13_master :
    Verified.Master compiled.module compiled.tables "siphash13" compiled.siphash13.bound
      (fun _ => True)
      (fun (x : UInt64 × UInt64 × Array UInt64 × UInt64) (y : UInt64) =>
        y = Spec.sipHash 1 3 ((List.range 16).map (byteAt #[x.1, x.2.1]))
          ((List.range x.2.2.2.toNat).map (byteAt x.2.2.1))) :=
  .of_trapFree (.ofA compiled.siphash13.trapFree) nofun siphash13_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => Proof.siphash13_spec x.1 x.2.1 x.2.2.1 x.2.2.2

#print axioms siphash13_master

end Library.Hashing.SipHash
