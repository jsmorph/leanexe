import Library.Hashing.Crc.Bytes
import Verified.Master

namespace Library.Hashing.Crc

open Library.Bytes Library.Hashing.Crc.Proof

/-- The export `crc32`, called on an array `msg` and a byte count `n`, returns CRC-32 of ITU-T V.42
of the first `n` bytes of `msg`. -/
theorem crc32_master :
    Verified.Master compiled.module compiled.tables "crc32" compiled.crc32.bound (fun _ => True)
      (fun (x : Array UInt64 × UInt64) (y : UInt64) =>
        y.toNat = Spec.crc32 ((List.range x.2.toNat).map (byteAt x.1))) :=
  .of_trapFree compiled.crc32.trapFree (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩)
    crc32_export (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ => crc32_spec x.1 x.2

#print axioms crc32_master

/-- The export `crc32c`, called on an array `msg` and a byte count `n`, returns CRC-32C of RFC 3720
of the first `n` bytes of `msg`. -/
theorem crc32c_master :
    Verified.Master compiled.module compiled.tables "crc32c" compiled.crc32c.bound (fun _ => True)
      (fun (x : Array UInt64 × UInt64) (y : UInt64) =>
        y.toNat = Spec.crc32c ((List.range x.2.toNat).map (byteAt x.1))) :=
  .of_trapFree compiled.crc32c.trapFree crc32c_table crc32c_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => crc32c_spec x.1 x.2

#print axioms crc32c_master

/-- The export `crc32Update`, called on a word `crc` that is CRC-32 of some bytes, an array `msg`,
and a byte count `n`, returns, for all bytes `A` whose CRC-32 is `crc`, CRC-32 of `A` followed by
the first `n` bytes of `msg`. -/
theorem crc32Update_master :
    Verified.Master compiled.module compiled.tables "crc32Update" compiled.crc32Update.bound
      (fun x : UInt64 × Array UInt64 × UInt64 => ∃ A, x.1.toNat = Spec.crc32 A)
      (fun x (y : UInt64) => ∀ A, x.1.toNat = Spec.crc32 A →
        y.toNat = Spec.crc32 (A ++ (List.range x.2.2.toNat).map (byteAt x.2.1))) :=
  .of_trapFree compiled.crc32Update.trapFree
    (fun _ ht => ⟨0, by decide, List.mem_singleton.mp ht⟩) crc32Update_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ A hA => crc32Update_spec A x.1 hA x.2.1 x.2.2

#print axioms crc32Update_master

/-- The export `crc32cUpdate`, called on a word `crc` that is CRC-32C of some bytes, an array
`msg`, and a byte count `n`, returns, for all bytes `A` whose CRC-32C is `crc`, CRC-32C of `A`
followed by the first `n` bytes of `msg`. -/
theorem crc32cUpdate_master :
    Verified.Master compiled.module compiled.tables "crc32cUpdate" compiled.crc32cUpdate.bound
      (fun x : UInt64 × Array UInt64 × UInt64 => ∃ A, x.1.toNat = Spec.crc32c A)
      (fun x (y : UInt64) => ∀ A, x.1.toNat = Spec.crc32c A →
        y.toNat = Spec.crc32c (A ++ (List.range x.2.2.toNat).map (byteAt x.2.1))) :=
  .of_trapFree compiled.crc32cUpdate.trapFree crc32c_table crc32cUpdate_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ A hA => crc32cUpdate_spec A x.1 hA x.2.1 x.2.2

#print axioms crc32cUpdate_master

end Library.Hashing.Crc
