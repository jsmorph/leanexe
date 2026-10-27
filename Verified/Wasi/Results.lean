import LeanExe.Wasi.Action
import Verified.Correct

namespace LeanExe.Wasi

open LeanExe.Pipeline

instance : Flat ReadResult (UInt64 × Bytes) := ⟨fun result => (result.errno, result.bytes)⟩

instance : Flat WriteResult (UInt64 × UInt64) := ⟨fun result => (result.errno, result.count)⟩

@[simp] theorem ReadResult.flat (result : ReadResult) :
    Flat.flat result = (result.errno, result.bytes) := rfl

@[simp] theorem WriteResult.flat (result : WriteResult) :
    Flat.flat result = (result.errno, result.count) := rfl

theorem ReadResult.agree :
    Verified.Agree (inferInstance : Represent ReadResult)
      (Verified.Ty.leanInst (.pair .word .bytes))
      (Flat.flat : ReadResult → UInt64 × Bytes) :=
  Verified.Agree.flat
    (Verified.Agree.refl (inferInstance : Represent (UInt64 × Bytes)))

theorem WriteResult.agree :
    Verified.Agree (inferInstance : Represent WriteResult)
      (Verified.Ty.leanInst (.elem (.prod .word .word)))
      (Flat.flat : WriteResult → UInt64 × UInt64) :=
  Verified.Agree.scalar Flat.flat (fun _ => rfl)

end LeanExe.Wasi
