import LeanExe.Wasi.Action
import LeanExe.Wasi.Sys
import Verified.Correct

namespace LeanExe.Wasi

open LeanExe.Pipeline

instance : Flat ReadResult (UInt64 × Bytes) := ⟨fun result => (result.errno, result.bytes)⟩

instance : Flat WriteResult (UInt64 × UInt64) := ⟨fun result => (result.errno, result.count)⟩

@[simp] theorem ReadResult.flat (result : ReadResult) :
    Flat.flat result = (result.errno, result.bytes) := rfl

@[simp] theorem WriteResult.flat (result : WriteResult) :
    Flat.flat result = (result.errno, result.count) := rfl

instance : Flat ClockResult (UInt64 × UInt64) := ⟨fun result => (result.errno, result.time)⟩

instance : Flat RandomResult (UInt64 × Bytes) := ⟨fun result => (result.errno, result.bytes)⟩

instance : Flat ArgsSizes (UInt64 × UInt64 × UInt64) :=
  ⟨fun result => (result.errno, result.count, result.size)⟩

instance : Flat ArgsResult (UInt64 × UInt64 × UInt64 × Bytes) :=
  ⟨fun result => (result.errno, result.count, result.size, result.bytes)⟩

@[simp] theorem ClockResult.flat (result : ClockResult) :
    Flat.flat result = (result.errno, result.time) := rfl

@[simp] theorem RandomResult.flat (result : RandomResult) :
    Flat.flat result = (result.errno, result.bytes) := rfl

@[simp] theorem ArgsSizes.flat (result : ArgsSizes) :
    Flat.flat result = (result.errno, result.count, result.size) := rfl

@[simp] theorem ArgsResult.flat (result : ArgsResult) :
    Flat.flat result = (result.errno, result.count, result.size, result.bytes) := rfl

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
