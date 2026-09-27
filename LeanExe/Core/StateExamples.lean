import LeanExe.Core.Extract
import LeanExe.Core.StateNative

namespace LeanExe.Core.StateExamples

def byteSum (address : UInt64) : StateM ByteArray UInt64 := do
  let first ← Memory.read address
  let second ← Memory.read (address + 1)
  pure (first + second)

def copy (source destination : UInt64) : StateM ByteArray UInt64 := do
  let value ← Memory.read source
  let _ ← Memory.write destination value
  pure value

def allocation (delta : UInt64) : StateM ByteArray UInt64 := do
  let previous ← Memory.grow delta
  let current ← Memory.size
  pure (previous + current)

def recursiveWrite (count address value : UInt64) : StateM ByteArray UInt64 :=
  if h : count = 0 then pure value else do
    let _ ← Memory.write address value
    recursiveWrite (count / 2) (address + 1) (value + 1)
termination_by count.toNat
decreasing_by
  have positive : 0 < count.toNat := by
    have nonzero : count.toNat ≠ 0 := by
      intro zero
      exact h (UInt64.toNat.inj (by simpa using zero))
    omega
  simpa using Nat.div_lt_self positive (by decide : 1 < 2)

run_elab Extract.certifyMemory ``byteSum `LeanExe.Core.StateExamples.byteSumCertificate
run_elab Extract.certifyMemory ``copy `LeanExe.Core.StateExamples.copyCertificate
run_elab Extract.certifyMemory ``allocation `LeanExe.Core.StateExamples.allocationCertificate
run_elab Extract.certifyMemory ``recursiveWrite `LeanExe.Core.StateExamples.recursiveWriteCertificate

end LeanExe.Core.StateExamples
