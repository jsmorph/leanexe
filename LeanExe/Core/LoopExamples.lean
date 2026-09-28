import LeanExe.Core.Extract
import LeanExe.Core.Examples

namespace LeanExe.Core.LoopExamples

def sum (count : UInt64) : UInt64 := Id.run do
  let mut accumulator : UInt64 := 0
  for index in [:count.toNat] do
    accumulator := accumulator + UInt64.ofNat index
  return accumulator

def sumBytes (count : UInt64) : StateM ByteArray UInt64 := do
  let mut accumulator : UInt64 := 0
  for index in [:count.toNat] do
    let value ← Memory.read (UInt64.ofNat index)
    accumulator := accumulator + value
  return accumulator

def nested (count : UInt64) : UInt64 := Id.run do
  let mut accumulator : UInt64 := 0
  for outer in [:count.toNat] do
    let bound := UInt64.ofNat outer
    let innerSum := Id.run do
      let mut current : UInt64 := accumulator
      for inner in [:bound.toNat] do
        current := current + UInt64.ofNat inner
      return current
    accumulator := innerSum + 1
  return accumulator

def recursiveCalls (count : UInt64) : UInt64 := Id.run do
  let mut accumulator : UInt64 := 0
  for index in [:count.toNat] do
    accumulator := accumulator + Examples.nonTail (UInt64.ofNat index)
  return accumulator

def recursionAfterLoop (count : UInt64) : UInt64 :=
  if h : count = 0 then 0 else
    let subtotal := Id.run do
      let mut accumulator : UInt64 := 0
      for index in [:count.toNat] do
        accumulator := accumulator + UInt64.ofNat index
      return accumulator
    subtotal + recursionAfterLoop (count / 2)
termination_by count.toNat
decreasing_by
  have positive : 0 < count.toNat := by
    have nonzero : count.toNat ≠ 0 := by
      intro zero
      exact h (UInt64.toNat.inj (by simpa using zero))
    omega
  simpa using Nat.div_lt_self positive (by decide : 1 < 2)

run_elab Extract.certify ``sum `LeanExe.Core.LoopExamples.sumCertificate
run_elab Extract.certifyMemory ``sumBytes `LeanExe.Core.LoopExamples.sumBytesCertificate
run_elab Extract.certify ``nested `LeanExe.Core.LoopExamples.nestedCertificate
run_elab Extract.certify ``recursiveCalls `LeanExe.Core.LoopExamples.recursiveCallsCertificate
run_elab Extract.certify ``recursionAfterLoop `LeanExe.Core.LoopExamples.recursionAfterLoopCertificate

end LeanExe.Core.LoopExamples
