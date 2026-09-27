import LeanExe.Core.Extract

namespace LeanExe.Core.Examples

def arithmetic (a b : UInt64) : UInt64 :=
  let x := a + b
  if x < a then x ^^^ b else x * 3

def gcd (a b : UInt64) : UInt64 :=
  if h : b = 0 then a else gcd b (a % b)
termination_by b.toNat
decreasing_by
  have positive : 0 < b.toNat := by
    have nonzero : b.toNat ≠ 0 := by
      intro zero
      exact h (UInt64.toNat.inj (by simpa using zero))
    omega
  simpa using Nat.mod_lt a.toNat positive

def nonTail (n : UInt64) : UInt64 :=
  if h : n = 0 then 1 else nonTail (n / 2) + nonTail (n / 2) + n
termination_by n.toNat
decreasing_by
  have positive : 0 < n.toNat := by
    have nonzero : n.toNat ≠ 0 := by
      intro zero
      exact h (UInt64.toNat.inj (by simpa using zero))
    omega
  simpa using Nat.div_lt_self positive (by decide : 1 < 2)

def called (a b : UInt64) : UInt64 :=
  let divisor := gcd a b
  nonTail divisor + arithmetic a b

run_elab Extract.certify ``arithmetic `LeanExe.Core.Examples.arithmeticCertificate
run_elab Extract.certify ``gcd `LeanExe.Core.Examples.gcdCertificate
run_elab Extract.certify ``nonTail `LeanExe.Core.Examples.nonTailCertificate
run_elab Extract.certify ``called `LeanExe.Core.Examples.calledCertificate

end LeanExe.Core.Examples
