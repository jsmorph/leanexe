import Project.ExpArm.Table
import Project.ProofKit.F64Rational

namespace Project.ExpArm
open Project.ProofKit.F64Rational

def tableScaleWord (i : Nat) : UInt64 := table[2*i+1]! + (UInt64.ofNat i <<< 45)

def tableValue (i : Nat) : ℚ := decode (tableScaleWord i) * (1 + decode table[2*i]!)

set_option maxRecDepth 16384 in
theorem table_rational_bounds : ∀ i : Fin 128,
    1 ≤ decode (tableScaleWord i) ∧ decode (tableScaleWord i) < 2 ∧
    |decode table[2*i.val]!| ≤ 1/(2 : ℚ)^53 ∧
    0 < tableValue i - 1/(2 : ℚ)^104 ∧
    (tableValue i - 1/(2 : ℚ)^104)^128 ≤ (2 : ℚ)^i.val ∧
    (2 : ℚ)^i.val ≤ (tableValue i + 1/(2 : ℚ)^104)^128 := by
  decide +kernel

#print axioms table_rational_bounds
end Project.ExpArm
