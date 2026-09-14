import Project.EulerRiemann.OutwardCfl
import Project.EulerRiemann.Time

namespace Project.EulerRiemann.OutwardCfl
open Project.ProofKit.F64Outward (Checked rejected)

def spacingLower (n : Nat) : Checked :=
  Project.ProofKit.F64Outward.div false 0x3FF0000000000000 (Time.smallNaturalBits n)

def gridRatioChecked (n : Nat) (dt alpha : UInt64) : Checked :=
  if 2 ≤ n ∧ n ≤ 800 then
    let spacing := spacingLower n
    if spacing.status == 0 then ratioChecked dt spacing.value alpha
    else rejected
  else rejected

end Project.EulerRiemann.OutwardCfl
