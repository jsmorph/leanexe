import Project.ProofKit.F64Outward

namespace Project.EulerRiemann.OutwardCfl
open Project.ProofKit.F64Outward (Checked rejected)
open Project.ProofKit.F64Order (positiveBits)

def ratioChecked (dt spacing alpha : UInt64) : Checked :=
  if positiveBits dt && positiveBits spacing && positiveBits alpha then
    let ratio := Project.ProofKit.F64Outward.div true dt spacing
    if ratio.status == 0 then
      let courant := Project.ProofKit.F64Outward.mul true ratio.value alpha
      if courant.status == 0 && decide (courant.value ≤ 0x3FE0000000000000) then ratio
      else rejected
    else rejected
  else rejected

end Project.EulerRiemann.OutwardCfl
