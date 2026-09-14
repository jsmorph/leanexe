import Project.ProofKit.F64Outward
import Project.EulerRiemann.Numerics

namespace Project.EulerRiemann.OutwardSpeed
open Project.ProofKit.F64Outward (Checked rejected)

def kineticLower (rho mx my : UInt64) : Checked :=
  let xx := Project.ProofKit.F64Outward.mul false mx mx
  let yy := Project.ProofKit.F64Outward.mul false my my
  if xx.status == 0 && yy.status == 0 then
    let sum := Project.ProofKit.F64Outward.add false xx.value yy.value
    if sum.status == 0 then
      let half := Project.ProofKit.F64Outward.mul false 0x3FE0000000000000 sum.value
      if half.status == 0 then Project.ProofKit.F64Outward.div false half.value rho
      else rejected
    else rejected
  else rejected

def internalUpper (rho mx my energy : UInt64) : Checked :=
  let kinetic := kineticLower rho mx my
  if kinetic.status == 0 then Project.ProofKit.F64Outward.sub true energy kinetic.value
  else rejected

def pressureUpper (rho mx my energy : UInt64) : Checked :=
  let internal := internalUpper rho mx my energy
  if internal.status == 0 then
    Project.ProofKit.F64Outward.mul true 0x3FD999999999999A internal.value
  else rejected

def radicandUpper (rho mx my energy : UInt64) : Checked :=
  let pressure := pressureUpper rho mx my energy
  if pressure.status == 0 then
    let ratio := Project.ProofKit.F64Outward.div true pressure.value rho
    if ratio.status == 0 then
      Project.ProofKit.F64Outward.mul true 0x3FF6666666666667 ratio.value
    else rejected
  else rejected

def soundUpper (rho mx my energy : UInt64) : Checked :=
  let radicand := radicandUpper rho mx my energy
  if radicand.status == 0 then Project.ProofKit.F64Outward.sqrt true radicand.value
  else rejected

def speedUpper (rho mx my energy : UInt64) : Checked :=
  if Numerics.stateGuard rho mx my energy then
    let velocity := Project.ProofKit.F64Outward.div true
      (Project.ProofKit.F64Order.absBits mx) rho
    let sound := soundUpper rho mx my energy
    if velocity.status == 0 && sound.status == 0 then
      Project.ProofKit.F64Outward.add true velocity.value sound.value
    else rejected
  else rejected

end Project.EulerRiemann.OutwardSpeed
