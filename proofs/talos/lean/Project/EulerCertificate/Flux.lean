import Project.ProofKit.F64Interval
import Project.Euler2DCellStep.SweepModel

namespace Project.EulerCertificate.Flux
open Project.ProofKit.F64Interval
open Project.Euler2DCellStep.Sweep (State)

structure Vector where
  mass : Bounds
  momentum : Bounds
  transverse : Bounds
  energy : Bounds
  deriving DecidableEq, Inhabited, Repr

def pressure (q : State) : Bounds :=
  let squares := add (scale (point q.mx) q.mx) (scale (point q.my) q.my)
  let kinetic := scale (divPositive squares q.density) 0x3FE0000000000000
  divPositive (scale (sub (point q.energy) kinetic) 0x4000000000000000) 0x4014000000000000

def physical (q : State) : Vector :=
  let p := pressure q
  ⟨point q.mx,
    add (divPositive (scale (point q.mx) q.mx) q.density) p,
    divPositive (scale (point q.mx) q.my) q.density,
    divPositive (scale (add (point q.energy) p) q.mx) q.density⟩

def component (alpha left right : UInt64) (leftFlux rightFlux : Bounds) : Bounds :=
  let mean := scale (add leftFlux rightFlux) 0x3FE0000000000000
  let jump := scale (scale (sub (point right) (point left)) alpha) 0x3FE0000000000000
  sub mean jump

def interface (alpha : UInt64) (left right : State) : Vector :=
  let lf := physical left
  let rf := physical right
  ⟨component alpha left.density right.density lf.mass rf.mass,
    component alpha left.mx right.mx lf.momentum rf.momentum,
    component alpha left.my right.my lf.transverse rf.transverse,
    component alpha left.energy right.energy lf.energy rf.energy⟩

end Project.EulerCertificate.Flux
