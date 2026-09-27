import Project.EulerCertificate.Flux

namespace Project.EulerCertificate.Vectors
open Project.EulerCertificate.Flux (Vector)
open Project.Euler2DCellStep.Sweep (State)

def zero : Vector := ⟨⟨0, 0, 0⟩, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩⟩

def state (q : State) : Vector :=
  let mass := Project.ProofKit.F64Interval.point q.density
  let momentum := Project.ProofKit.F64Interval.point q.mx
  let transverse := Project.ProofKit.F64Interval.point q.my
  let energy := Project.ProofKit.F64Interval.point q.energy
  ⟨mass, momentum, transverse, energy⟩

def add (a b : Vector) : Vector :=
  let mass := Project.ProofKit.F64Interval.add a.mass b.mass
  let momentum := Project.ProofKit.F64Interval.add a.momentum b.momentum
  let transverse := Project.ProofKit.F64Interval.add a.transverse b.transverse
  let energy := Project.ProofKit.F64Interval.add a.energy b.energy
  ⟨mass, momentum, transverse, energy⟩

def sub (a b : Vector) : Vector :=
  let mass := Project.ProofKit.F64Interval.sub a.mass b.mass
  let momentum := Project.ProofKit.F64Interval.sub a.momentum b.momentum
  let transverse := Project.ProofKit.F64Interval.sub a.transverse b.transverse
  let energy := Project.ProofKit.F64Interval.sub a.energy b.energy
  ⟨mass, momentum, transverse, energy⟩

def scale (a : Vector) (word : UInt64) : Vector :=
  let mass := Project.ProofKit.F64Interval.scale a.mass word
  let momentum := Project.ProofKit.F64Interval.scale a.momentum word
  let transverse := Project.ProofKit.F64Interval.scale a.transverse word
  let energy := Project.ProofKit.F64Interval.scale a.energy word
  ⟨mass, momentum, transverse, energy⟩

def divPositive (a : Vector) (word : UInt64) : Vector :=
  let mass := Project.ProofKit.F64Interval.divPositive a.mass word
  let momentum := Project.ProofKit.F64Interval.divPositive a.momentum word
  let transverse := Project.ProofKit.F64Interval.divPositive a.transverse word
  let energy := Project.ProofKit.F64Interval.divPositive a.energy word
  ⟨mass, momentum, transverse, energy⟩

def orient (axis : Bool) (a : Vector) : Vector :=
  if axis then ⟨a.mass, a.transverse, a.momentum, a.energy⟩ else a

end Project.EulerCertificate.Vectors
