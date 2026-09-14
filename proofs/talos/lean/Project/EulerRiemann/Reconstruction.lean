import Project.ProofKit.F64Minmod
import Project.EulerRiemann.Numerics
import Project.Euler2DCellStep.SweepModel

namespace Project.EulerRiemann.Reconstruction
open Project.Euler2DCellStep.Sweep (State)
open Project.ProofKit.F64Order (finiteBits)

def zeroState : State := ⟨0, 0, 0, 0⟩

def finiteState (state : State) : Bool :=
  finiteBits state.density && finiteBits state.mx &&
    finiteBits state.my && finiteBits state.energy

def admissibleState (state : State) : Bool :=
  Numerics.stateGuard state.density state.mx state.my state.energy

def difference (a b : State) : State :=
  ⟨Wasm.IEEE64.sub a.density b.density, Wasm.IEEE64.sub a.mx b.mx,
   Wasm.IEEE64.sub a.my b.my, Wasm.IEEE64.sub a.energy b.energy⟩

def sum (a b : State) : State :=
  ⟨Wasm.IEEE64.add a.density b.density, Wasm.IEEE64.add a.mx b.mx,
   Wasm.IEEE64.add a.my b.my, Wasm.IEEE64.add a.energy b.energy⟩

def scale (factor : UInt64) (state : State) : State :=
  ⟨Wasm.IEEE64.mul factor state.density, Wasm.IEEE64.mul factor state.mx,
   Wasm.IEEE64.mul factor state.my, Wasm.IEEE64.mul factor state.energy⟩

def minmodState (a b : State) : State :=
  ⟨Project.ProofKit.F64Minmod.minmod a.density b.density,
   Project.ProofKit.F64Minmod.minmod a.mx b.mx,
   Project.ProofKit.F64Minmod.minmod a.my b.my,
   Project.ProofKit.F64Minmod.minmod a.energy b.energy⟩

structure CheckedSlope where
  status : UInt64
  state : State
  deriving DecidableEq, Inhabited

def rejectedSlope : CheckedSlope := ⟨1, zeroState⟩

def slope (left center right : State) : CheckedSlope :=
  let backward := difference center left
  let forward := difference right center
  if finiteState backward && finiteState forward then
    ⟨0, minmodState backward forward⟩
  else rejectedSlope

structure Faces where
  status : UInt64
  left : State
  right : State
  factor : UInt64
  deriving DecidableEq, Inhabited

def rejectedFaces : Faces := ⟨1, zeroState, zeroState, 0⟩

def constantFaces (center : State) : Faces := ⟨0, center, center, 0⟩

def candidate (center delta : State) (factor : UInt64) : Faces :=
  let offset := scale factor delta
  let left := difference center offset
  let right := sum center offset
  if finiteBits factor && finiteState offset && admissibleState left && admissibleState right then
    ⟨0, left, right, factor⟩
  else rejectedFaces

def limit : Nat → State → State → UInt64 → Faces
  | 0, center, _, _ => constantFaces center
  | fuel+1, center, delta, factor =>
      let faces := candidate center delta factor
      if faces.status == 0 then faces
      else limit fuel center delta (Wasm.IEEE64.mul 0x3FE0000000000000 factor)

def reconstruct (fuel : Nat) (left center right : State) : Faces :=
  if admissibleState left && admissibleState center && admissibleState right then
    let delta := slope left center right
    if delta.status == 0 then limit fuel center delta.state 0x3FE0000000000000
    else rejectedFaces
  else rejectedFaces

end Project.EulerRiemann.Reconstruction
