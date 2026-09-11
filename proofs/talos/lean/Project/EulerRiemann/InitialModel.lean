import Project.Euler2DCellStep.Sweep

namespace Project.EulerRiemann.Initial
open Project.Euler2DCellStep.Sweep
open Wasm.IEEE64 (add sub mul div)

def conservative (pressure density u v : UInt64) : State :=
  ⟨density, mul density u, mul density v,
    add (div pressure 0x3FD999999999999A)
      (mul (mul 0x3FE0000000000000 density) (add (mul u u) (mul v v)))⟩

def bottomLeft : State :=
  conservative 0x3F9DB22D0E560419 0x3FC1A9FBE76C8B44
    0x3FF34BC6A7EF9DB2 0x3FF34BC6A7EF9DB2

def bottomRight : State :=
  conservative 0x3FD3333333333333 0x3FE1089A02752546 0 0x3FF34BC6A7EF9DB2

def topLeft : State :=
  conservative 0x3FD3333333333333 0x3FE1089A02752546 0x3FF34BC6A7EF9DB2 0

def topRight : State :=
  conservative 0x3FF8000000000000 0x3FF8000000000000 0 0

def fifths (n : Nat) : UInt64 :=
  if n = 0 then 0
  else if n = 1 then 0x3FC999999999999A
  else if n = 2 then 0x3FD999999999999A
  else if n = 3 then 0x3FE3333333333333
  else if n = 4 then 0x3FE999999999999A
  else 0x3FF0000000000000

def weightedWord (x y bl br tl tr : UInt64) : UInt64 :=
  let right := sub 0x3FF0000000000000 x
  let top := sub 0x3FF0000000000000 y
  add (add (add (mul (mul x y) bl) (mul (mul right y) br))
    (mul (mul x top) tl)) (mul (mul right top) tr)

def weighted (x y : Nat) : State :=
  let fx := fifths x
  let fy := fifths y
  ⟨weightedWord fx fy bottomLeft.density bottomRight.density topLeft.density topRight.density,
    weightedWord fx fy bottomLeft.mx bottomRight.mx topLeft.mx topRight.mx,
    weightedWord fx fy bottomLeft.my bottomRight.my topLeft.my topRight.my,
    weightedWord fx fy bottomLeft.energy bottomRight.energy topLeft.energy topRight.energy⟩

end Project.EulerRiemann.Initial
