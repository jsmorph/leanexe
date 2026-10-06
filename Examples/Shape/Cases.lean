import Examples.Shape.Program
import Examples.Host

/-! The module cases of `shapes`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Shape

open Examples.Host

/-- A shape as the host's four slots: the constructor index, the circle's radius as its bit
pattern, and the rectangle's sides, with zeros in the slots of the other constructors. -/
def shapeWords : Shape → List UInt64
  | .circle r => [0, r.toBits, 0, 0]
  | .rect w h => [1, 0, w, h]
  | .point => [2, 0, 0, 0]

/-- A shape as the host's four arguments. -/
def shapeArgs : Shape → List String
  | .circle r => [u 0, fl r, u 0, u 0]
  | .rect w h => [u 1, fl 0, u w, u h]
  | .point => [u 2, fl 0, u 0, u 0]

def shapeKind : String := "list:i64,f64,i64,i64"

def shapeCases : IO Unit := do
  let dims : List UInt64 := [0, 1, 7, 2 ^ 32, maxU, rw 1, rw 2]
  let radii : List Float := [0.0, -0.0, 1.5, 1e300, inf, nan, 3.0e-310]
  let shapes : List Shape :=
    .point :: radii.map .circle ++ dims.flatMap fun w => [0, 3, maxU].map (Shape.rect w)
  for s in shapes do
    line "shapes" "area" "f64" (shapeArgs s) (toString s.area.toBits)
    line "shapes" "width" "i64" (shapeArgs s) (toString s.width)
    line "shapes" "grow" shapeKind (shapeArgs s) (words (shapeWords s.grow))
    for f in [0, 2, maxU] do
      line "shapes" "scale" shapeKind (shapeArgs s ++ [u f]) (words (shapeWords (s.scale f)))
  for k in [0, 1, 2, 3, maxU] do
    for (a, b) in [(0, 0), (5, 9), (maxU, 2), (2 ^ 53 + 1, 1)] do
      line "shapes" "ofWords" shapeKind [u k, u a, u b] (words (shapeWords (Shape.ofWords k a b)))
      line "shapes" "normalize" shapeKind [u k, u a, u b]
        (words (shapeWords (Shape.normalize k a b)))
  for count in [0, 1, 4, 13] do
    for seed in [0, 1, 2] do
      let ws := (List.range (3 * count + seed % 3)).map fun k =>
        if k % 3 = 0 then UInt64.ofNat ((seed + k) % 4) else rw (seed * 17 + k) % 1000
      line "shapes" "totalArea" "f64" [arrU ws] (toString (totalArea ws.toArray).toBits)

def cases : IO Unit := do
  shapeCases

end Examples.Shape
