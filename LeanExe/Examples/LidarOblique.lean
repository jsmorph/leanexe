import LeanExe.Examples.Lidar

/-! Four rational unit directions `(±3/5, ±4/5)`. Answers use 60 ticks
per distance unit. Integer corners therefore give exact intersection ticks:
one x-coordinate unit costs 100 ticks and one y-coordinate unit costs 75.
The range argument to these functions is already measured in ticks. -/
namespace LeanExe.Examples.LidarOblique
open LeanExe.Examples.Lidar

def entry (b : Rect) (x y : Nat) : Nat :=
  max (100 * (b.x0-x)) (75 * (b.y0-y))

def exit (b : Rect) (x y : Nat) : Nat :=
  min (100 * (b.x1-x)) (75 * (b.y1-y))

def positiveDistance (b : Rect) (x y range : Nat) : Nat :=
  if x ≤ b.x1 ∧ y ≤ b.y1 ∧ entry b x y ≤ exit b x y ∧ entry b x y ≤ range
  then entry b x y else range+1

/-- Direction IDs 0,1,2,3 mean NE,NW,SE,SW. -/
def reflected (b : Rect) (direction : Nat) : Rect :=
  { x0 := if direction = 1 ∨ direction = 3 then world-b.x1 else b.x0
    x1 := if direction = 1 ∨ direction = 3 then world-b.x0 else b.x1
    y0 := if direction = 2 ∨ direction = 3 then world-b.y1 else b.y0
    y1 := if direction = 2 ∨ direction = 3 then world-b.y0 else b.y1 }

def originX (x direction : Nat) : Nat :=
  if direction = 1 ∨ direction = 3 then world-x else x

def originY (y direction : Nat) : Nat :=
  if direction = 2 ∨ direction = 3 then world-y else y

def boxDistance (b : Rect) (x y direction range : Nat) : Nat :=
  positiveDistance (reflected b direction) (originX x direction) (originY y direction) range

def trace (boxes : List Rect) (x y direction range : Nat) : Nat :=
  match boxes with
  | [] => range+1
  | b :: rest => min (boxDistance b x y direction range) (trace rest x y direction range)

end LeanExe.Examples.LidarOblique
