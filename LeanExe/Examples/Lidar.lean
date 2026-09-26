/-! Deterministic cardinal lidar. Distances and coordinates are integer grid units.
Closed rectangles, inclusive range, and distance zero for an occupied origin.
The miss sentinel is `range + 1`; no floating-point arithmetic is used. -/
namespace LeanExe.Examples.Lidar

structure Rect where
  x0 : Nat
  y0 : Nat
  x1 : Nat
  y1 : Nat
  deriving Repr, DecidableEq

def world : Nat := 4095

def Rect.Valid (b : Rect) : Prop :=
  b.x0 ≤ b.x1 ∧ b.x1 ≤ world ∧ b.y0 ≤ b.y1 ∧ b.y1 ≤ world

instance (b : Rect) : Decidable b.Valid := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Positive-axis ray, with the transverse coordinate held fixed. -/
def axisDistance (lo hi low high origin transverse range : Nat) : Nat :=
  if low ≤ transverse ∧ transverse ≤ high ∧ origin ≤ hi then
    if lo - origin ≤ range then lo - origin else range + 1
  else range + 1

/-- Directions 0,1,2,3 are east, west, north, south. Reflection of the
bounded coordinate box reduces all four to a positive-axis calculation. -/
def boxDistance (box : Rect) (x y direction range : Nat) : Nat :=
  if direction = 0 then axisDistance box.x0 box.x1 box.y0 box.y1 x y range
  else if direction = 1 then
    axisDistance (world-box.x1) (world-box.x0) box.y0 box.y1 (world-x) y range
  else if direction = 2 then axisDistance box.y0 box.y1 box.x0 box.x1 y x range
  else axisDistance (world-box.y1) (world-box.y0) box.x0 box.x1 (world-y) x range

def trace (boxes : List Rect) (x y direction range : Nat) : Nat :=
  match boxes with
  | [] => range+1
  | box :: rest => min (boxDistance box x y direction range) (trace rest x y direction range)

/-- A scalar controller accepted by the general arithmetic compiler.
Four bounded fields fit in one 40-bit word: x, y, range, requested beam mask.
The host unpacks this into four u32 words. All-ones marks rejected inputs. -/
def parameters (x y range mask : UInt64) : UInt64 :=
  if x ≤ 4095 ∧ y ≤ 4095 ∧ range ≤ 4095 ∧ mask ≤ 15 then
    x + y * 4096 + range * 16777216 + mask * 68719476736
  else 18446744073709551615

end LeanExe.Examples.Lidar
