import Library.Numerics.Interval.Enclose

/-!
The closed form of `Model.lean` in interval arithmetic.  Each `enclosure_def` declares a real
function, its interval function, whose name ends in `I`, and the theorem `encloses` that the
interval function's result contains the real function's result when each interval argument
contains the real argument.  `Soundness.lean` equates each real function with the model.
-/

open Real

namespace Demos.PassiveSafety

/-- The position at time `t` of the closed form from the state `(x, y, z, vx, vy, vz)`. -/
enclosure_def flowPosition (n t x y z vx vy vz) :=
  let p := n * t
  let s := sin p
  let c := cos p
  ((4 - 3 * c) * x + s / n * vx + 2 / n * (1 - c) * vy,
    6 * (s - p) * x + y - 2 / n * (1 - c) * vx + (4 * s - 3 * p) / n * vy,
    c * z + s / n * vz)

/-- The square of the separation of the position `(x, y, z)`. -/
enclosure_def sepSquare (x y z) := |x| * |x| + |y| * |y| + |z| * |z|

/-- The square of the radial and cross-track distance of the components `x` and `z`. -/
enclosure_def rcSquare (x z) := |x| * |x| + |z| * |z|

end Demos.PassiveSafety
