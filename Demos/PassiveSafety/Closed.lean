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

/-- The state at time `t` of the closed form from the state `(x, y, z, vx, vy, vz)`. -/
enclosure_def flowState (n t x y z vx vy vz) :=
  let p := n * t
  let s := sin p
  let c := cos p
  ((4 - 3 * c) * x + s / n * vx + 2 / n * (1 - c) * vy,
    6 * (s - p) * x + y - 2 / n * (1 - c) * vx + (4 * s - 3 * p) / n * vy,
    c * z + s / n * vz,
    3 * n * s * x + c * vx + 2 * s * vy,
    -(6 * n * (1 - c)) * x - 2 * s * vx + (4 * c - 3) * vy,
    -(n * s) * z + c * vz)

/-- The square of the separation of the position `(x, y, z)`. -/
enclosure_def sepSquare (x y z) := |x| * |x| + |y| * |y| + |z| * |z|

/-- The square of the radial and cross-track distance at phase `p` of the closed form from a
state with the components `x`, `z`, `vx`, `vy`, and `vz`. -/
enclosure_def rcSquare (n p x z vx vy vz) :=
  let s := sin p
  let c := cos p
  let r := (4 - 3 * c) * x + s / n * vx + 2 / n * (1 - c) * vy
  let q := c * z + s / n * vz
  |r| * |r| + |q| * |q|

end Demos.PassiveSafety
