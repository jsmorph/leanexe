import Library.Numerics.Interval.Enclose

/-!
The closed form of `Model.lean` in interval arithmetic, and the Taylor forms of the squared
distances.  Each `enclosure_def` declares a real function, its interval function, whose name ends
in `I`, and the theorem `encloses` that the interval function's result contains the real
function's result when each interval argument contains the real argument.  `Soundness.lean`
equates each real function with the model.
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

/-- The velocity at time `t` of the closed form from a state with the components `x`, `z`, `vx`,
`vy`, and `vz`.  The along-track position does not enter it. -/
enclosure_def flowVelocity (n t x z vx vy vz) :=
  let p := n * t
  let s := sin p
  let c := cos p
  (3 * n * s * x + c * vx + 2 * s * vy,
    -(6 * n * (1 - c)) * x - 2 * s * vx + (4 * c - 3) * vy,
    -(n * s) * z + c * vz)

/-- The square of the separation of the position `(x, y, z)`. -/
enclosure_def sepSquare (x y z) := |x| * |x| + |y| * |y| + |z| * |z|

/-- The square of the radial and cross-track distance of the components `x` and `z`. -/
enclosure_def rcSquare (x z) := |x| * |x| + |z| * |z|

/-- The second-order Taylor form of the squared separation about a time `t_m`, at the time
`t_m + d`: `(x, y, z)` and `(vx, vy, vz)` are the position and velocity at `t_m`, and
`(px, py, pz)` and `(ux, uy, uz)` those at the point of the Lagrange remainder, where the
acceleration of the equations is `(ax, ay, az)`. -/
enclosure_def sepTaylor (n x y z vx vy vz px py pz ux uy uz d) :=
  let g1 := 2 * (x * vx + y * vy + z * vz)
  let ax := 3 * (n * n) * px + 2 * n * uy
  let ay := -(2 * n * ux)
  let az := -(n * n * pz)
  let g2 := 2 * (sepSquare ux uy uz + (px * ax + py * ay + pz * az))
  sepSquare x y z + g1 * d + g2 * (|d| * |d|) / 2

/-- The second-order Taylor form of the squared radial and cross-track distance, with the
arguments of `sepTaylor` but `y`, `vy`, and `py`.  It keeps `uy`, the along-track velocity at the
point of the remainder, which the radial acceleration `ax` needs. -/
enclosure_def rcTaylor (n x z vx vz px pz ux uy uz d) :=
  let g1 := 2 * (x * vx + z * vz)
  let ax := 3 * (n * n) * px + 2 * n * uy
  let az := -(n * n * pz)
  let g2 := 2 * (rcSquare ux uz + (px * ax + pz * az))
  rcSquare x z + g1 * d + g2 * (|d| * |d|) / 2

end Demos.PassiveSafety
