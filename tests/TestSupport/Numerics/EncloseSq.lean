module

public import Library.Numerics.Interval.Enclose

@[expose] public section

/-!
Tests of the label `enclose` on `Library.Numerics.Interval.encloses_sq`.  `gI` is a hand-written
interval function of the fields of a structure that squares with `sq`, and the tactic `enclose`
proves that it encloses `gR` with the library's labels alone, without a local attribute.
-/

namespace TestSupport.Numerics.EncloseSq

open Library.Numerics.Interval

/-- A point of two intervals. -/
structure Pt where
  x : Interval
  y : Interval

/-- The sum of the squares of a point's coordinates, and `c` times that sum less the first. -/
def gI (p : Pt) (c : Interval) : Interval × Interval :=
  let s := add (sq p.x) (sq p.y)
  let t := mul c s
  (s, sub t p.x)

/-- The real function of `gI`. -/
noncomputable def gR (x y c : ℝ) : ℝ × ℝ :=
  let s := x * x + y * y
  let t := c * s
  (s, t - x)

theorem gI_encloses {p : Pt} {c : Interval} {x y c' : ℝ}
    (hx : Encloses p.x x) (hy : Encloses p.y y) (hc : Encloses c c') :
    prodRel Encloses Encloses (gI p c) (gR x y c') := by
  enclose

#print axioms gI_encloses

end TestSupport.Numerics.EncloseSq
