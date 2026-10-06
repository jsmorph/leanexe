import LeanExe.Dialect.Loop

/-!
Shapes as a sum: a type whose constructors carry different fields, words and a float.
-/

namespace Examples.Shape

/-- A shape: a circle of float radius, a rectangle of whole-number sides, or a point. -/
inductive Shape
  | circle (r : Float)
  | rect (w h : UInt64)
  | point

/-- The area, with 3 in place of π. -/
def Shape.area : Shape → Float
  | .circle r => 3.0 * r * r
  | .rect w h => (w * h).toFloat
  | .point => 0.0

/-- The shape that the words `k`, `a`, and `b` encode: a circle of radius `a` for `k = 0`, an
`a` by `b` rectangle for `k = 1`, and a point otherwise. -/
def Shape.ofWords (k a b : UInt64) : Shape :=
  if k = 0 then .circle a.toFloat else if k = 1 then .rect a b else .point

/-- The shape with its dimensions multiplied by `f`. -/
def Shape.scale (s : Shape) (f : UInt64) : Shape :=
  match s with
  | .circle r => .circle (r * f.toFloat)
  | .rect w h => .rect (w * f) (h * f)
  | .point => .point

/-- The width of a rectangle, and 0 for the other shapes. -/
def Shape.width : Shape → UInt64
  | .rect w _ => w
  | _ => 0

/-- A rectangle one larger in each side; the other shapes are unchanged. -/
def Shape.grow : Shape → Shape
  | .rect w h => .rect (w + 1) (h + 1)
  | other => other

/-- The shape that the words encode, with a point made into an empty rectangle. -/
def Shape.normalize (k a b : UInt64) : Shape :=
  match Shape.ofWords k a b with
  | .point => .rect 0 0
  | other => other

/-- The total area of the shapes in `words`, three words each, as `Shape.ofWords` reads them. -/
def totalArea (words : Array UInt64) : Float :=
  LeanExe.loop (words.size.toUInt64 / 3) 0.0 fun i total =>
    total + (Shape.ofWords words[(3 * i).toNat]! words[(3 * i + 1).toNat]!
      words[(3 * i + 2).toNat]!).area

end Examples.Shape
