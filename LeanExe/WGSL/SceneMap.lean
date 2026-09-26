import LeanExe.WGSL.UInt

namespace LeanExe.WGSL.UInt

/-- Substitute immutable scene reads, leaving parameters and directions alone. -/
def Expr.mapScene (word : Nat → Expr) : Expr → Expr
  | .lit n => .lit n
  | .read .scene i => word i
  | .read .params i => .read .params i
  | .direction => .direction
  | .add a b => .add (a.mapScene word) (b.mapScene word)
  | .mul a b => .mul (a.mapScene word) (b.mapScene word)
  | .sub a b => .sub (a.mapScene word) (b.mapScene word)
  | .min a b => .min (a.mapScene word) (b.mapScene word)
  | .le a b => .le (a.mapScene word) (b.mapScene word)
  | .eq a b => .eq (a.mapScene word) (b.mapScene word)
  | .both a b => .both (a.mapScene word) (b.mapScene word)
  | .choose c a b => .choose (c.mapScene word) (a.mapScene word) (b.mapScene word)

def Input.mapScene (input : Input) (word : Nat → Expr) : Input :=
  {input with scene := fun i => (word i).eval input}

theorem eval_mapScene (word : Nat → Expr) (e : Expr) (input : Input) :
    (e.mapScene word).eval input = e.eval (input.mapScene word) := by
  induction e with
  | read b i => cases b <;> rfl
  | lit | direction => rfl
  | add a b ha hb | mul a b ha hb | sub a b ha hb | min a b ha hb | le a b ha hb | eq a b ha hb | both a b ha hb =>
    simp only [Expr.mapScene, Expr.eval, ha, hb]
  | choose c a b hc ha hb => simp only [Expr.mapScene, Expr.eval, hc, ha, hb]

end LeanExe.WGSL.UInt
