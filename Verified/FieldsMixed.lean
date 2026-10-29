import Verified.FieldsBytes

namespace Verified

variable {pool : Bytes.LiteralPool}

open Wasm LeanExe.Pipeline LeanExe.Runtime

/-- The code after the store of an argument of type `t` in the locals from `loc` on: the
normalization of a buffer, and nothing for a value of another type. -/
def Ty.normalizeCode : Ty → Nat → Program
  | .bytes, loc => Bytes.normalizeCode loc (loc + 1)
  | _, _ => []

/-- The first local of argument `i` among arguments of the types `ps`, relative to the first
argument's. -/
def fieldOffset (ps : List Ty) (i : Nat) : Nat := ((ps.take i).map Ty.width).sum

theorem fieldOffset_zero (ps : List Ty) : fieldOffset ps 0 = 0 := by
  simp [fieldOffset]

theorem fieldOffset_succ (p : Ty) (ps : List Ty) (i : Nat) :
    fieldOffset (p :: ps) (i + 1) = p.width + fieldOffset ps i := by
  simp [fieldOffset]

/-- The words of a value of type `t` whose buffer, if it is one, has root 0 when it is empty. -/
def Ty.Normal : Ty → List Value → Prop
  | .bytes, ws => Bytes.Normal ws
  | _, _ => True

/-- The words of values of the types `ps`, each as `Ty.Normal` states. -/
def FieldsNormal : List Ty → List Value → Prop
  | [], _ => True
  | p :: ps, ws => p.Normal (ws.take p.width) ∧ FieldsNormal ps (ws.drop p.width)

end Verified
