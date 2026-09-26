import LeanExe.Source.ScalarBooleanLet

namespace LeanExe.Source.Scalar

/-- Boolean flags and Boolean-returning functions occupy distinct lexical slots. -/
structure BooleanEnvironment where
  flags : Nat → Bool
  predicates : Nat → UInt64 → Bool

instance : CoeFun BooleanEnvironment (fun _ => Nat → Bool) := ⟨BooleanEnvironment.flags⟩

def BooleanEnvironment.ofFlags (flags : Nat → Bool) : BooleanEnvironment :=
  ⟨flags, fun _ _ => false⟩

instance : Coe (Nat → Bool) BooleanEnvironment := ⟨BooleanEnvironment.ofFlags⟩

/-- An ordinary value binder shifts captured functions without creating one. -/
def BooleanEnvironment.bind (outer : BooleanEnvironment) (flag : Bool) : BooleanEnvironment :=
  ⟨booleanLetBooleans flag outer.flags, fun
    | 0 => fun _ => false
    | index + 1 => outer.predicates index⟩

@[simp] theorem BooleanEnvironment.bind_flag_zero (outer : BooleanEnvironment) (flag : Bool) :
    (outer.bind flag).flags 0 = flag := rfl

@[simp] theorem BooleanEnvironment.bind_flag_succ (outer : BooleanEnvironment) (flag : Bool) (index : Nat) :
    (outer.bind flag).flags (index + 1) = outer.flags index := rfl

@[simp] theorem BooleanEnvironment.bind_predicate_succ (outer : BooleanEnvironment)
    (flag : Bool) (index : Nat) : (outer.bind flag).predicates (index + 1) = outer.predicates index := rfl

end LeanExe.Source.Scalar
