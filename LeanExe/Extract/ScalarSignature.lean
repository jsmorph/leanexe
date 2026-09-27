import LeanExe.Source.ScalarFunction

namespace LeanExe.Extract.Core

/-- Exact UInt64 or Bool parameters and either a UInt64 or Bool public result. -/
def scalarSignature? : Lean.Expr → Option (Nat × LeanExe.Source.Scalar.PublicResult)
  | .const ``UInt64 [] => some (0, .word)
  | .const ``Bool [] => some (0, .boolean)
  | .app (.const ``Id [.zero]) inner =>
      match scalarSignature? inner with
      | some (0, result) => some (0, result)
      | _ => none
  | .forallE _ (.const ``UInt64 []) body _ =>
      (scalarSignature? body).map fun signature => (signature.1 + 1, signature.2)
  | .forallE _ (.const ``Bool []) body _ =>
      (scalarSignature? body).map fun signature => (signature.1 + 1, signature.2)
  | .mdata _ body => scalarSignature? body
  | _ => none

theorem scalarSignature_accepts {type : Lean.Expr} {arity : Nat}
    {result : LeanExe.Source.Scalar.PublicResult}
    (h : LeanExe.Source.Scalar.Arrow type arity result) :
    scalarSignature? type = some (arity, result) := by
  induction h with
  | result kind => cases kind <;> rfl
  | idResult _ ih => simp [scalarSignature?, ih]
  | arg _ ih => simp [scalarSignature?, ih]
  | booleanArg _ ih => simp [scalarSignature?, ih]
  | metadata _ ih => exact ih

theorem scalarSignature_sound {type : Lean.Expr} {arity : Nat}
    {result : LeanExe.Source.Scalar.PublicResult}
    (parsed : scalarSignature? type = some (arity, result)) :
    LeanExe.Source.Scalar.Arrow type arity result := by
  fun_induction scalarSignature? type generalizing arity result with
  | case1 => cases Option.some.inj parsed; exact .result .word
  | case2 => cases Option.some.inj parsed; exact .result .boolean
  | case3 inner kind found ih =>
    cases Option.some.inj parsed
    exact .idResult (ih found)
  | case4 => contradiction
  | case5 name body bi ih =>
    obtain ⟨⟨n, kind⟩, found, same⟩ := Option.map_eq_some_iff.mp parsed
    cases same
    exact .arg (ih found)
  | case6 name body bi ih =>
    obtain ⟨⟨n, kind⟩, found, same⟩ := Option.map_eq_some_iff.mp parsed
    cases same
    exact .booleanArg (ih found)
  | case7 data body ih => exact .metadata (ih parsed)
  | case8 => contradiction

theorem scalarSignature_inputs_length {type : Lean.Expr} {arity : Nat}
    {result : LeanExe.Source.Scalar.PublicResult}
    (parsed : scalarSignature? type = some (arity, result)) :
    (LeanExe.Source.Scalar.publicInputs type).length = arity :=
  (scalarSignature_sound parsed).inputs_length

end LeanExe.Extract.Core
