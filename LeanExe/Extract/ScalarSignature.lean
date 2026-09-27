import LeanExe.Source.ScalarFunction

namespace LeanExe.Extract.Core

/-- UInt64/Bool public parameters and results, with standard Id annotations. -/
def scalarSignature? : Lean.Expr → Option (Nat × LeanExe.Source.Scalar.PublicResult)
  | .const ``UInt64 [] => some (0, .word)
  | .const ``Bool [] => some (0, .boolean)
  | .app (.const ``Id [.zero]) inner =>
      match scalarSignature? inner with
      | some (0, result) => some (0, result)
      | _ => none
  | .forallE _ domain body _ => do
      let _ ← LeanExe.Source.Scalar.PublicArgument.ofType? domain
      let signature ← scalarSignature? body
      pure (signature.1 + 1, signature.2)
  | .mdata _ body => scalarSignature? body
  | _ => none

theorem scalarSignature_accepts {type : Lean.Expr} {arity : Nat}
    {result : LeanExe.Source.Scalar.PublicResult}
    (h : LeanExe.Source.Scalar.Arrow type arity result) :
    scalarSignature? type = some (arity, result) := by
  induction h with
  | result kind => cases kind <;> rfl
  | idResult _ ih => simp [scalarSignature?, ih]
  | arg input _ ih => simp [scalarSignature?, LeanExe.Source.Scalar.PublicArgument.ofType_accepts input, ih]
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
  | case5 name domain body bi ih =>
    simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
    obtain ⟨input, valid, ⟨n, kind⟩, found, same⟩ := parsed
    cases same
    exact .arg (LeanExe.Source.Scalar.PublicArgument.ofType_sound valid) (ih found)
  | case6 data body ih => exact .metadata (ih parsed)
  | case7 => contradiction

theorem scalarSignature_inputs_length {type : Lean.Expr} {arity : Nat}
    {result : LeanExe.Source.Scalar.PublicResult}
    (parsed : scalarSignature? type = some (arity, result)) :
    (LeanExe.Source.Scalar.publicInputs type).length = arity :=
  (scalarSignature_sound parsed).inputs_length

end LeanExe.Extract.Core
