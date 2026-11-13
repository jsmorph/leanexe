import Lean
import Verified.Wasi.SysForm

namespace Verified.Wasi.Reflect

open Lean

/-- A typed flat call that `reflect` maps to one `sys` command: the call, its form, whether each
argument of the typed function is an input, in order, and the equation that relates the command to
the typed function.  The equation takes the variables of the arguments in order, then their values,
then the equations between them. -/
structure SysOperation where
  call : Name
  form : Lean.Expr
  inputs : List Bool
  equation : Name

/-- The number of arguments of the typed function. -/
def SysOperation.arity (operation : SysOperation) : Nat := operation.inputs.length

/-- The form `SysForm.flat words bytes` as a term. -/
def flatForm (words : Nat) (bytes : Bool) : Lean.Expr :=
  mkApp2 (mkConst ``Verified.Wasi.SysForm.flat) (mkNatLit words) (toExpr bytes)

end Verified.Wasi.Reflect
