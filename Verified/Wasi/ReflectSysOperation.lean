import Lean
import Verified.Wasi.SysForm

namespace Verified.Wasi.Reflect

open Lean

/-- The kind of an argument of a typed flat call: a word, bytes that the call reads, or a buffer
that the call fills and returns. -/
inductive ArgKind where
  | word
  | input
  | buffer
  deriving BEq

/-- A typed flat call that `reflect` maps to one `sys` command: the call, its form, the kind of
each argument of the typed function, in order, and the equation that relates the command to the
typed function.  The equation takes the variables of the arguments in order, then their values,
then the equations between them. -/
structure SysOperation where
  call : Name
  form : Lean.Expr
  kinds : List ArgKind
  equation : Name

/-- The number of arguments of the typed function. -/
def SysOperation.arity (operation : SysOperation) : Nat := operation.kinds.length

/-- The form `SysForm.flat words bytes` as a term. -/
def flatForm (words : Nat) (bytes : Bool) : Lean.Expr :=
  mkApp2 (mkConst ``Verified.Wasi.SysForm.flat) (mkNatLit words) (toExpr bytes)

/-- The form `SysForm.record fields` as a term. -/
def recordForm (fields : Nat) : Lean.Expr :=
  mkApp (mkConst ``Verified.Wasi.SysForm.record) (mkNatLit fields)

/-- The form `SysForm.iovecRead` as a term. -/
def iovecReadForm : Lean.Expr := mkConst ``Verified.Wasi.SysForm.iovecRead

/-- The form `SysForm.iovecWrite` as a term. -/
def iovecWriteForm : Lean.Expr := mkConst ``Verified.Wasi.SysForm.iovecWrite

/-- The form `SysForm.poll` as a term. -/
def pollForm : Lean.Expr := mkConst ``Verified.Wasi.SysForm.poll

end Verified.Wasi.Reflect
