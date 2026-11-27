module

public import LeanExe.Native.Clight.Clight
public import Lean.ToExpr

@[expose] public section

/-!
The `Lean.ToExpr` instances of LClight's syntax, in a module of their own so that the tactic
`inst_ok` of `LeanExe.Native.ClightN.Instance` can state a program as a literal at the meta
phase.
-/

namespace ClightN.Proof

deriving instance Lean.ToExpr for LClight.typ
deriving instance Lean.ToExpr for LClight.xtype
deriving instance Lean.ToExpr for LClight.calling_convention
deriving instance Lean.ToExpr for LClight.signature
deriving instance Lean.ToExpr for LClight.memory_chunk
deriving instance Lean.ToExpr for LClight.external_function
deriving instance Lean.ToExpr for LClight.signedness
deriving instance Lean.ToExpr for LClight.intsize
deriving instance Lean.ToExpr for LClight.floatsize
deriving instance Lean.ToExpr for LClight.attr
deriving instance Lean.ToExpr for LClight.type
deriving instance Lean.ToExpr for LClight.unary_operation
deriving instance Lean.ToExpr for LClight.binary_operation
deriving instance Lean.ToExpr for LClight.expr
deriving instance Lean.ToExpr for LClight.statement, LClight.labeled_statements
deriving instance Lean.ToExpr for LClight.function
deriving instance Lean.ToExpr for LClight.fundef
deriving instance Lean.ToExpr for LClight.init_data
deriving instance Lean.ToExpr for LClight.globvar
deriving instance Lean.ToExpr for LClight.globdef

end ClightN.Proof
