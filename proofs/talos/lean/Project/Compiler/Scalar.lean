import Lean
import Project.IR.Function
import Project.IR.Hint

namespace Project.Compiler

open Lean Meta Project.IR
open Project.ProofKit.ScalarTransition (U64Op)

abbrev IRExpr := Project.ProofKit.ScalarTransition.Expr .u64

/-- The source operators the compiler translates, with the IR operation and the
rule name for each.  The instance arguments are not checked: a wrong match makes
the proof fail. -/
def binaryRules : List (Name × U64Op × String) :=
  [(``HAdd.hAdd, .add, "add"), (``HSub.hSub, .sub, "sub"), (``HMul.hMul, .mul, "mul"),
   (``HDiv.hDiv, .divU, "div"), (``HMod.hMod, .remU, "mod"),
   (``HAnd.hAnd, .bitAnd, "and"), (``HOr.hOr, .bitOr, "or"), (``HXor.hXor, .bitXor, "xor"),
   (``HShiftLeft.hShiftLeft, .shiftLeft, "shiftLeft"),
   (``HShiftRight.hShiftRight, .shiftRight, "shiftRight")]

def isUInt64 (type : Lean.Expr) : MetaM Bool := do
  return (← whnfR type).isConstOf ``UInt64

/-- Translates `term` to an IR expression whose code starts at instruction
`start` and uses scratch locals from `scratch`, with a hint for every node. -/
partial def translate (params : Array Lean.Expr) (scratch start : Nat) (term : Lean.Expr) :
    MetaM (IRExpr × List Hint) := do
  let term := term.consumeMData
  let source := toString (← ppExpr term)
  let hint (ir : IRExpr) (rule : String) : Hint :=
    { func := 0, start, stop := start + (ir.program scratch).length, rule, source }
  if let some index := params.idxOf? term then
    let ir : IRExpr := .get index
    return (ir, [hint ir "parameter"])
  match term.getAppFnArgs with
  | (``OfNat.ofNat, #[type, .lit (.natVal value), _]) =>
      unless ← isUInt64 type do throwError "unsupported literal type: {type}"
      let ir : IRExpr := .const (UInt64.ofNat value)
      return (ir, [hint ir "literal"])
  | (fn, #[left, right, out, _, a, b]) =>
      let some (_, op, rule) := binaryRules.find? (·.1 == fn)
        | throwError "unsupported operation: {fn}"
      unless (← isUInt64 left) && (← isUInt64 right) && (← isUInt64 out) do
        throwError "unsupported operand types in {source}"
      if op = .divU ∨ op = .remU then
        let childScratch := scratch + 2
        let (l, lHints) ← translate params childScratch start a
        let (r, rHints) ← translate params childScratch
          (start + (l.program childScratch).length + 1) b
        let ir : IRExpr := .bin op l r
        return (ir, hint ir rule :: lHints ++ rHints)
      else
        let (l, lHints) ← translate params scratch start a
        let (r, rHints) ← translate params scratch (start + (l.program scratch).length) b
        let ir : IRExpr := .bin op l r
        return (ir, hint ir rule :: lHints ++ rHints)
  | _ => throwError "unsupported term: {source}"

/-- Compiles the definition `declName`, whose parameters and result are all
`UInt64`, to an IR function with hints. -/
def compileScalar (declName : Name) : MetaM (Func × Hints) := do
  let env ← getEnv
  let .defnInfo info ← getConstInfo declName
    | throwError "{declName} is not a definition"
  if (Compiler.implementedByAttr.getParam? env declName).isSome || isExtern env declName then
    throwError "{declName} has an implementation other than its definition"
  lambdaTelescope info.value fun params body => do
    for param in params do
      unless ← isUInt64 (← inferType param) do
        throwError "parameter {param} of {declName} is not UInt64"
    unless ← isUInt64 (← inferType body) do
      throwError "the result of {declName} is not UInt64"
    let (result, nodes) ← translate params params.size 0 body
    let names ← params.toList.mapM fun param => return (← param.fvarId!.getUserName).toString
    return ({ params := params.size, result }, { params := names.zipIdx, nodes })

deriving instance ToExpr for U64Op

/-- The Lean term for an IR expression, for the definitions the command adds. -/
def irToExpr : IRExpr → MetaM Lean.Expr
  | .get index => return mkApp (mkConst ``Project.ProofKit.ScalarTransition.Expr.get) (toExpr index)
  | .const value =>
      return mkApp (mkConst ``Project.ProofKit.ScalarTransition.Expr.const) (toExpr value)
  | .bin op left right =>
      return mkApp3 (mkConst ``Project.ProofKit.ScalarTransition.Expr.bin) (toExpr op)
        (← irToExpr left) (← irToExpr right)
  | _ => throwError "the scalar compiler does not emit this IR node"

end Project.Compiler
