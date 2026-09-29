import Lean
import Project.IR.Function
import Project.IR.Hint

namespace Project.Compiler

open Lean Meta Project.IR
open Project.ProofKit.ScalarTransition (U64Op ScalarType)

abbrev IRExpr := Project.ProofKit.ScalarTransition.Expr

/-- The source operators on `UInt64` the compiler translates, with the IR
operation and the rule name for each.  Instance arguments are not checked: a
wrong match makes the proof fail. -/
def binaryRules : List (Name × U64Op × String) :=
  [(``HAdd.hAdd, .add, "add"), (``HSub.hSub, .sub, "sub"), (``HMul.hMul, .mul, "mul"),
   (``HDiv.hDiv, .divU, "div"), (``HMod.hMod, .remU, "mod"),
   (``HAnd.hAnd, .bitAnd, "and"), (``HOr.hOr, .bitOr, "or"), (``HXor.hXor, .bitXor, "xor"),
   (``HShiftLeft.hShiftLeft, .shiftLeft, "shiftLeft"),
   (``HShiftRight.hShiftRight, .shiftRight, "shiftRight")]

def isUInt64 (type : Lean.Expr) : MetaM Bool := do
  return (← whnfR type).isConstOf ``UInt64

/-- The compiler's view of the function being compiled.  Locals are laid out as
the parameters, then `result`, `done`, one temporary per parameter, and scratch. -/
structure Ctx where
  self : Name
  params : Array Lean.Expr
  scratch : Nat

def Ctx.result (ctx : Ctx) : Nat := ctx.params.size
def Ctx.done (ctx : Ctx) : Nat := ctx.params.size + 1
def Ctx.temp (ctx : Ctx) (i : Nat) : Nat := ctx.params.size + 2 + i
def Ctx.vars (ctx : Ctx) : Nat := ctx.params.size + 2

/-- Where a node's code starts: the path to the enclosing instruction list and
the index in that list. -/
structure Loc where
  prefix_ : List Nat
  index : Nat

def Loc.path (loc : Loc) : List Nat := loc.prefix_ ++ [loc.index]
def Loc.skip (loc : Loc) (n : Nat) : Loc := { loc with index := loc.index + n }
/-- The start of branch `branch` (0 or 1) of the `if` at `loc`, or of the body
of the `block` or `loop` at `loc` when `branch` is `none`. -/
def Loc.inside (loc : Loc) (branch : Option Nat) : Loc :=
  { prefix_ := loc.path ++ branch.toList, index := 0 }

def mkHint (loc : Loc) (length : Nat) (rule source : String) : Hint :=
  { func := 0, path := loc.path, length, rule, source }

def sourceOf (term : Lean.Expr) : MetaM String := return toString (← ppExpr term)

mutual
  /-- Translates a `UInt64` term to an IR expression whose code starts at `loc`
  and uses scratch locals from `scratch`. -/
  partial def translateValue (ctx : Ctx) (scratch : Nat) (loc : Loc) (term : Lean.Expr) :
      MetaM (IRExpr .u64 × List Hint) := do
    let term := term.consumeMData
    let source ← sourceOf term
    let hint (ir : IRExpr .u64) (rule : String) : Hint :=
      mkHint loc (ir.program scratch).length rule source
    if let some index := ctx.params.idxOf? term then
      let ir : IRExpr .u64 := .get index
      return (ir, [hint ir "parameter"])
    match term.getAppFnArgs with
    | (``OfNat.ofNat, #[type, .lit (.natVal value), _]) =>
        unless ← isUInt64 type do throwError "unsupported literal type: {type}"
        let ir : IRExpr .u64 := .const (UInt64.ofNat value)
        return (ir, [hint ir "literal"])
    | (``ite, #[type, condition, _, thenTerm, elseTerm]) =>
        unless ← isUInt64 type do throwError "unsupported conditional type in {source}"
        let (c, cHints) ← translateCondition ctx scratch loc condition
        let branch := loc.skip (c.program scratch).length
        let (a, aHints) ← translateValue ctx scratch (branch.inside (some 0)) thenTerm
        let (b, bHints) ← translateValue ctx scratch (branch.inside (some 1)) elseTerm
        let ir : IRExpr .u64 := .ite c a b
        return (ir, hint ir "conditional value" :: cHints ++ aHints ++ bHints)
    | (fn, #[left, right, out, _, a, b]) =>
        let some (_, op, rule) := binaryRules.find? (·.1 == fn)
          | throwError "unsupported operation {fn} in {source}"
        unless (← isUInt64 left) && (← isUInt64 right) && (← isUInt64 out) do
          throwError "unsupported operand types in {source}"
        if op = .divU ∨ op = .remU then
          let childScratch := scratch + 2
          let (l, lHints) ← translateValue ctx childScratch loc a
          let (r, rHints) ← translateValue ctx childScratch
            (loc.skip ((l.program childScratch).length + 1)) b
          let ir : IRExpr .u64 := .bin op l r
          return (ir, hint ir rule :: lHints ++ rHints)
        else
          let (l, lHints) ← translateValue ctx scratch loc a
          let (r, rHints) ← translateValue ctx scratch (loc.skip (l.program scratch).length) b
          let ir : IRExpr .u64 := .bin op l r
          return (ir, hint ir rule :: lHints ++ rHints)
    | _ => throwError "unsupported term: {source}"

  /-- Translates a decidable proposition about `UInt64` values to an IR
  condition. -/
  partial def translateCondition (ctx : Ctx) (scratch : Nat) (loc : Loc)
      (prop : Lean.Expr) : MetaM (IRExpr .bool × List Hint) := do
    let prop := prop.consumeMData
    let source ← sourceOf prop
    let hint (ir : IRExpr .bool) (rule : String) : Hint :=
      mkHint loc (ir.program scratch).length rule source
    let pair (make : IRExpr .u64 → IRExpr .u64 → IRExpr .bool) (rule : String)
        (a b : Lean.Expr) : MetaM (IRExpr .bool × List Hint) := do
      let (l, lHints) ← translateValue ctx scratch loc a
      let (r, rHints) ← translateValue ctx scratch (loc.skip (l.program scratch).length) b
      let ir := make l r
      return (ir, hint ir rule :: lHints ++ rHints)
    let connective (make : IRExpr .bool → IRExpr .bool → IRExpr .bool) (rule : String)
        (a b : Lean.Expr) : MetaM (IRExpr .bool × List Hint) := do
      let (l, lHints) ← translateCondition ctx scratch loc a
      let inner := (loc.skip (l.program scratch).length).inside
        (some (if rule == "and" then 0 else 1))
      let (r, rHints) ← translateCondition ctx scratch inner b
      let ir := make l r
      return (ir, hint ir rule :: lHints ++ rHints)
    match prop.getAppFnArgs with
    | (``Eq, #[type, a, b]) =>
        unless ← isUInt64 type do throwError "unsupported equality type in {source}"
        pair .eq "equal" a b
    | (``Ne, #[type, a, b]) =>
        unless ← isUInt64 type do throwError "unsupported inequality type in {source}"
        pair .ne "not equal" a b
    | (``LT.lt, #[type, _, a, b]) =>
        unless ← isUInt64 type do throwError "unsupported comparison type in {source}"
        pair .ltU "less than" a b
    | (``LE.le, #[type, _, a, b]) =>
        unless ← isUInt64 type do throwError "unsupported comparison type in {source}"
        pair .leU "at most" a b
    | (``GT.gt, #[type, _, a, b]) =>
        unless ← isUInt64 type do throwError "unsupported comparison type in {source}"
        pair .ltU "greater than" b a
    | (``GE.ge, #[type, _, a, b]) =>
        unless ← isUInt64 type do throwError "unsupported comparison type in {source}"
        pair .leU "at least" b a
    | (``Not, #[p]) =>
        let (c, cHints) ← translateCondition ctx scratch loc p
        let ir : IRExpr .bool := .not c
        return (ir, hint ir "not" :: cHints)
    | (``And, #[a, b]) => connective .and "and" a b
    | (``Or, #[a, b]) => connective .or "or" a b
    | _ => throwError "unsupported condition: {source}"
end

/-- `stmts` in sequence, with the code of each placed after the previous. -/
def seqAll : List Project.IR.Stmt → Project.IR.Stmt
  | [] => .skip
  | [s] => s
  | s :: rest => .seq s (seqAll rest)

/-- Translates the body of a tail-recursive definition, in tail position, to a
statement that either updates the parameters for the next iteration or stores
the result and sets `done`. -/
partial def translateTail (ctx : Ctx) (loc : Loc) (term : Lean.Expr) :
    MetaM (Project.IR.Stmt × List Hint) := do
  let term := term.consumeMData
  let source ← sourceOf term
  match term.getAppFnArgs with
  | (``ite, #[_, condition, _, thenTerm, elseTerm]) =>
      let (c, cHints) ← translateCondition ctx ctx.scratch loc condition
      let branch := loc.skip (c.program ctx.scratch).length
      let (a, aHints) ← translateTail ctx (branch.inside (some 0)) thenTerm
      let (b, bHints) ← translateTail ctx (branch.inside (some 1)) elseTerm
      let stmt : Project.IR.Stmt := .ite c a b
      return (stmt, mkHint loc (stmt.program ctx.scratch).length "branch" source ::
        cHints ++ aHints ++ bHints)
  | (fn, args) =>
      if fn == ctx.self then
        unless args.size == ctx.params.size do
          throwError "a recursive call must pass every parameter: {source}"
        -- Evaluate every argument into a temporary, then copy the temporaries into the
        -- parameters, so each argument sees the parameters of the current call.
        let mut stmts : List Project.IR.Stmt := []
        let mut hints : List Hint := []
        let mut here := loc
        for i in [:args.size] do
          let (value, valueHints) ← translateValue ctx ctx.scratch here args[i]!
          let stmt : Project.IR.Stmt := .assign (ctx.temp i) value
          stmts := stmts ++ [stmt]
          hints := hints ++ valueHints
          here := here.skip (stmt.program ctx.scratch).length
        for i in [:args.size] do
          stmts := stmts ++ [.assign i (.get (ctx.temp i))]
        let stmt := seqAll stmts
        return (stmt, mkHint loc (stmt.program ctx.scratch).length "tail call" source :: hints)
      else
        let (value, valueHints) ← translateValue ctx ctx.scratch loc term
        let stmt : Project.IR.Stmt :=
          .seq (.assign ctx.result value) (.assign ctx.done (.const 1))
        return (stmt, mkHint loc (stmt.program ctx.scratch).length "base case" source ::
          valueHints)

/-- Compiles the definition `declName`, whose parameters and result are all
`UInt64`, to an IR function with hints.  The compiler reads the definition's
unfolding equation, so a recursive call appears as a call of `declName`.  A
definition without recursive calls becomes a result expression; a definition
whose recursive calls are all in tail position becomes a loop. -/
def compileScalar (declName : Name) : MetaM (Func × Hints) := do
  let env ← getEnv
  let .defnInfo _ ← getConstInfo declName
    | throwError "{declName} is not a definition"
  if (Compiler.implementedByAttr.getParam? env declName).isSome || isExtern env declName then
    throwError "{declName} has an implementation other than its definition"
  let some equation ← getUnfoldEqnFor? declName (nonRec := true)
    | throwError "{declName} has no unfolding equation"
  forallTelescope (← getConstInfo equation).type fun params eq => do
    let some (_, _, body) := eq.eq?
      | throwError "unexpected unfolding equation for {declName}"
    for param in params do
      unless ← isUInt64 (← inferType param) do
        throwError "parameter {param} of {declName} is not UInt64"
    unless ← isUInt64 (← inferType body) do
      throwError "the result of {declName} is not UInt64"
    let paramNames ← params.toList.mapM fun p => return (← p.fvarId!.getUserName).toString
    let recursive := (body.find? fun e => e.isConstOf declName).isSome
    if recursive then
      let ctx : Ctx := { self := declName, params, scratch := params.size + params.size + 2 }
      -- The loop is the first instruction of the body: a block holding a loop.
      let loopBody := ((({ prefix_ := [], index := 0 } : Loc).inside none).inside none)
      let condition : IRExpr .bool := .eq (.get ctx.done) (.const 0)
      let (step, stepHints) ← translateTail ctx
        (loopBody.skip ((condition.program ctx.scratch).length + 2)) body
      let loop : Project.IR.Stmt := .while condition step
      let loopHint := mkHint { prefix_ := [], index := 0 } (loop.program ctx.scratch).length
        "tail-recursion-loop" (← sourceOf body)
      let resultHint := mkHint { prefix_ := [], index := 1 } 1 "result" "result"
      let names := paramNames.zipIdx ++
        [("result", ctx.result), ("done", ctx.done)] ++
        (paramNames.zipIdx.map fun (name, i) => (s!"next {name}", ctx.temp i))
      return ({ params := params.size, vars := ctx.vars, body := loop, result := .get ctx.result },
        { locals := names, nodes := loopHint :: stepHints ++ [resultHint] })
    else
      let ctx : Ctx := { self := declName, params, scratch := params.size }
      let (result, nodes) ← translateValue ctx ctx.scratch { prefix_ := [], index := 0 } body
      return ({ params := params.size, vars := 0, body := .skip, result },
        { locals := paramNames.zipIdx, nodes })

deriving instance ToExpr for U64Op

/-- The Lean term for an IR expression, for the definitions the command adds. -/
def irToExpr : {type : ScalarType} → IRExpr type → Lean.Expr
  | _, .get index => mkApp (mkConst ``Project.ProofKit.ScalarTransition.Expr.get) (toExpr index)
  | _, .const value => mkApp (mkConst ``Project.ProofKit.ScalarTransition.Expr.const) (toExpr value)
  | _, .bconst value => mkApp (mkConst ``Project.ProofKit.ScalarTransition.Expr.bconst) (toExpr value)
  | _, .bin op left right => mkApp3 (mkConst ``Project.ProofKit.ScalarTransition.Expr.bin) (toExpr op) (irToExpr left) (irToExpr right)
  | _, .eq left right => mkApp2 (mkConst ``Project.ProofKit.ScalarTransition.Expr.eq) (irToExpr left) (irToExpr right)
  | _, .ne left right => mkApp2 (mkConst ``Project.ProofKit.ScalarTransition.Expr.ne) (irToExpr left) (irToExpr right)
  | _, .ltU left right => mkApp2 (mkConst ``Project.ProofKit.ScalarTransition.Expr.ltU) (irToExpr left) (irToExpr right)
  | _, .leU left right => mkApp2 (mkConst ``Project.ProofKit.ScalarTransition.Expr.leU) (irToExpr left) (irToExpr right)
  | _, .not condition => mkApp (mkConst ``Project.ProofKit.ScalarTransition.Expr.not) (irToExpr condition)
  | _, .and left right => mkApp2 (mkConst ``Project.ProofKit.ScalarTransition.Expr.and) (irToExpr left) (irToExpr right)
  | _, .or left right => mkApp2 (mkConst ``Project.ProofKit.ScalarTransition.Expr.or) (irToExpr left) (irToExpr right)
  | _, .ite condition thenValue elseValue =>
      mkApp3 (mkConst ``Project.ProofKit.ScalarTransition.Expr.ite) (irToExpr condition) (irToExpr thenValue) (irToExpr elseValue)

def stmtToExpr : Project.IR.Stmt → Lean.Expr
  | .skip => mkConst ``Project.IR.Stmt.skip
  | .assign index value => mkApp2 (mkConst ``Project.IR.Stmt.assign) (toExpr index) (irToExpr value)
  | .seq first second => mkApp2 (mkConst ``Project.IR.Stmt.seq) (stmtToExpr first) (stmtToExpr second)
  | .ite condition thenStmt elseStmt =>
      mkApp3 (mkConst ``Project.IR.Stmt.ite) (irToExpr condition) (stmtToExpr thenStmt)
        (stmtToExpr elseStmt)
  | .while condition body =>
      mkApp2 (mkConst ``Project.IR.Stmt.while) (irToExpr condition) (stmtToExpr body)

def funcToExpr (func : Func) : Lean.Expr :=
  mkApp4 (mkConst ``Func.mk) (toExpr func.params) (toExpr func.vars) (stmtToExpr func.body)
    (irToExpr func.result)

end Project.Compiler
