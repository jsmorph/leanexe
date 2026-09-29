import Lean
import Project.IR.ArrayLiteral
import Project.IR.Fold
import Project.IR.Release
import Project.IR.Function
import Project.IR.Hint

namespace Project.Compiler

open Lean Meta Project.IR

abbrev IRExpr := Project.IR.Expr

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

def isFloat (type : Lean.Expr) : MetaM Bool := do
  return (← whnfR type).isConstOf ``Float

/-- The source operators on `Float` the compiler translates. -/
def floatRules : List (Name × F64Op × String) :=
  [(``HAdd.hAdd, .add, "float add"), (``HSub.hSub, .sub, "float sub"),
   (``HMul.hMul, .mul, "float mul")]

def isUInt64Array (type : Lean.Expr) : MetaM Bool := do
  let type ← whnfR type
  if type.isAppOfArity ``Array 1 then isUInt64 type.appArg! else return false

/-- The number of instructions in the code of an expression or a statement.  It
does not depend on the scratch index. -/
def exprLength (e : IRExpr type) : Nat := (e.program 0).length
def stmtLength (s : Project.IR.Stmt) : Nat := (s.program 0).length

/-- The compiler's view of the definition being compiled.  `words`, `floats`, and
`arrays` give the local of each `UInt64`, `Float`, and `Array UInt64` variable in
scope.  A
recursive definition's locals are the parameters, then `result`, `done`, and one
temporary per parameter.  `foldable` says whether a fold may appear: a fold runs
before the value that contains it, so it may not appear in a branch, in a fold
body, or in a recursive definition. -/
structure Ctx where
  self : Name
  params : Array Lean.Expr
  words : List (Lean.Expr × Nat)
  floats : List (Lean.Expr × Nat)
  arrays : List (Lean.Expr × Nat)
  foldable : Bool

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

/-- The hint for code moved `offset` instructions later in the function body. -/
def Hint.shift (offset : Nat) (hint : Hint) : Hint :=
  match hint.path with
  | i :: rest => { hint with path := (i + offset) :: rest }
  | [] => hint

/-- The start of the body's code in a fold whose code starts at `loc`: inside the
block and loop of the `while`, after the condition, the exit test, and the
element load. -/
def foldBodyLoc (loc : Loc) : Project.IR.Stmt → Loc
  | .seq first (.seq second (.while condition (.seq load _))) =>
      (((loc.skip (stmtLength first + stmtLength second)).inside none).inside none).skip
        (exprLength condition + 2 + stmtLength load)
  | _ => loc

def sourceOf (term : Lean.Expr) : MetaM String := return toString (← ppExpr term)

/-- The elements of an array literal `#[e₀, …]`, which elaborates to
`List.toArray [e₀, …]`. -/
def arrayLiteral? (term : Lean.Expr) : Option (List Lean.Expr) :=
  match term.consumeMData.getAppFnArgs with
  | (``List.toArray, #[_, list]) => list.consumeMData.listLit?.map (·.2)
  | _ => none

/-- Statements that run before the value being translated and become the start
of the function body, with their hints, their code length, and the compiler's
variables. -/
structure Prelude where
  stmts : Array Project.IR.Stmt := #[]
  hints : Array Hint := #[]
  length : Nat := 0
  next : Nat
  names : Array (String × Nat) := #[]

abbrev CompileM := StateT Prelude MetaM

mutual
  /-- Translates a `UInt64` term to an IR expression whose code starts at `loc`.
  A fold in the term adds its statements to the prelude, and the expression reads
  its accumulator. -/
  partial def translateValue (ctx : Ctx) (loc : Loc) (term : Lean.Expr) :
      CompileM (IRExpr .u64 × List Hint) := do
    let term := term.consumeMData
    let source ← sourceOf term
    let hint (ir : IRExpr .u64) (rule : String) : Hint :=
      mkHint loc (exprLength ir) rule source
    if let some index := ctx.words.lookup term then
      let ir : IRExpr .u64 := .get index
      return (ir, [hint ir "variable"])
    if (ctx.arrays.lookup term).isSome then
      throwError "the array {source} is used as a value"
    match term.getAppFnArgs with
    | (``OfNat.ofNat, #[type, .lit (.natVal value), _]) =>
        unless ← isUInt64 type do throwError "unsupported literal type: {type}"
        let ir : IRExpr .u64 := .const (UInt64.ofNat value)
        return (ir, [hint ir "literal"])
    | (``ite, #[type, condition, _, thenTerm, elseTerm]) =>
        unless ← isUInt64 type do throwError "unsupported conditional type in {source}"
        let inner := { ctx with foldable := false }
        let (c, cHints) ← translateCondition inner loc condition
        let branch := loc.skip (exprLength c)
        let (a, aHints) ← translateValue inner (branch.inside (some 0)) thenTerm
        let (b, bHints) ← translateValue inner (branch.inside (some 1)) elseTerm
        let ir : IRExpr .u64 := .ite c a b
        return (ir, hint ir "conditional value" :: cHints ++ aHints ++ bHints)
    | (``Nat.toUInt64, #[size]) =>
        let (``Array.size, #[_, array]) := size.consumeMData.getAppFnArgs
          | throwError "unsupported term: {source}"
        unless ctx.foldable do
          throwError "an array size may not appear in a branch, a fold body, or a recursive definition: {source}"
        let some arrayLocal := ctx.arrays.lookup array.consumeMData
          | throwError "the size must be of an array variable: {source}"
        let before ← get
        let temp := before.next
        let stmt := Stmt.arraySize temp arrayLocal
        set { before with
          stmts := before.stmts.push stmt
          hints := before.hints.push
            (mkHint ⟨[], before.length⟩ (stmtLength stmt) "array-size" source)
          length := before.length + stmtLength stmt
          next := temp + 1
          names := before.names.push ("size", temp) }
        let ir : IRExpr .u64 := .get temp
        return (ir, [hint ir "size result"])
    | (``Array.foldl, #[element, acc, f, init, array, start, stop]) =>
        unless ctx.foldable do
          throwError "a fold may not appear in a branch, a fold body, or a recursive definition: {source}"
        unless (← isUInt64 element) && (← isUInt64 acc) do
          throwError "unsupported fold types in {source}"
        unless start.nat? == some 0 do throwError "a fold must start at index 0: {source}"
        match stop.consumeMData.getAppFnArgs with
        | (``Array.size, #[_, sized]) =>
            unless sized.consumeMData == array.consumeMData do
              throwError "a fold must stop at the size of its array: {source}"
        | _ => throwError "a fold must stop at the size of its array: {source}"
        -- An array literal becomes a temporary that is released after the fold.
        let (arrayLocal, temporary) ← match ctx.arrays.lookup array.consumeMData with
          | some index => pure (index, false)
          | none => do
              let some elements := arrayLiteral? array
                | throwError "a fold must run over an array variable or an array literal: {source}"
              pure (← translateArrayLiteral ctx array elements, true)
        let (initial, initialHints) ← translateValue ctx ⟨[], 0⟩ init
        let before ← get
        let accLocal := before.next
        let (indexLocal, lengthLocal, elementLocal) := (accLocal + 1, accLocal + 2, accLocal + 3)
        let assign : Project.IR.Stmt := .assign accLocal initial
        let foldLoc : Loc := ⟨[], before.length + stmtLength assign⟩
        let bodyLoc := foldBodyLoc foldLoc
          (Stmt.fold arrayLocal accLocal indexLocal lengthLocal elementLocal (.const 0))
        let (body, bodyHints) ← withLocalDeclD `acc acc fun a => withLocalDeclD `element element
          fun e => translateValue
            { ctx with words := (a, accLocal) :: (e, elementLocal) :: ctx.words, foldable := false }
            bodyLoc (mkApp2 f a e).headBeta
        let fold := Stmt.fold arrayLocal accLocal indexLocal lengthLocal elementLocal body
        let arraySource ← sourceOf array
        let releases : List (Project.IR.Stmt × Hint) := if temporary then
            [(.release arrayLocal, mkHint ⟨[], before.length + stmtLength assign + stmtLength fold⟩
              (stmtLength (.release arrayLocal)) "release-temporary" arraySource)]
          else []
        set { before with
          stmts := (before.stmts.push assign |>.push fold) ++
            (releases.map Prod.fst).toArray
          hints := before.hints ++
            (mkHint ⟨[], before.length⟩ (stmtLength assign) "fold start" (← sourceOf init) ::
              initialHints.map (Hint.shift before.length) ++
              mkHint foldLoc (stmtLength fold) "array-fold-loop" source :: bodyHints ++
              releases.map Prod.snd).toArray
          length := before.length + stmtLength assign + stmtLength fold +
            (releases.map (stmtLength ∘ Prod.fst)).sum
          next := accLocal + 4
          names := before.names ++ #[("accumulator", accLocal), ("index", indexLocal),
            ("length", lengthLocal), ("element", elementLocal)] }
        let ir : IRExpr .u64 := .get accLocal
        return (ir, [hint ir "fold result"])
    | (fn, #[left, right, out, _, a, b]) =>
        let some (_, op, rule) := binaryRules.find? (·.1 == fn)
          | throwError "unsupported operation {fn} in {source}"
        unless (← isUInt64 left) && (← isUInt64 right) && (← isUInt64 out) do
          throwError "unsupported operand types in {source}"
        let (l, lHints) ← translateValue ctx loc a
        let offset := if op = .divU ∨ op = .remU then exprLength l + 1 else exprLength l
        let (r, rHints) ← translateValue ctx (loc.skip offset) b
        let ir : IRExpr .u64 := .bin op l r
        return (ir, hint ir rule :: lHints ++ rHints)
    | _ => throwError "unsupported term: {source}"

  /-- Translates a decidable proposition about `UInt64` values to an IR
  condition. -/
  partial def translateCondition (ctx : Ctx) (loc : Loc) (prop : Lean.Expr) :
      CompileM (IRExpr .bool × List Hint) := do
    let prop := prop.consumeMData
    let source ← sourceOf prop
    let hint (ir : IRExpr .bool) (rule : String) : Hint :=
      mkHint loc (exprLength ir) rule source
    let pair (make : IRExpr .u64 → IRExpr .u64 → IRExpr .bool) (rule : String)
        (a b : Lean.Expr) : CompileM (IRExpr .bool × List Hint) := do
      let (l, lHints) ← translateValue ctx loc a
      let (r, rHints) ← translateValue ctx (loc.skip (exprLength l)) b
      let ir := make l r
      return (ir, hint ir rule :: lHints ++ rHints)
    let connective (make : IRExpr .bool → IRExpr .bool → IRExpr .bool) (rule : String)
        (a b : Lean.Expr) : CompileM (IRExpr .bool × List Hint) := do
      let (l, lHints) ← translateCondition ctx loc a
      let inner := (loc.skip (exprLength l)).inside (some (if rule == "and" then 0 else 1))
      let (r, rHints) ← translateCondition { ctx with foldable := false } inner b
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
        let (c, cHints) ← translateCondition ctx loc p
        let ir : IRExpr .bool := .not c
        return (ir, hint ir "not" :: cHints)
    | (``And, #[a, b]) => connective .and "and" a b
    | (``Or, #[a, b]) => connective .or "or" a b
    | _ => throwError "unsupported condition: {source}"

  /-- Translates a `Float` term to an IR expression whose code starts at `loc`. -/
  partial def translateFloat (ctx : Ctx) (loc : Loc) (term : Lean.Expr) :
      CompileM (IRExpr .f64 × List Hint) := do
    let term := term.consumeMData
    let source ← sourceOf term
    let hint (ir : IRExpr .f64) (rule : String) : Hint :=
      mkHint loc (exprLength ir) rule source
    if let some index := ctx.floats.lookup term then
      let ir : IRExpr .f64 := .getF index
      return (ir, [hint ir "float variable"])
    match term.getAppFnArgs with
    | (fn, #[left, right, out, _, a, b]) =>
        let some (_, op, rule) := floatRules.find? (·.1 == fn)
          | throwError "unsupported float operation {fn} in {source}"
        unless (← isFloat left) && (← isFloat right) && (← isFloat out) do
          throwError "unsupported operand types in {source}"
        let (l, lHints) ← translateFloat ctx loc a
        let (r, rHints) ← translateFloat ctx (loc.skip (exprLength l)) b
        let ir : IRExpr .f64 := .binF op l r
        return (ir, hint ir rule :: lHints ++ rHints)
    | _ => throwError "unsupported float term: {source}"

  /-- Translates the array literal `term` with `elements` to an allocation and
  stores into a fresh local, which it returns.  Folds in the elements run first. -/
  partial def translateArrayLiteral (ctx : Ctx) (term : Lean.Expr) (elements : List Lean.Expr) :
      CompileM Nat := do
    let mut values : Array (IRExpr .u64) := #[]
    let mut valueHints : Array (List Hint) := #[]
    for element in elements do
      let (value, hints) ← translateValue ctx ⟨[], 0⟩ element
      values := values.push value
      valueHints := valueHints.push hints
    let before ← get
    let temp := before.next
    let literal := Stmt.arrayLiteral temp values.toList
    -- Element `i`'s value follows the call, the length store, the earlier element
    -- stores, and its own address code.
    let address : IRExpr .u64 := .bin .add (.get temp) (.const 0)
    let elementHints := (List.range values.size).flatMap fun i =>
      (valueHints[i]!).map (Hint.shift (before.length +
        stmtLength (Stmt.arrayLiteral temp (values.toList.take i)) + exprLength address + 1))
    set { before with
      stmts := before.stmts.push literal
      hints := before.hints ++
        (mkHint ⟨[], before.length⟩ (stmtLength literal) "array-literal" (← sourceOf term) ::
          elementHints).toArray
      length := before.length + stmtLength literal
      next := temp + 1
      names := before.names.push ("array", temp) }
    return temp
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
    CompileM (Project.IR.Stmt × List Hint) := do
  let term := term.consumeMData
  let source ← sourceOf term
  match term.getAppFnArgs with
  | (``ite, #[_, condition, _, thenTerm, elseTerm]) =>
      let (c, cHints) ← translateCondition ctx loc condition
      let branch := loc.skip (exprLength c)
      let (a, aHints) ← translateTail ctx (branch.inside (some 0)) thenTerm
      let (b, bHints) ← translateTail ctx (branch.inside (some 1)) elseTerm
      let stmt : Project.IR.Stmt := .ite c a b
      return (stmt, mkHint loc (stmtLength stmt) "branch" source :: cHints ++ aHints ++ bHints)
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
          let (value, valueHints) ← translateValue ctx here args[i]!
          let stmt : Project.IR.Stmt := .assign (ctx.temp i) value
          stmts := stmts ++ [stmt]
          hints := hints ++ valueHints
          here := here.skip (stmtLength stmt)
        for i in [:args.size] do
          stmts := stmts ++ [.assign i (.get (ctx.temp i))]
        let stmt := seqAll stmts
        return (stmt, mkHint loc (stmtLength stmt) "tail call" source :: hints)
      else
        let (value, valueHints) ← translateValue ctx loc term
        let stmt : Project.IR.Stmt :=
          .seq (.assign ctx.result value) (.assign ctx.done (.const 1))
        return (stmt, mkHint loc (stmtLength stmt) "base case" source :: valueHints)

/-- Compiles the definition `declName`, whose parameters are `UInt64` or
`Array UInt64` and whose result is `UInt64` or an `Array UInt64` literal, to an
IR function with hints.  The
compiler reads the definition's unfolding equation, so a recursive call appears
as a call of `declName`.  A definition without recursive calls becomes a prelude
of folds and a result expression; a definition whose recursive calls are all in
tail position becomes a loop. -/
def compileDefinition (declName : Name) : MetaM (Func × Hints) := do
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
    let mut words := []
    let mut floats := []
    let mut arrays := []
    let mut paramTypes : Array ScalarType := #[]
    for h : i in [:params.size] do
      let type ← inferType params[i]
      if ← isUInt64 type then
        words := (params[i], i) :: words
        paramTypes := paramTypes.push .u64
      else if ← isFloat type then
        floats := (params[i], i) :: floats
        paramTypes := paramTypes.push .f64
      else if ← isUInt64Array type then
        arrays := (params[i], i) :: arrays
        paramTypes := paramTypes.push .u64
      else
        throwError "parameter {params[i]} of {declName} is not UInt64, Float, or Array UInt64"
    let resultType ← inferType body
    let arrayResult ← isUInt64Array resultType
    let floatResult ← isFloat resultType
    unless arrayResult || floatResult || (← isUInt64 resultType) do
      throwError "the result of {declName} is not UInt64, Float, or Array UInt64"
    let paramNames ← params.toList.mapM fun p => return (← p.fvarId!.getUserName).toString
    let recursive := (body.find? fun e => e.isConstOf declName).isSome
    if recursive then
      unless arrays.isEmpty && floats.isEmpty && !arrayResult && !floatResult do
        throwError "a recursive definition may take and return only UInt64: {declName}"
      let ctx : Ctx := { self := declName, params, words, floats, arrays, foldable := false }
      -- The loop is the first instruction of the body: a block holding a loop.
      let loopBody := ((({ prefix_ := [], index := 0 } : Loc).inside none).inside none)
      let condition : IRExpr .bool := .eq (.get ctx.done) (.const 0)
      let (step, stepHints) ← (translateTail ctx
        (loopBody.skip (exprLength condition + 2)) body).run' { next := ctx.vars }
      let loop : Project.IR.Stmt := .while condition step
      let loopHint := mkHint { prefix_ := [], index := 0 } (stmtLength loop)
        "tail-recursion-loop" (← sourceOf body)
      let resultHint := mkHint { prefix_ := [], index := 1 } 1 "result" "result"
      let names := paramNames.zipIdx ++
        [("result", ctx.result), ("done", ctx.done)] ++
        (paramNames.zipIdx.map fun (name, i) => (s!"next {name}", ctx.temp i))
      let func : Func :=
        { params := paramTypes.toList, vars := ctx.vars, body := loop
          result := ⟨.u64, .get ctx.result⟩ }
      return (func, { locals := names, nodes := loopHint :: stepHints ++ [resultHint] })
    else
      let ctx : Ctx := { self := declName, params, words, floats, arrays, foldable := true }
      let translate : CompileM ((Σ type, IRExpr type) × List Hint) :=
        if arrayResult then do
          let some elements := arrayLiteral? body
            | throwError "an Array UInt64 result must be an array literal: {← sourceOf body}"
          let array ← translateArrayLiteral ctx body elements
          let ir : IRExpr .u64 := .get array
          return (⟨.u64, ir⟩,
            [mkHint ⟨[], 0⟩ (exprLength ir) "array result" (← sourceOf body)])
        else if floatResult then do
          let (ir, hints) ← translateFloat ctx { prefix_ := [], index := 0 } body
          return (⟨.f64, ir⟩, hints)
        else do
          let (ir, hints) ← translateValue ctx { prefix_ := [], index := 0 } body
          return (⟨.u64, ir⟩, hints)
      let ((result, resultHints), prelude) ← translate.run { next := params.size }
      let func : Func :=
        { params := paramTypes.toList, vars := prelude.next - params.size
          body := seqAll prelude.stmts.toList, result }
      let hints : Hints :=
        { locals := paramNames.zipIdx ++ prelude.names.toList
          nodes := prelude.hints.toList ++ resultHints.map (Hint.shift prelude.length) }
      return (func, hints)

deriving instance ToExpr for U64Op
deriving instance ToExpr for F64Op
deriving instance ToExpr for ScalarType

/-- The Lean term for an IR expression, for the definitions the command adds. -/
def irToExpr : {type : ScalarType} → IRExpr type → Lean.Expr
  | _, .get index => mkApp (mkConst ``Project.IR.Expr.get) (toExpr index)
  | _, .getF index => mkApp (mkConst ``Project.IR.Expr.getF) (toExpr index)
  | _, .binF op left right =>
      mkApp3 (mkConst ``Project.IR.Expr.binF) (toExpr op) (irToExpr left) (irToExpr right)
  | _, .const value => mkApp (mkConst ``Project.IR.Expr.const) (toExpr value)
  | _, .bconst value => mkApp (mkConst ``Project.IR.Expr.bconst) (toExpr value)
  | _, .bin op left right => mkApp3 (mkConst ``Project.IR.Expr.bin) (toExpr op) (irToExpr left) (irToExpr right)
  | _, .eq left right => mkApp2 (mkConst ``Project.IR.Expr.eq) (irToExpr left) (irToExpr right)
  | _, .ne left right => mkApp2 (mkConst ``Project.IR.Expr.ne) (irToExpr left) (irToExpr right)
  | _, .ltU left right => mkApp2 (mkConst ``Project.IR.Expr.ltU) (irToExpr left) (irToExpr right)
  | _, .leU left right => mkApp2 (mkConst ``Project.IR.Expr.leU) (irToExpr left) (irToExpr right)
  | _, .not condition => mkApp (mkConst ``Project.IR.Expr.not) (irToExpr condition)
  | _, .and left right => mkApp2 (mkConst ``Project.IR.Expr.and) (irToExpr left) (irToExpr right)
  | _, .or left right => mkApp2 (mkConst ``Project.IR.Expr.or) (irToExpr left) (irToExpr right)
  | _, .ite condition thenValue elseValue =>
      mkApp3 (mkConst ``Project.IR.Expr.ite) (irToExpr condition) (irToExpr thenValue) (irToExpr elseValue)

def stmtToExpr : Project.IR.Stmt → Lean.Expr
  | .skip => mkConst ``Project.IR.Stmt.skip
  | .assign index value => mkApp2 (mkConst ``Project.IR.Stmt.assign) (toExpr index) (irToExpr value)
  | .seq first second => mkApp2 (mkConst ``Project.IR.Stmt.seq) (stmtToExpr first) (stmtToExpr second)
  | .ite condition thenStmt elseStmt =>
      mkApp3 (mkConst ``Project.IR.Stmt.ite) (irToExpr condition) (stmtToExpr thenStmt)
        (stmtToExpr elseStmt)
  | .while condition body =>
      mkApp2 (mkConst ``Project.IR.Stmt.while) (irToExpr condition) (stmtToExpr body)
  | .load index address =>
      mkApp2 (mkConst ``Project.IR.Stmt.load) (toExpr index) (irToExpr address)
  | .store address value =>
      mkApp2 (mkConst ``Project.IR.Stmt.store) (irToExpr address) (irToExpr value)
  | .call func args result =>
      mkApp3 (mkConst ``Project.IR.Stmt.call) (toExpr func)
        (let type := mkApp (mkConst ``Project.IR.Expr) (mkConst ``Project.IR.ScalarType.u64)
         args.foldr (fun arg list => mkApp3 (mkConst ``List.cons [Level.zero]) type (irToExpr arg) list)
           (mkApp (mkConst ``List.nil [Level.zero]) type))
        (toExpr result)

def funcToExpr (func : Func) : Lean.Expr :=
  mkApp4 (mkConst ``Func.mk) (toExpr func.params) (toExpr func.vars) (stmtToExpr func.body)
    (mkApp4 (mkConst ``Sigma.mk [Level.zero, Level.zero]) (mkConst ``ScalarType)
      (mkConst ``Project.IR.Expr) (toExpr func.result.1) (irToExpr func.result.2))

end Project.Compiler
