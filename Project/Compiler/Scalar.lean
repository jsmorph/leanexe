import Lean
import Project.IR.ArrayLiteral
import Project.IR.Fold
import Project.IR.Release
import Project.IR.Function
import Project.IR.Loop
import Project.IR.Build
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
   (``HMul.hMul, .mul, "float mul"), (``HDiv.hDiv, .div, "float div")]

def isUInt64Array (type : Lean.Expr) : MetaM Bool := do
  let type ← whnfR type
  if type.isAppOfArity ``Array 1 then isUInt64 type.appArg! else return false

def isFloatArray (type : Lean.Expr) : MetaM Bool := do
  let type ← whnfR type
  if type.isAppOfArity ``Array 1 then isFloat type.appArg! else return false

/-- The number of instructions in the code of an expression or a statement.  It
does not depend on the scratch index. -/
def exprLength (e : IRExpr type) : Nat := (e.program 0).length
def stmtLength (s : Project.IR.Stmt) : Nat := (s.program 0).length

/-- The compiler's view of the definition being compiled.  `words`, `floats`,
`arrays`, and `floatArrays` give the local of each `UInt64`, `Float`,
`Array UInt64`, and `Array Float` variable in scope, and `tuples` gives the
locals of each pair-valued variable's components.  A recursive definition's
locals are the parameters, then `result`, `done`, and one temporary per
parameter.  `foldable` says whether a fold may appear: a fold runs
before the value that contains it, so it may not appear in a branch, in a fold
body, or in a recursive definition. -/
structure Ctx where
  self : Name
  params : Array Lean.Expr
  words : List (Lean.Expr × Nat)
  floats : List (Lean.Expr × Nat)
  arrays : List (Lean.Expr × Nat)
  floatArrays : List (Lean.Expr × Nat)
  tuples : List (Lean.Expr × List (Nat × ScalarType)) := []
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
of the function body, with their hints, their code length, and the types of the
compiler's variables, which start at local `base`. -/
structure Prelude where
  stmts : Array Project.IR.Stmt := #[]
  hints : Array Hint := #[]
  length : Nat := 0
  base : Nat
  vars : Array ScalarType := #[]
  names : Array (String × Nat) := #[]

/-- The next free local. -/
def Prelude.next (p : Prelude) : Nat := p.base + p.vars.size

abbrev CompileM := StateT Prelude MetaM

/-- `stmts` in sequence, with the code of each placed after the previous. -/
def seqAll : List Project.IR.Stmt → Project.IR.Stmt
  | [] => .skip
  | [s] => s
  | s :: rest => .seq s (seqAll rest)

/-- The scalar type of a `UInt64` or `Float` type. -/
def scalarTypeOf (type : Lean.Expr) : MetaM ScalarType := do
  if ← isUInt64 type then return .u64
  if ← isFloat type then return .f64
  throwError "unsupported type {type}"

/-- The components of a loop state: a `UInt64`, a `Float`, or a pair of states,
flattened from the left. -/
partial def stateTypes (type : Lean.Expr) : MetaM (List ScalarType) := do
  let type ← whnfR type
  if type.isAppOfArity ``Prod 2 then
    return (← stateTypes type.appFn!.appArg!) ++ (← stateTypes type.appArg!)
  return [← scalarTypeOf type]

/-- The component terms of `term`, a nest of `Prod.mk` of type `type`. -/
partial def stateTerms (term type : Lean.Expr) : MetaM (List (Lean.Expr × ScalarType)) := do
  let type ← whnfR type
  if type.isAppOfArity ``Prod 2 then
    let (``Prod.mk, #[first, second, a, b]) := term.consumeMData.getAppFnArgs
      | throwError "a loop state must be a tuple of components: {← sourceOf term}"
    return (← stateTerms a first) ++ (← stateTerms b second)
  return [(term, ← scalarTypeOf type)]

instance : Inhabited (Σ type, IRExpr type) := ⟨⟨.u64, .const 0⟩⟩

/-- A fresh local of type `type`. -/
def fresh (type : ScalarType) (name : String) : CompileM Nat := do
  let p ← get
  set { p with vars := p.vars.push type, names := p.names.push (name, p.next) }
  return p.next

/-- Binds `x` to the locals `components`: a variable for one component, a tuple
otherwise. -/
def Ctx.bind (ctx : Ctx) (x : Lean.Expr) : List (Nat × ScalarType) → Ctx
  | [(index, .f64)] => { ctx with floats := (x, index) :: ctx.floats }
  | [(index, _)] => { ctx with words := (x, index) :: ctx.words }
  | components => { ctx with tuples := (x, components) :: ctx.tuples }

/-- The unfolding of a `match` auxiliary definition applied to its arguments. -/
def unfoldMatcher? (term : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let .const name levels := term.getAppFn | return none
  unless ← isMatcher name do return none
  let value ← instantiateValueLevelParams (← getConstInfo name) levels
  return value.beta term.getAppArgs

/-- Where a loop's body code starts when its code starts at `loc`: inside the
block and loop of the `while`, after the count, the two assignments, the
condition, and the exit test. -/
def loopBodyLoc (loc : Loc) (count : IRExpr .u64) : Loc :=
  (((loc.skip (exprLength count + 3)).inside none).inside none).skip
    (exprLength (.ltU (.get 0) (.get 0) : IRExpr .bool) + 2)

/-- Where the element code of the copying template starts when the template's code
starts at `loc`: inside the block and loop of its `while`, after the condition,
the exit test, the element address, and its wrap to 32 bits. -/
def buildElementLoc (loc : Loc) (dst limit index : Nat) (count : IRExpr .u64) : Loc :=
  let before : List Project.IR.Stmt := [.assign limit count,
    .call 1 [.bin .mul (.bin .add (.get limit) (.const 1)) (.const 8)] (some dst),
    .store (.get dst) (.get limit), .assign index (.const 0)]
  let address : IRExpr .u64 :=
    .bin .add (.get dst) (.bin .mul (.bin .add (.get index) (.const 1)) (.const 8))
  (((loc.skip (before.map stmtLength).sum).inside none).inside none).skip
    (exprLength (.ltU (.get index) (.get limit) : IRExpr .bool) + 2 + exprLength address + 1)

/-- The hint for code at `path` inside the code a hint's path is relative to. -/
def Hint.within (path : List Nat) (hint : Hint) : Hint := { hint with path := path ++ hint.path }

/-- Runs `action` with an empty statement list and returns its statements and
hints, relative to their own start, while keeping the locals it allocates. -/
def withBlock (action : CompileM α) : CompileM (α × List Project.IR.Stmt × List Hint) := do
  let saved ← get
  set { saved with stmts := #[], hints := #[], length := 0 }
  let result ← action
  let inner ← get
  set { inner with stmts := saved.stmts, hints := saved.hints, length := saved.length }
  return (result, inner.stmts.toList, inner.hints.toList)

/-- Pushes `stmt` to the prelude with its hints, which are relative to its start. -/
def pushStmt (stmt : Project.IR.Stmt) (hints : List Hint) : CompileM Unit :=
  modify fun p => { p with
    stmts := p.stmts.push stmt
    hints := p.hints ++ (hints.map (Hint.shift p.length)).toArray
    length := p.length + stmtLength stmt }

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
    if (ctx.arrays.lookup term).isSome || (ctx.floatArrays.lookup term).isSome then
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
        let some arrayLocal := (ctx.arrays ++ ctx.floatArrays).lookup array.consumeMData
          | throwError "the size must be of an array variable: {source}"
        let before ← get
        let temp := before.next
        let stmt := Stmt.arraySize temp arrayLocal
        set { before with
          stmts := before.stmts.push stmt
          hints := before.hints.push
            (mkHint ⟨[], before.length⟩ (stmtLength stmt) "array-size" source)
          length := before.length + stmtLength stmt
          vars := before.vars.push .u64
          names := before.names.push ("size", temp) }
        let ir : IRExpr .u64 := .get temp
        return (ir, [hint ir "size result"])
    | (``Array.foldl, _) =>
        let ir : IRExpr .u64 := .get (← translateFold ctx term .u64)
        return (ir, [hint ir "fold result"])
    | (``LeanExe.loop, _) =>
        let [(state, .u64)] ← translateLoop ctx term
          | throwError "a loop used as a word must have a word state: {source}"
        let ir : IRExpr .u64 := .get state
        return (ir, [hint ir "loop result"])
    | (``Min.min, #[type, _, a, b]) =>
        unless ← isUInt64 type do throwError "unsupported min type in {source}"
        -- `min a b` is `if a ≤ b then a else b`.
        let inner := { ctx with foldable := false }
        let (l, lHints) ← translateValue inner loc a
        let (r, rHints) ← translateValue inner (loc.skip (exprLength l)) b
        let condition : IRExpr .bool := .leU l r
        let branch := loc.skip (exprLength condition)
        let (x, xHints) ← translateValue inner (branch.inside (some 0)) a
        let (y, yHints) ← translateValue inner (branch.inside (some 1)) b
        let ir : IRExpr .u64 := .ite condition x y
        return (ir, hint ir "min" :: lHints ++ rHints ++ xHints ++ yHints)
    | (``GetElem?.getElem!, #[collection, _, element, _, _, _, array, position]) =>
        unless (← isUInt64Array collection) && (← isUInt64 element) do
          throwError "unsupported array read in {source}"
        let some arrayLocal := ctx.arrays.lookup array.consumeMData
          | throwError "a read must be of an array variable: {source}"
        let (``UInt64.toNat, #[k]) := position.consumeMData.getAppFnArgs
          | throwError "a read position must be `i.toNat` for a UInt64 `i`: {source}"
        let (i, iHints) ← translateValue ctx loc k
        let ir : IRExpr .u64 := .read arrayLocal i
        return (ir, hint ir "array read" :: iHints)
    | (``Float.toUInt64, #[operand]) =>
        let (x, xHints) ← translateFloat ctx loc operand
        let ir : IRExpr .u64 := .truncSatU x
        return (ir, hint ir "float to word" :: xHints)
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
    let floatPair (make : IRExpr .f64 → IRExpr .f64 → IRExpr .bool) (rule : String)
        (a b : Lean.Expr) : CompileM (IRExpr .bool × List Hint) := do
      let (l, lHints) ← translateFloat ctx loc a
      let (r, rHints) ← translateFloat ctx (loc.skip (exprLength l)) b
      let ir := make l r
      return (ir, hint ir rule :: lHints ++ rHints)
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
    | (``Eq, #[type, lhs, rhs]) =>
        -- `a == b` on floats appears as `(a == b) = true`.
        if (← whnfR type).isConstOf ``Bool && rhs.consumeMData.isConstOf ``Bool.true then
          match lhs.consumeMData.getAppFnArgs with
          | (``BEq.beq, #[floatType, _, a, b]) =>
              unless ← isFloat floatType do throwError "unsupported equality type in {source}"
              floatPair .eqF "float equal" a b
          | _ => throwError "unsupported condition: {source}"
        else
          unless ← isUInt64 type do throwError "unsupported equality type in {source}"
          pair .eq "equal" lhs rhs
    | (``Ne, #[type, a, b]) =>
        unless ← isUInt64 type do throwError "unsupported inequality type in {source}"
        pair .ne "not equal" a b
    | (``LT.lt, #[type, _, a, b]) =>
        if ← isFloat type then floatPair .ltF "float less than" a b
        else
          unless ← isUInt64 type do throwError "unsupported comparison type in {source}"
          pair .ltU "less than" a b
    | (``LE.le, #[type, _, a, b]) =>
        if ← isFloat type then floatPair .leF "float at most" a b
        else
          unless ← isUInt64 type do throwError "unsupported comparison type in {source}"
          pair .leU "at most" a b
    | (``GT.gt, #[type, _, a, b]) =>
        if ← isFloat type then floatPair .ltF "float greater than" b a
        else
          unless ← isUInt64 type do throwError "unsupported comparison type in {source}"
          pair .ltU "greater than" b a
    | (``GE.ge, #[type, _, a, b]) =>
        if ← isFloat type then floatPair .leF "float at least" b a
        else
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
    | (``OfScientific.ofScientific, #[type, _, .lit (.natVal mantissa), sign, .lit (.natVal exponent)]) =>
        unless ← isFloat type do throwError "unsupported literal type in {source}"
        let negative ← match sign.consumeMData with
          | .const ``Bool.true _ => pure true
          | .const ``Bool.false _ => pure false
          | _ => throwError "unsupported literal: {source}"
        let ir : IRExpr .f64 := .constF (OfScientific.ofScientific mantissa negative exponent : Float).toBits
        return (ir, [hint ir "float literal"])
    | (``OfNat.ofNat, #[type, .lit (.natVal value), _]) =>
        unless ← isFloat type do throwError "unsupported literal type in {source}"
        let ir : IRExpr .f64 := .constF (Float.ofNat value).toBits
        return (ir, [hint ir "float literal"])
    | (``Neg.neg, #[type, _, operand]) =>
        unless ← isFloat type do throwError "unsupported negation type in {source}"
        -- `-x` is `-0.0 - x`, which is exact and yields the canonical NaN for NaN.
        let zero : IRExpr .f64 := .constF 0x8000000000000000
        let (x, xHints) ← translateFloat ctx (loc.skip (exprLength zero)) operand
        let ir : IRExpr .f64 := .binF .sub zero x
        return (ir, hint ir "float neg" :: xHints)
    | (``Float.abs, #[operand]) =>
        let (x, xHints) ← translateFloat ctx loc operand
        let ir : IRExpr .f64 := .unF .abs x
        return (ir, hint ir "float abs" :: xHints)
    | (``Min.min, #[type, _, a, b]) | (``Max.max, #[type, _, a, b]) =>
        unless ← isFloat type do throwError "unsupported min or max type in {source}"
        -- `min a b` is `if a ≤ b then a else b`, and `max a b` is `if a ≤ b then b else a`.
        let isMin := term.isAppOf ``Min.min
        let inner := { ctx with foldable := false }
        let (l, lHints) ← translateFloat inner loc a
        let (r, rHints) ← translateFloat inner (loc.skip (exprLength l)) b
        let condition : IRExpr .bool := .leF l r
        let branch := loc.skip (exprLength condition)
        let (first, second) := if isMin then (a, b) else (b, a)
        let (x, xHints) ← translateFloat inner (branch.inside (some 0)) first
        let (y, yHints) ← translateFloat inner (branch.inside (some 1)) second
        let ir : IRExpr .f64 := .iteF condition x y
        return (ir, hint ir (if isMin then "float min" else "float max") ::
          lHints ++ rHints ++ xHints ++ yHints)
    | (``ite, #[type, condition, _, thenTerm, elseTerm]) =>
        unless ← isFloat type do throwError "unsupported conditional type in {source}"
        let inner := { ctx with foldable := false }
        let (c, cHints) ← translateCondition inner loc condition
        let branch := loc.skip (exprLength c)
        let (a, aHints) ← translateFloat inner (branch.inside (some 0)) thenTerm
        let (b, bHints) ← translateFloat inner (branch.inside (some 1)) elseTerm
        let ir : IRExpr .f64 := .iteF c a b
        return (ir, hint ir "float conditional" :: cHints ++ aHints ++ bHints)
    | (``Float.sqrt, #[operand]) =>
        let (x, xHints) ← translateFloat ctx loc operand
        let ir : IRExpr .f64 := .unF .sqrt x
        return (ir, hint ir "float sqrt" :: xHints)
    | (``Array.foldl, _) =>
        let ir : IRExpr .f64 := .getF (← translateFold ctx term .f64)
        return (ir, [hint ir "fold result"])
    | (``LeanExe.loop, _) =>
        let [(state, .f64)] ← translateLoop ctx term
          | throwError "a loop used as a float must have a float state: {source}"
        let ir : IRExpr .f64 := .getF state
        return (ir, [hint ir "loop result"])
    | (``UInt64.toFloat, #[operand]) =>
        let (x, xHints) ← translateValue ctx loc operand
        let ir : IRExpr .f64 := .convertU x
        return (ir, hint ir "word to float" :: xHints)
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

  /-- Translates a term of type `type`, which is `UInt64` or `Float`. -/
  partial def translateAs (ctx : Ctx) (loc : Loc) (type : ScalarType) (term : Lean.Expr) :
      CompileM ((Σ type, IRExpr type) × List Hint) := do
    match type with
    | .u64 => let (ir, hints) ← translateValue ctx loc term; return (⟨.u64, ir⟩, hints)
    | .f64 => let (ir, hints) ← translateFloat ctx loc term; return (⟨.f64, ir⟩, hints)
    | .bool => throwError "a Bool value is not supported: {← sourceOf term}"

  /-- Translates the fold `term`, whose accumulator has type `accType`, to
  statements in the prelude and returns the local of the accumulator.  An array
  literal becomes a temporary that is released after the fold. -/
  partial def translateFold (ctx : Ctx) (term : Lean.Expr) (accType : ScalarType) :
      CompileM Nat := do
    let source ← sourceOf term
    unless ctx.foldable do
      throwError "a fold may not appear in a branch, a fold body, or a recursive definition: {source}"
    let (``Array.foldl, #[element, acc, f, init, array, start, stop]) := term.getAppFnArgs
      | throwError "unsupported fold: {source}"
    let elementType : ScalarType ← if ← isUInt64 element then pure .u64
      else if ← isFloat element then pure .f64
      else throwError "unsupported fold element type in {source}"
    unless ← (if accType == .f64 then isFloat acc else isUInt64 acc) do
      throwError "unsupported fold accumulator type in {source}"
    unless start.nat? == some 0 do throwError "a fold must start at index 0: {source}"
    match stop.consumeMData.getAppFnArgs with
    | (``Array.size, #[_, sized]) =>
        unless sized.consumeMData == array.consumeMData do
          throwError "a fold must stop at the size of its array: {source}"
    | _ => throwError "a fold must stop at the size of its array: {source}"
    let arrays := if elementType == .f64 then ctx.floatArrays else ctx.arrays
    let (arrayLocal, temporary) ← match arrays.lookup array.consumeMData with
      | some index => pure (index, false)
      | none => do
          let some elements := arrayLiteral? array
            | throwError "a fold must run over an array variable or an array literal: {source}"
          unless elementType == .u64 do
            throwError "a fold over a Float array literal is not supported: {source}"
          pure (← translateArrayLiteral ctx array elements, true)
    let (⟨_, initial⟩, initialHints) ← translateAs ctx ⟨[], 0⟩ accType init
    let before ← get
    let accLocal := before.next
    let (indexLocal, lengthLocal, elementLocal) := (accLocal + 1, accLocal + 2, accLocal + 3)
    let assign : Project.IR.Stmt := .assign accLocal initial
    let foldLoc : Loc := ⟨[], before.length + stmtLength assign⟩
    let bodyLoc := foldBodyLoc foldLoc
      (Stmt.fold elementType arrayLocal accLocal indexLocal lengthLocal elementLocal (.const 0))
    let bind (type : ScalarType) (x : Lean.Expr) (index : Nat) (ctx : Ctx) : Ctx :=
      if type == .f64 then { ctx with floats := (x, index) :: ctx.floats }
      else { ctx with words := (x, index) :: ctx.words }
    let (⟨_, body⟩, bodyHints) ← withLocalDeclD `acc acc fun a =>
      withLocalDeclD `element element fun e =>
        translateAs (bind accType a accLocal <| bind elementType e elementLocal
          { ctx with foldable := false }) bodyLoc accType (mkApp2 f a e).headBeta
    let fold := Stmt.fold elementType arrayLocal accLocal indexLocal lengthLocal elementLocal body
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
      vars := before.vars ++ #[accType, .u64, .u64, elementType]
      names := before.names ++ #[("accumulator", accLocal), ("index", indexLocal),
        ("length", lengthLocal), ("element", elementLocal)] }
    return accLocal

  /-- Removes pattern matches on pairs from `term`, binding each pattern
  variable to the locals of its components, and continues with `k`. -/
  partial def peel {γ : Type} [Inhabited γ] (ctx : Ctx) (term : Lean.Expr)
      (k : Ctx → Lean.Expr → CompileM γ) : CompileM γ := do
    let term := term.consumeMData
    if let some unfolded ← unfoldMatcher? term then
      return ← peel ctx unfolded k
    match term.getAppFnArgs with
    | (``Prod.casesOn, #[first, second, _, pair, alternative]) =>
        let components ← tupleOf ctx pair
        let split := (← stateTypes first).length
        withLocalDeclD `fst first fun a => withLocalDeclD `snd second fun b => do
          peel ((ctx.bind a (components.take split)).bind b (components.drop split))
            (← Core.betaReduce (mkApp2 alternative a b)) k
    | _ => k ctx term

  /-- The locals holding the components of the pair-valued `term`: a pair
  variable, or a loop, whose statements join the prelude. -/
  partial def tupleOf (ctx : Ctx) (term : Lean.Expr) : CompileM (List (Nat × ScalarType)) := do
    let term := term.consumeMData
    if let some components := ctx.tuples.lookup term then return components
    if term.isAppOf ``LeanExe.loop then return ← translateLoop ctx term
    throwError "unsupported pair: {← sourceOf term}"

  /-- Translates `LeanExe.loop n init f` to assignments of `init`'s components to
  fresh state locals and `Stmt.loop`, and returns the state locals. -/
  partial def translateLoop (ctx : Ctx) (term : Lean.Expr) :
      CompileM (List (Nat × ScalarType)) := do
    let source ← sourceOf term
    let (``LeanExe.loop, #[stateType, n, init, f]) := term.getAppFnArgs
      | throwError "unsupported loop: {source}"
    unless ctx.foldable do
      throwError "a loop may not appear in a branch, a fold or loop body, or a recursive definition: {source}"
    let (count, countHints) ← translateValue ctx ⟨[], 0⟩ n
    let initTerms ← stateTerms init stateType
    let mut inits := #[]
    for (component, type) in initTerms do
      inits := inits.push (← translateAs ctx ⟨[], 0⟩ type component, ← sourceOf component)
    let mut state := #[]
    for (_, type) in initTerms do
      state := state.push (← fresh type s!"state {state.size}", type)
    let limit ← fresh .u64 "limit"
    let index ← fresh .u64 "index"
    for (((⟨_, value⟩, hints), componentSource), (local_, _)) in inits.toList.zip state.toList do
      let stmt := Project.IR.Stmt.assign local_ value
      pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "loop start" componentSource :: hints)
    let bodyCtx := { ctx with foldable := false }
    let (bodyStmts, bodyHints) ← withLocalDeclD `i (mkConst ``UInt64) fun i =>
      withLocalDeclD `state stateType fun x =>
        translateLoopBody ((bodyCtx.bind i [(index, .u64)]).bind x state.toList)
          (loopBodyLoc ⟨[], 0⟩ count) (mkApp2 f i x).headBeta state.toList
    let loop := Stmt.loop limit index count (seqAll bodyStmts)
    pushStmt loop (mkHint ⟨[], 0⟩ (stmtLength loop) "loop" source :: countHints ++ bodyHints)
    return state.toList

  /-- Translates a loop body, which computes the next state, to statements that
  bind its `have` variables to fresh locals, evaluate the next state's
  components into fresh temporaries, and copy them to the state locals. -/
  partial def translateLoopBody (ctx : Ctx) (loc : Loc) (term : Lean.Expr)
      (state : List (Nat × ScalarType)) : CompileM (List Project.IR.Stmt × List Hint) :=
    peel ctx term fun ctx term => do
      match term with
      | .letE name type value body _ =>
          let scalar ← scalarTypeOf type
          let (⟨_, v⟩, vHints) ← translateAs ctx loc scalar value
          let local_ ← fresh scalar name.toString
          let stmt := Project.IR.Stmt.assign local_ v
          let hint := mkHint loc (stmtLength stmt) "let" (← sourceOf value)
          withLocalDeclD name type fun x => do
            let (rest, restHints) ← translateLoopBody (ctx.bind x [(local_, scalar)])
              (loc.skip (stmtLength stmt)) (body.instantiate1 x) state
            return (stmt :: rest, hint :: vHints ++ restHints)
      | _ =>
          let components ← stateTerms term (← inferType term)
          let mut stmts := #[]
          let mut hints := #[]
          let mut temps := #[]
          let mut here := loc
          for (component, type) in components do
            let (⟨_, v⟩, vHints) ← translateAs ctx here type component
            let temp ← fresh type "next state"
            let stmt := Project.IR.Stmt.assign temp v
            hints := hints ++ (mkHint here (stmtLength stmt) "next state" (← sourceOf component) ::
              vHints).toArray
            stmts := stmts.push stmt
            temps := temps.push (temp, type)
            here := here.skip (stmtLength stmt)
          for ((temp, type), (local_, _)) in temps.toList.zip state do
            let stmt : Project.IR.Stmt := match type with
              | .f64 => .assign local_ (.getF temp)
              | _ => .assign local_ (.get temp)
            hints := hints.push (mkHint here (stmtLength stmt) "state copy" "state")
            stmts := stmts.push stmt
            here := here.skip (stmtLength stmt)
          return (stmts.toList, hints.toList)

  /-- Pushes the copying template for an array of `count` elements whose element
  is `element`, a function of the index local, and returns the new array's local. -/
  partial def emitBuild (ctx : Ctx) (source rule : String) (count : IRExpr .u64)
      (countHints : List Hint) (element : Nat → Loc → CompileM (IRExpr .u64 × List Hint)) :
      CompileM Nat := do
    let dst ← fresh .u64 "array"
    let limit ← fresh .u64 "limit"
    let index ← fresh .u64 "index"
    let (elementIR, elementHints) ← element index (buildElementLoc ⟨[], 0⟩ dst limit index count)
    let stmt := Stmt.build dst limit index count elementIR
    pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) rule source :: countHints ++ elementHints)
    return dst

  /-- Translates an `Array UInt64` term to statements that leave a new array, which
  the caller owns, in a fresh local, and returns the local: an array literal,
  `set!` on an array variable, `LeanExe.build`, or an array variable, which is
  copied. -/
  partial def translateArray (ctx : Ctx) (term : Lean.Expr) : CompileM Nat := do
    let term := term.consumeMData
    let source ← sourceOf term
    unless ctx.foldable do
      throwError "an array may not be built in a branch, a fold or loop body, or a recursive definition: {source}"
    if let some elements := arrayLiteral? term then
      return ← translateArrayLiteral ctx term elements
    let sizeOf (arrayLocal : Nat) : CompileM Nat := do
      let size ← fresh .u64 "size"
      let stmt := Stmt.arraySize size arrayLocal
      pushStmt stmt [mkHint ⟨[], 0⟩ (stmtLength stmt) "array-size" source]
      return size
    if let some arrayLocal := ctx.arrays.lookup term then
      let size ← sizeOf arrayLocal
      return ← emitBuild ctx source "array copy" (.get size) [] fun index loc =>
        let ir : IRExpr .u64 := .read arrayLocal (.get index)
        return (ir, [mkHint loc (exprLength ir) "array read" source])
    match term.getAppFnArgs with
    | (``Array.set!, #[element, array, position, value])
    | (``Array.setIfInBounds, #[element, array, position, value]) =>
        unless ← isUInt64 element do throwError "unsupported array element type in {source}"
        let some arrayLocal := ctx.arrays.lookup array.consumeMData
          | throwError "`set!` must be applied to an array variable: {source}"
        let (``UInt64.toNat, #[k]) := position.consumeMData.getAppFnArgs
          | throwError "a `set!` position must be `i.toNat` for a UInt64 `i`: {source}"
        let (kIR, kHints) ← translateValue ctx ⟨[], 0⟩ k
        let kLocal ← fresh .u64 "set position"
        let kStmt := Project.IR.Stmt.assign kLocal kIR
        pushStmt kStmt (mkHint ⟨[], 0⟩ (stmtLength kStmt) "set position" (← sourceOf k) :: kHints)
        let (vIR, vHints) ← translateValue ctx ⟨[], 0⟩ value
        let vLocal ← fresh .u64 "set value"
        let vStmt := Project.IR.Stmt.assign vLocal vIR
        pushStmt vStmt (mkHint ⟨[], 0⟩ (stmtLength vStmt) "set value" (← sourceOf value) :: vHints)
        let size ← sizeOf arrayLocal
        emitBuild ctx source "array set" (.get size) [] fun index loc =>
          let ir : IRExpr .u64 :=
            .ite (.eq (.get index) (.get kLocal)) (.get vLocal) (.read arrayLocal (.get index))
          return (ir, [mkHint loc (exprLength ir) "set element" source])
    | (``Array.insertIdx!, #[element, array, position, value]) =>
        unless ← isUInt64 element do throwError "unsupported array element type in {source}"
        let some arrayLocal := ctx.arrays.lookup array.consumeMData
          | throwError "`insertIdx!` must be applied to an array variable: {source}"
        let (``UInt64.toNat, #[k]) := position.consumeMData.getAppFnArgs
          | throwError "an `insertIdx!` position must be `i.toNat` for a UInt64 `i`: {source}"
        let (kIR, kHints) ← translateValue ctx ⟨[], 0⟩ k
        let kLocal ← fresh .u64 "insert position"
        let kStmt := Project.IR.Stmt.assign kLocal kIR
        pushStmt kStmt (mkHint ⟨[], 0⟩ (stmtLength kStmt) "insert position" (← sourceOf k) :: kHints)
        let (vIR, vHints) ← translateValue ctx ⟨[], 0⟩ value
        let vLocal ← fresh .u64 "insert value"
        let vStmt := Project.IR.Stmt.assign vLocal vIR
        pushStmt vStmt (mkHint ⟨[], 0⟩ (stmtLength vStmt) "insert value" (← sourceOf value) :: vHints)
        let size ← sizeOf arrayLocal
        -- `insertIdx!` past the end panics and returns the empty array.
        let count : IRExpr .u64 :=
          .ite (.leU (.get kLocal) (.get size)) (.bin .add (.get size) (.const 1)) (.const 0)
        emitBuild ctx source "array insert" count [] fun index loc =>
          let ir : IRExpr .u64 :=
            .ite (.ltU (.get index) (.get kLocal)) (.read arrayLocal (.get index))
              (.ite (.eq (.get index) (.get kLocal)) (.get vLocal)
                (.read arrayLocal (.bin .sub (.get index) (.const 1))))
          return (ir, [mkHint loc (exprLength ir) "insert element" source])
    | (``LeanExe.build, #[element, count, f]) =>
        unless ← isUInt64 element do throwError "unsupported array element type in {source}"
        let (countIR, countHints) ← translateValue ctx ⟨[], 0⟩ count
        emitBuild ctx source "array build" countIR countHints fun index loc =>
          withLocalDeclD `i (mkConst ``UInt64) fun i =>
            translateValue ({ ctx with foldable := false }.bind i [(index, .u64)]) loc
              (mkApp f i).headBeta
    | _ => throwError "unsupported array: {source}"

  /-- Translates a result term of type `type` to one result expression per
  component, each with hints relative to its own code: a pair gives the results of
  its components, an array a new array's pointer, and a scalar its value. -/
  partial def translateResults (ctx : Ctx) (term type : Lean.Expr) :
      CompileM (List (Σ type, IRExpr type) × List (List Hint)) :=
    peel ctx term fun ctx term => do
      let type ← whnfR type
      if let .letE name letType value body _ := term then
        let scalar ← scalarTypeOf letType
        let (⟨_, v⟩, vHints) ← translateAs ctx ⟨[], 0⟩ scalar value
        let local_ ← fresh scalar name.toString
        let stmt := Project.IR.Stmt.assign local_ v
        pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "let" (← sourceOf value) :: vHints)
        return ← withLocalDeclD name letType fun x =>
          translateResults (ctx.bind x [(local_, scalar)]) (body.instantiate1 x) type
      let branching := type.isAppOfArity ``Prod 2 || (← isUInt64Array type)
      if let (``ite, #[_, condition, _, thenTerm, elseTerm]) := term.getAppFnArgs then
        if branching then
          return ← translateResultBranch ctx term condition thenTerm elseTerm type
      if type.isAppOfArity ``Prod 2 then
        let (``Prod.mk, #[first, second, a, b]) := term.getAppFnArgs
          | throwError "a pair result must be a pair: {← sourceOf term}"
        let (aResults, aHints) ← translateResults ctx a first
        let (bResults, bHints) ← translateResults ctx b second
        return (aResults ++ bResults, aHints ++ bHints)
      if ← isUInt64Array type then
        let array ← translateArray ctx term
        let ir : IRExpr .u64 := .get array
        return ([⟨.u64, ir⟩], [[mkHint ⟨[], 0⟩ (exprLength ir) "array result" (← sourceOf term)]])
      let (result, hints) ← translateAs ctx ⟨[], 0⟩ (← scalarTypeOf type) term
      return ([result], [hints])

  /-- Translates a conditional result whose branches build arrays to a statement
  `if` whose branches leave the results in fresh locals, and returns the locals. -/
  partial def translateResultBranch (ctx : Ctx) (term condition thenTerm elseTerm type : Lean.Expr) :
      CompileM (List (Σ type, IRExpr type) × List (List Hint)) := do
    let source ← sourceOf term
    let (c, cHints) ← translateCondition ctx ⟨[], 0⟩ condition
    let branch (resultTerm : Lean.Expr) (locals : List (Nat × ScalarType)) :
        CompileM (List (Nat × ScalarType)) := do
      let (results, hints) ← translateResults ctx resultTerm type
      let mut locals := locals
      let mut out := #[]
      for (⟨resultType, ir⟩, own) in results.zip hints do
        let (local_, rest) ← match locals with
          | first :: rest => pure (first.1, rest)
          | [] => do pure (← fresh resultType "result", [])
        locals := rest
        let stmt := Project.IR.Stmt.assign local_ ir
        pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "result" (← sourceOf resultTerm) :: own)
        out := out.push (local_, resultType)
      return out.toList
    let (resultLocals, thenStmts, thenHints) ← withBlock (branch thenTerm [])
    let (_, elseStmts, elseHints) ← withBlock (branch elseTerm resultLocals)
    let stmt := Project.IR.Stmt.ite c (seqAll thenStmts) (seqAll elseStmts)
    let branchAt := exprLength c
    pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "result branch" source :: cHints ++
      thenHints.map (Hint.within [branchAt, 0]) ++ elseHints.map (Hint.within [branchAt, 1]))
    return (resultLocals.map fun (local_, resultType) => match resultType with
        | .f64 => (⟨.f64, .getF local_⟩ : Σ type, IRExpr type)
        | _ => ⟨.u64, .get local_⟩,
      resultLocals.map fun _ => [])

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
      vars := before.vars.push .u64
      names := before.names.push ("array", temp) }
    return temp
end

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

/-- Compiles the definition `declName`, whose parameters are `UInt64`, `Float`,
`Array UInt64`, or `Array Float` and whose result is `UInt64`, `Float`, or an
`Array UInt64` literal, to an IR function with hints.  The
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
    let mut floatArrays := []
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
      else if ← isFloatArray type then
        floatArrays := (params[i], i) :: floatArrays
        paramTypes := paramTypes.push .u64
      else
        throwError "parameter {params[i]} of {declName} is not UInt64, Float, Array UInt64, or Array Float"
    let resultType ← inferType body
    let arrayResult ← isUInt64Array resultType
    let floatResult ← isFloat resultType
    let pairResult := (← whnfR resultType).isAppOfArity ``Prod 2
    unless arrayResult || floatResult || pairResult || (← isUInt64 resultType) do
      throwError "the result of {declName} is not UInt64, Float, Array UInt64, or a pair"
    let paramNames ← params.toList.mapM fun p => return (← p.fvarId!.getUserName).toString
    let recursive := (body.find? fun e => e.isConstOf declName).isSome
    if recursive then
      unless arrays.isEmpty && floatArrays.isEmpty && floats.isEmpty && !arrayResult &&
          !floatResult && !pairResult do
        throwError "a recursive definition may take and return only UInt64: {declName}"
      let ctx : Ctx :=
        { self := declName, params, words, floats, arrays, floatArrays, foldable := false }
      -- The loop is the first instruction of the body: a block holding a loop.
      let loopBody := ((({ prefix_ := [], index := 0 } : Loc).inside none).inside none)
      let condition : IRExpr .bool := .eq (.get ctx.done) (.const 0)
      let (step, stepHints) ← (translateTail ctx
        (loopBody.skip (exprLength condition + 2)) body).run' { base := ctx.vars }
      let loop : Project.IR.Stmt := .while condition step
      let loopHint := mkHint { prefix_ := [], index := 0 } (stmtLength loop)
        "tail-recursion-loop" (← sourceOf body)
      let resultHint := mkHint { prefix_ := [], index := 1 } 1 "result" "result"
      let names := paramNames.zipIdx ++
        [("result", ctx.result), ("done", ctx.done)] ++
        (paramNames.zipIdx.map fun (name, i) => (s!"next {name}", ctx.temp i))
      let func : Func :=
        { params := paramTypes.toList, vars := List.replicate ctx.vars .u64, body := loop
          results := [⟨.u64, .get ctx.result⟩] }
      return (func, { locals := names, nodes := loopHint :: stepHints ++ [resultHint] })
    else
      let ctx : Ctx :=
        { self := declName, params, words, floats, arrays, floatArrays, foldable := true }
      let ((results, resultHints), prelude) ←
        (translateResults ctx body resultType).run { base := params.size }
      -- Each result's code follows the body and the earlier results.
      let (_, shifted) := (results.zip resultHints).foldl (init := (prelude.length, []))
        fun (offset, hints) (⟨_, ir⟩, own) =>
          (offset + exprLength ir, hints ++ own.map (Hint.shift offset))
      let func : Func :=
        { params := paramTypes.toList, vars := prelude.vars.toList
          body := seqAll prelude.stmts.toList, results }
      let hints : Hints :=
        { locals := paramNames.zipIdx ++ prelude.names.toList
          nodes := prelude.hints.toList ++ shifted }
      return (func, hints)

deriving instance ToExpr for U64Op
deriving instance ToExpr for F64Op
deriving instance ToExpr for F64UnOp
deriving instance ToExpr for ScalarType

/-- The Lean term for an IR expression, for the definitions the command adds. -/
def irToExpr : {type : ScalarType} → IRExpr type → Lean.Expr
  | _, .get index => mkApp (mkConst ``Project.IR.Expr.get) (toExpr index)
  | _, .getF index => mkApp (mkConst ``Project.IR.Expr.getF) (toExpr index)
  | _, .binF op left right =>
      mkApp3 (mkConst ``Project.IR.Expr.binF) (toExpr op) (irToExpr left) (irToExpr right)
  | _, .unF op operand => mkApp2 (mkConst ``Project.IR.Expr.unF) (toExpr op) (irToExpr operand)
  | _, .convertU operand => mkApp (mkConst ``Project.IR.Expr.convertU) (irToExpr operand)
  | _, .truncSatU operand => mkApp (mkConst ``Project.IR.Expr.truncSatU) (irToExpr operand)
  | _, .read array position =>
      mkApp2 (mkConst ``Project.IR.Expr.read) (toExpr array) (irToExpr position)
  | _, .constF bits => mkApp (mkConst ``Project.IR.Expr.constF) (toExpr bits)
  | _, .iteF condition thenValue elseValue =>
      mkApp3 (mkConst ``Project.IR.Expr.iteF) (irToExpr condition) (irToExpr thenValue)
        (irToExpr elseValue)
  | _, .eqF left right => mkApp2 (mkConst ``Project.IR.Expr.eqF) (irToExpr left) (irToExpr right)
  | _, .ltF left right => mkApp2 (mkConst ``Project.IR.Expr.ltF) (irToExpr left) (irToExpr right)
  | _, .leF left right => mkApp2 (mkConst ``Project.IR.Expr.leF) (irToExpr left) (irToExpr right)
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
  | .assign (type := type) index value =>
      mkApp3 (mkConst ``Project.IR.Stmt.assign) (toExpr type) (toExpr index) (irToExpr value)
  | .seq first second => mkApp2 (mkConst ``Project.IR.Stmt.seq) (stmtToExpr first) (stmtToExpr second)
  | .ite condition thenStmt elseStmt =>
      mkApp3 (mkConst ``Project.IR.Stmt.ite) (irToExpr condition) (stmtToExpr thenStmt)
        (stmtToExpr elseStmt)
  | .while condition body =>
      mkApp2 (mkConst ``Project.IR.Stmt.while) (irToExpr condition) (stmtToExpr body)
  | .load type index address =>
      mkApp3 (mkConst ``Project.IR.Stmt.load) (toExpr type) (toExpr index) (irToExpr address)
  | .store address value =>
      mkApp2 (mkConst ``Project.IR.Stmt.store) (irToExpr address) (irToExpr value)
  | .call func args result =>
      mkApp3 (mkConst ``Project.IR.Stmt.call) (toExpr func)
        (let type := mkApp (mkConst ``Project.IR.Expr) (mkConst ``Project.IR.ScalarType.u64)
         args.foldr (fun arg list => mkApp3 (mkConst ``List.cons [Level.zero]) type (irToExpr arg) list)
           (mkApp (mkConst ``List.nil [Level.zero]) type))
        (toExpr result)

def funcToExpr (func : Func) : Lean.Expr :=
  let resultType := mkApp2 (mkConst ``Sigma [Level.zero, Level.zero]) (mkConst ``ScalarType)
    (mkConst ``Project.IR.Expr)
  let results := func.results.foldr (init := mkApp (mkConst ``List.nil [Level.zero]) resultType)
    fun result list => mkApp3 (mkConst ``List.cons [Level.zero]) resultType
      (mkApp4 (mkConst ``Sigma.mk [Level.zero, Level.zero]) (mkConst ``ScalarType)
        (mkConst ``Project.IR.Expr) (toExpr result.1) (irToExpr result.2)) list
  mkApp4 (mkConst ``Func.mk) (toExpr func.params) (toExpr func.vars) (stmtToExpr func.body) results

end Project.Compiler
