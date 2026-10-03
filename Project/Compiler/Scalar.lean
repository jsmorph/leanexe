import Lean
import Project.IR.ArrayLiteral
import Project.IR.Fold
import Project.IR.ListFold
import Project.IR.Record
import Project.IR.Release
import Project.IR.Function
import Project.IR.Loop
import Project.IR.Append
import Project.IR.Build
import Project.IR.Update
import Project.IR.ArrayLoop
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

def isUInt64List (type : Lean.Expr) : MetaM Bool := do
  let type ← whnfR type
  if type.isAppOfArity ``List 1 then isUInt64 type.appArg! else return false

/-- Whether `type` is `Array UInt64` or `Array Float`, both a pointer word. -/
def isArray (type : Lean.Expr) : MetaM Bool := do
  return (← isUInt64Array type) || (← isFloatArray type)

/-- The number of instructions in the code of an expression or a statement.  It
does not depend on the scratch index. -/
def exprLength (e : IRExpr type) : Nat := (e.program 0).length
def stmtLength (s : Project.IR.Stmt) : Nat := (s.program 0).length

/-- The most values a recursive internal function may hold in its frame: parameters, locals,
and scratch.  With the depth limit of 1,000, every accepted frame overflows Wasmtime's default
512 KiB stack only beyond 2,000 calls, measured on aarch64 with Wasmtime 44. -/
def recursiveFrameLimit : Nat := 24

/-- The functions that `s` calls. -/
def callsOf : Project.IR.Stmt → List Nat
  | .seq first second => callsOf first ++ callsOf second
  | .ite _ thenStmt elseStmt => callsOf thenStmt ++ callsOf elseStmt
  | .while _ body => callsOf body
  | .call func _ _ => [func]
  | _ => []

/-- Whether a recursive body may call `func`, which carries no depth: it calls only the
runtime's `alloc` and `release` and holds at most `recursiveFrameLimit` values, so it adds one
bounded frame on top of the recursion. -/
def isLeaf (func : Project.IR.Func) : Bool :=
  (callsOf func.body).all (· < 2) &&
    func.params.length + func.vars.length + func.width ≤ recursiveFrameLimit

/-- The compiler's view of the definition being compiled.  `words`, `floats`,
`arrays`, `floatArrays`, and `lists` give the local of each `UInt64`, `Float`,
`Array UInt64`, `Array Float`, and `List UInt64` variable in scope, `tuples` gives the
locals of each pair-valued variable's components, and `callees` gives the
function index of each definition compiled into the same module.  A recursive definition's
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
  lists : List (Lean.Expr × Nat) := []
  /-- The local of each variable of a recursive user type in scope, a borrowed pointer. -/
  nodes : List (Lean.Expr × Nat) := []
  /-- In the internal function of a recursive definition that is not tail recursive: the
  function's index and the local of its depth parameter. -/
  selfCall : Option (Nat × Nat) := none
  tuples : List (Lean.Expr × List (Nat × ScalarType)) := []
  callees : List (Name × Nat) := []
  /-- The internal function of each recursive callee, which a call from a recursive body
  enters at the caller's depth plus one. -/
  internals : List (Name × Nat) := []
  /-- The non-recursive callees that a recursive body may call: those that call no compiled
  function and hold at most `recursiveFrameLimit` values in their frame. -/
  leaves : List Name := []
  foldable : Bool
  /-- Whether code may allocate or call: false inside an element of
  `LeanExe.build`, whose statements must keep the store. -/
  allocating : Bool := true
  /-- Whether calls with scalar arguments and results may appear where code must
  keep the store: true in loop bodies and elements of `LeanExe.build`. -/
  pureCalls : Bool := false
  /-- Whether such a call may also lend a value of a recursive type: true in loop bodies. -/
  lendsTrees : Bool := false
  /-- Whether a `let` may bind an array: true at the top of a function body, false
  in a branch, since the array is released at the end of the function. -/
  temporaries : Bool := true
  /-- The positions of the owned parameters of each definition in `callees`. -/
  owners : List (Name × List Nat) := []
  /-- The array parameters that this code may move: those whose last use, in the
  result term, is the left operand of `++` or an owned parameter of a callee.  Also the owned
  values of recursive types: parameters that the result moves, and the children of an owned
  record that a match examines. -/
  owned : List Lean.Expr := []
  /-- In the record branch of a match on an owned value of a recursive type: the value, the
  local of its pointer, and the field variables.  A constructor of the same type rewrites the
  record in place. -/
  reuse : Option (Lean.Expr × Nat × List Lean.Expr) := none

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

/-- The start of the body's code in an array or list fold whose code starts at `loc`:
inside the block and loop of the `while`, after the condition, the exit test, and the
element load. -/
def foldBodyLoc (loc : Loc) : Project.IR.Stmt → Loc
  | .seq first (.seq second (.while condition (.seq load _))) =>
      (((loc.skip (stmtLength first + stmtLength second)).inside none).inside none).skip
        (exprLength condition + 2 + stmtLength load)
  | .seq first (.while condition (.seq load _)) =>
      (((loc.skip (stmtLength first)).inside none).inside none).skip
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
  /-- The variables and locals of the temporary arrays, with their sources.  The end of the
  function releases those that the code has not moved. -/
  temporaries : Array (Lean.Expr × Nat × String) := #[]
  /-- The owned parameters that the code has moved on the current path. -/
  consumed : List Lean.Expr := []
  /-- The matched owned values whose records a constructor has rewritten on the current path. -/
  rebuilt : List Lean.Expr := []
  /-- The arrays that already translated parts of a value read.  Those parts run after the
  statements of the parts translated now, which therefore may not move these arrays. -/
  pendingReads : List Lean.Expr := []

/-- The next free local. -/
def Prelude.next (p : Prelude) : Nat := p.base + p.vars.size

abbrev CompileM := StateT Prelude MetaM

/-- `stmts` in sequence, with the code of each placed after the previous. -/
def seqAll : List Project.IR.Stmt → Project.IR.Stmt
  | [] => .skip
  | [s] => s
  | s :: rest => .seq s (seqAll rest)

/-- The user types the compiler accepts: an enumeration, held as the word of its constructor
index; a structure, held as its fields' components in order; and a sum, held as the word of
its constructor index followed by every constructor's fields, in order. -/
inductive UserType where
  | enum (ctors : List Name)
  | struct (ctor : Name) (fields : List Lean.Expr)
  | sum (ctors : List (Name × List Lean.Expr))
  | recursive (ctors : List (Name × List Lean.Expr))

/-- `type` as a user type: an inductive type without parameters or indices that is an
enumeration, whose constructors have no fields, a structure, or a sum, or a recursive type
that is neither nested nor mutual, whose values are records on the heap. -/
def userType? (type : Lean.Expr) : MetaM (Option UserType) := do
  let .const name _ ← whnfR type | return none
  if name == ``UInt64 || name == ``Float then return none
  let some (.inductInfo info) := (← getEnv).find? name | return none
  unless info.numParams == 0 && info.numIndices == 0 do return none
  let fields ← info.ctors.mapM fun ctor => do
    forallTelescope (← getConstInfoCtor ctor).type fun xs _ => xs.toList.mapM inferType
  if info.isRec then
    unless info.numNested == 0 && info.all.length == 1 do return none
    return some (.recursive (info.ctors.zip fields))
  if fields.all (·.isEmpty) then return some (.enum info.ctors)
  if let [ctor] := info.ctors then
    if isStructure (← getEnv) name then return some (.struct ctor fields[0]!)
    return none
  return some (.sum (info.ctors.zip fields))

/-- Whether `type` is a recursive user type, whose values are pointers to records. -/
def isNodeType (type : Lean.Expr) : MetaM Bool :=
  return (← userType? type) matches some (.recursive _)

/-- Whether `type` is `UInt64` or an enumeration, held as one word. -/
def isWordType (type : Lean.Expr) : MetaM Bool := do
  if ← isUInt64 type then return true
  return (← userType? type) matches some (.enum _)

/-- Whether `name` is the constructor without fields of a recursive type, the null pointer. -/
def isNullCtor (name : Name) : MetaM Bool := do
  let some (.ctorInfo info) := (← getEnv).find? name | return false
  unless info.numFields == 0 do return false
  return (← userType? (.const info.induct [])) matches some (.recursive _)

/-- The fields of `term`, a list cell `x :: xs` of words or a constructor application with
fields of a recursive type whose other constructor has none, with the child mask of its
record: bit `i` is set when field `i` is a value of a recursive type.  A type with more than
one constructor with fields needs a tag, which is not supported yet. -/
def recordCell? (term : Lean.Expr) : MetaM (Option (List Lean.Expr × UInt64)) := do
  let term := term.consumeMData
  if let (``List.cons, #[element, head, tail]) := term.getAppFnArgs then
    unless ← isUInt64 element do return none
    return some ([head, tail], 2)
  let .const name _ := term.getAppFn | return none
  let some (.ctorInfo info) := (← getEnv).find? name | return none
  let some (.recursive ctors) ← userType? (.const info.induct []) | return none
  let some (_, fields) := ctors.find? (·.1 == name) | return none
  unless !fields.isEmpty && term.getAppNumArgs == fields.length do return none
  unless ctors.length == 2 && (ctors.filter (!·.2.isEmpty)).length == 1 do
    throwError "a recursive type must have one constructor without fields and one with fields: {info.induct}"
  let mut mask : Nat := 0
  for h : i in [:fields.length] do
    if ← isNodeType fields[i] then
      mask := mask + 2 ^ i
    else unless ← isWordType fields[i] do
      throwError "a field of a record built by the compiler must be a word or a value of a recursive type: {fields[i]}"
  return some (term.getAppArgs.toList, UInt64.ofNat mask)

/-- Whether `type` is a pair, a structure, or a sum, whose values have several components. -/
def isTupleType (type : Lean.Expr) : MetaM Bool := do
  let type ← whnfR type
  if type.isAppOfArity ``Prod 2 then return true
  match ← userType? type with
  | some (.struct ..) | some (.sum _) => return true
  | _ => return false

/-- The index of the enumeration constructor `name`. -/
def enumIndex? (name : Name) : MetaM (Option Nat) := do
  let some (.ctorInfo info) := (← getEnv).find? name | return none
  let some (.enum _) ← userType? (.const info.induct []) | return none
  return some info.cidx

/-- The scalar type of a `UInt64`, `Float`, or enumeration type. -/
def scalarTypeOf (type : Lean.Expr) : MetaM ScalarType := do
  if ← isUInt64 type then return .u64
  if ← isFloat type then return .f64
  if (← userType? type) matches some (.enum _) then return .u64
  throwError "unsupported type {type}"

/-- The WebAssembly value types of a value of type `type`: a word for `UInt64`, for an
enumeration, and, when `arrays`, for an array or list pointer; a float for `Float`; the components of
each side of a pair and of each field of a structure, in order; and for a sum, a word for the
constructor index followed by the components of every constructor's fields.  The fields of a
structure or sum may not be arrays. -/
partial def componentTypes (type : Lean.Expr) (arrays : Bool) : MetaM (List ScalarType) := do
  let type ← whnfR type
  if type.isAppOfArity ``Prod 2 then
    return (← componentTypes type.appFn!.appArg! arrays) ++ (← componentTypes type.appArg! arrays)
  if arrays && ((← isArray type) || (← isUInt64List type) || (← isNodeType type)) then
    return [.u64]
  match ← userType? type with
  | some (.struct _ fields) => return (← fields.mapM fun field => componentTypes field false).flatten
  | some (.sum ctors) =>
      return .u64 :: (← ctors.mapM fun (_, fields) => return (← fields.mapM fun field =>
        componentTypes field false).flatten).flatten
  | _ => return [← scalarTypeOf type]

/-- The components of a loop state: words and floats. -/
def stateTypes (type : Lean.Expr) : MetaM (List ScalarType) := componentTypes type false

/-- The zero of the field type `type`, held in the slots of a sum's inactive constructors:
0 for a word or float, and the first constructor of an enumeration. -/
def zeroOf (type : Lean.Expr) : MetaM Lean.Expr := do
  if (← isUInt64 type) || (← isFloat type) then return ← mkNumeral type 0
  if let some (.enum (ctor :: _)) ← userType? type then return mkConst ctor
  throwError "a field of a sum must be a word, a float, or an enumeration: {type}"

/-- The parts of `term`, a constructor application of the pair, structure, or sum type
`type`, with their types.  The parts of a sum's constructor are its index, then each
constructor's fields: the applied constructor's arguments, and zeros for the others. -/
def constructorParts? (term type : Lean.Expr) : MetaM (Option (List (Lean.Expr × Lean.Expr))) := do
  let type ← whnfR type
  let term := term.consumeMData
  if type.isAppOfArity ``Prod 2 then
    let (``Prod.mk, #[first, second, a, b]) := term.getAppFnArgs | return none
    return some [(a, first), (b, second)]
  match ← userType? type with
  | some (.struct ctor fields) =>
      unless term.isAppOfArity ctor fields.length do return none
      return some (term.getAppArgs.toList.zip fields)
  | some (.sum ctors) =>
      let some index := ctors.findIdx? fun (ctor, fields) => term.isAppOfArity ctor fields.length
        | return none
      let word := mkConst ``UInt64
      let mut parts := [(← mkNumeral word index, word)]
      for h : i in [:ctors.length] do
        let fields := ctors[i].2
        if i == index then
          parts := parts ++ term.getAppArgs.toList.zip fields
        else
          parts := parts ++ (← fields.mapM fun field => return (← zeroOf field, field))
      return some parts
  | _ => return none

/-- The component terms of `term`, a nest of constructor applications of type `type`. -/
partial def stateTerms (term type : Lean.Expr) : MetaM (List (Lean.Expr × ScalarType)) := do
  if (← isUInt64List type) || (← isNodeType type) then return [(term, .u64)]
  if ← isTupleType type then
    let some parts ← constructorParts? term type
      | throwError "a loop state must be a tuple of components: {← sourceOf term}"
    return (← parts.mapM fun (part, partType) => stateTerms part partType).flatten
  return [(term, ← scalarTypeOf type)]

instance : Inhabited (Σ type, IRExpr type) := ⟨⟨.u64, .const 0⟩⟩

/-- The WebAssembly value types of a result's components, array pointers included. -/
def resultTypes (type : Lean.Expr) : MetaM (List ScalarType) := componentTypes type true

/-- `term` with every redex at its head reduced, including those that a reduction exposes. -/
partial def headBetaAll (term : Lean.Expr) : Lean.Expr :=
  if term.isHeadBetaTarget then headBetaAll term.headBeta else term

/-- Whether the sparse case split `name`, which Lean generates for a match with a wildcard,
is an auxiliary `_sparseCasesOn` definition. -/
def isSparseCasesOn : Name → Bool
  | .str _ s => s.startsWith "_sparseCasesOn"
  | _ => false

/-- An alternative of a case split: the field types of its constructor, and the function
that takes the fields and then the further arguments `extra`. -/
structure CaseAlt where
  fields : List Lean.Expr
  fn : Lean.Expr
  extra : Array Lean.Expr

/-- The alternative's body for the field variables `xs`. -/
def CaseAlt.body (alt : CaseAlt) (xs : List Lean.Expr) : Lean.Expr :=
  headBetaAll (mkAppN alt.fn (xs.toArray ++ alt.extra))

/-- The discriminant and the alternatives, one per constructor in order, of a case split on
an enumeration or a sum: `T.casesOn`, `T.rec` applied to further arguments, or an auxiliary
`_sparseCasesOn` definition, which unfolds to `T.rec`. -/
partial def userCases? (term : Lean.Expr) : MetaM (Option (Lean.Expr × List CaseAlt)) := do
  let term := headBetaAll term.consumeMData
  let .const name _ := term.getAppFn | return none
  let args := term.getAppArgs
  if isSparseCasesOn name then
    let some unfolded ← unfoldDefinition? term | return none
    return ← userCases? unfolded
  let .str induct kind := name | return none
  unless kind == "casesOn" || kind == "rec" do return none
  let ctorFields ← match ← userType? (.const induct []) with
    | some (.enum ctors) => pure (ctors.map fun _ => [])
    | some (.sum ctors) => pure (ctors.map (·.2))
    -- The alternatives of `rec` on a recursive type also take induction hypotheses.
    | some (.recursive ctors) =>
        unless kind == "casesOn" do return none
        pure (ctors.map (·.2))
    | _ => return none
  let n := ctorFields.length
  if kind == "casesOn" && args.size == 2 + n then
    return some (args[1]!, ((args.extract 2 args.size).toList.zip ctorFields).map
      fun (alt, fields) => ⟨fields, alt, #[]⟩)
  if kind == "rec" && args.size ≥ 2 + n then
    let extra := args.extract (2 + n) args.size
    return some (args[1 + n]!, ((args.extract 1 (1 + n)).toList.zip ctorFields).map
      fun (minor, fields) => ⟨fields, minor, extra⟩)
  return none

/-- The field types and the alternative of a `casesOn` on a pair or a structure, with its
discriminant. -/
def tupleCases? (term : Lean.Expr) : MetaM (Option (Lean.Expr × List Lean.Expr × Lean.Expr)) := do
  match term.getAppFnArgs with
  | (``Prod.casesOn, #[first, second, _, pair, alternative]) =>
      return some (pair, [first, second], alternative)
  | (.str induct "casesOn", #[_, value, alternative]) =>
      let some (.struct _ fields) ← userType? (.const induct []) | return none
      return some (value, fields, alternative)
  | _ => return none

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

/-- Binds `x`, of type `type`, to the locals `components`: an array to its one local, and
any other value as `Ctx.bind` does. -/
def Ctx.bindTyped (ctx : Ctx) (x type : Lean.Expr) (components : List (Nat × ScalarType)) :
    MetaM Ctx := do
  if ← isUInt64Array type then
    let [(index, _)] := components | throwError "an array takes one local"
    return { ctx with arrays := (x, index) :: ctx.arrays }
  if ← isFloatArray type then
    let [(index, _)] := components | throwError "an array takes one local"
    return { ctx with floatArrays := (x, index) :: ctx.floatArrays }
  if (← isNodeType type) || (← isUInt64List type) then
    let [(index, _)] := components | throwError "a value with records takes one local"
    return { ctx with nodes := (x, index) :: ctx.nodes }
  return ctx.bind x components

/-- Whether `type` is a nest of at least two word arrays, `Array UInt64 × (… × Array UInt64)`. -/
partial def isArrayNest (type : Lean.Expr) : MetaM Bool := do
  let type ← whnfR type
  unless type.isAppOfArity ``Prod 2 do return false
  unless ← isUInt64Array type.appFn!.appArg! do return false
  if ← isUInt64Array type.appArg! then return true
  isArrayNest type.appArg!

/-- The components of `term`, a nest of `Prod.mk` of the nest type `type`, or `none` when
`term` is not such a nest. -/
partial def nestTerms? (term type : Lean.Expr) : MetaM (Option (List Lean.Expr)) := do
  let type ← whnfR type
  unless type.isAppOfArity ``Prod 2 do return some [term.consumeMData]
  let (``Prod.mk, #[_, _, a, b]) := term.consumeMData.getAppFnArgs | return none
  return (a.consumeMData :: ·) <$> (← nestTerms? b type.appArg!)

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

/-- Where the per-element statement of the copying template starts when the
template's code starts at `loc`: inside the block and loop of its `while`, after
the condition and the exit test. -/
def buildBodyLoc (loc : Loc) (dst limit index : Nat) (count : IRExpr .u64) : Loc :=
  let before : List Project.IR.Stmt := [.assign limit count,
    .call 0 [⟨.u64, .bin .mul (.bin .add (.get limit) (.const 1)) (.const 8)⟩] [dst],
    .store (.get dst) (.get limit), .assign index (.const 0)]
  (((loc.skip (before.map stmtLength).sum).inside none).inside none).skip
    (exprLength (.ltU (.get index) (.get limit) : IRExpr .bool) + 2)

/-- Where the element code of the copying template starts: after the per-element
statement, of `bodyLength` instructions, the element address, and its wrap to 32
bits. -/
def buildElementLoc (loc : Loc) (dst limit index : Nat) (count : IRExpr .u64)
    (bodyLength : Nat := 0) : Loc :=
  let address : IRExpr .u64 :=
    .bin .add (.get dst) (.bin .mul (.bin .add (.get index) (.const 1)) (.const 8))
  (buildBodyLoc loc dst limit index count).skip (bodyLength + exprLength address + 1)

/-- Where the value of slot `k` starts in `Stmt.record dst values mask` when the record's code
starts at `loc`: after the allocation, the header stores, the earlier slots' stores, and the
slot's address. -/
def recordValueLoc (loc : Loc) (dst : Nat) (values : List (IRExpr .u64)) (mask : UInt64)
    (k : Nat) : Loc :=
  loc.skip (stmtLength (Stmt.record dst (values.take k) mask) +
    exprLength (.bin .add (.get dst) (.const 0) : IRExpr .u64) + 1)

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

/-- The local of the array variable `term` in `vars`, which the code must not have moved. -/
def lookupArray (vars : List (Lean.Expr × Nat)) (term : Lean.Expr) : CompileM (Option Nat) := do
  let some local_ := vars.lookup term | return none
  if (← get).consumed.contains term then
    throwError "the array {← sourceOf term} is used after the code moved it"
  return some local_

/-- The local of the variable `term` of a recursive type, which the code must not have
moved. -/
def lookupNode (ctx : Ctx) (term : Lean.Expr) : CompileM (Option Nat) := do
  let some local_ := ctx.nodes.lookup term | return none
  if (← get).consumed.contains term then
    throwError "the value {← sourceOf term} is used after the code moved it"
  return some local_

/-- Records that the code has moved the owned parameter `param`. -/
def markMoved (param : Lean.Expr) : CompileM Unit := do
  if (← get).pendingReads.contains param then
    throwError "the value {← sourceOf param} moves before an earlier part of the same value reads it"
  modify fun p => { p with consumed := param :: p.consumed }

/-- The locals that `e` reads: those it gets, including the pointers of arrays and values of
recursive types that it passes on, and the arrays whose elements it reads. -/
def readLocals : {type : ScalarType} → IRExpr type → List Nat
  | _, .get index => [index]
  | _, .read array position => array :: readLocals position
  | _, .bin _ l r => readLocals l ++ readLocals r
  | _, .eq l r => readLocals l ++ readLocals r
  | _, .ne l r => readLocals l ++ readLocals r
  | _, .ltU l r => readLocals l ++ readLocals r
  | _, .leU l r => readLocals l ++ readLocals r
  | _, .and l r => readLocals l ++ readLocals r
  | _, .or l r => readLocals l ++ readLocals r
  | _, .binF _ l r => readLocals l ++ readLocals r
  | _, .eqF l r => readLocals l ++ readLocals r
  | _, .ltF l r => readLocals l ++ readLocals r
  | _, .leF l r => readLocals l ++ readLocals r
  | _, .not c => readLocals c
  | _, .unF _ x => readLocals x
  | _, .convertU x => readLocals x
  | _, .truncSatU x => readLocals x
  | _, .ofBits x => readLocals x
  | _, .toBits x => readLocals x
  | _, .ite c a b => readLocals c ++ readLocals a ++ readLocals b
  | _, .iteF c a b => readLocals c ++ readLocals a ++ readLocals b
  | _, _ => []

/-- Runs `action`, which translates a later part of a value, while the arrays and values of
recursive types at the locals `reads`, which earlier parts read, count as pending reads: the
earlier parts run after `action`'s statements, so `action` may not move them. -/
def afterReads {γ : Type} (ctx : Ctx) (reads : List Nat) (action : CompileM γ) : CompileM γ := do
  let arrays := (ctx.arrays ++ ctx.floatArrays ++ ctx.nodes).filterMap fun (x, local_) =>
    if reads.contains local_ then some x else none
  let saved := (← get).pendingReads
  modify fun p => { p with pendingReads := arrays ++ p.pendingReads }
  let result ← action
  modify fun p => { p with pendingReads := saved }
  return result

/-- The number of occurrences of the free variable `x` in `term`. -/
partial def occurrences (x : FVarId) : Lean.Expr → Nat
  | .fvar y => if y == x then 1 else 0
  | .app f a => occurrences x f + occurrences x a
  | .lam _ t b _ | .forallE _ t b _ => occurrences x t + occurrences x b
  | .letE _ t v b _ => occurrences x t + occurrences x v + occurrences x b
  | .mdata _ e | .proj _ _ e => occurrences x e
  | _ => 0

/-- `ctx` for the value of a `let` whose body is `body`: the value may move only the owned values
that the body does not use. -/
def Ctx.movableIn (ctx : Ctx) (body : Lean.Expr) : Ctx :=
  { ctx with owned := ctx.owned.filter fun x => occurrences x.fvarId! body == 0 }

/-- `ctx` for a part of a value that the parts `later` follow: the part may move only the owned
arrays that no later part mentions, since the later parts use them. -/
def Ctx.before (ctx : Ctx) (later : List Lean.Expr) : Ctx :=
  let arrays := (ctx.arrays ++ ctx.floatArrays).map (·.1)
  { ctx with owned := ctx.owned.filter fun x =>
      !arrays.contains x || later.all fun t => occurrences x.fvarId! t == 0 }

/-- Runs `k` with a fresh variable of each type in `types`. -/
def withVars {γ : Type} : List Lean.Expr → (List Lean.Expr → MetaM γ) → MetaM γ
  | [], k => k []
  | type :: types, k => withLocalDeclD `field type fun x => withVars types fun xs => k (x :: xs)

/-- For each result component of `type`, whether it points to heap data the value owns: an
array, a list, or a value of a recursive type. -/
partial def heapComponents (type : Lean.Expr) : MetaM (List Bool) := do
  let type ← whnfR type
  if type.isAppOfArity ``Prod 2 then
    return (← heapComponents type.appFn!.appArg!) ++ (← heapComponents type.appArg!)
  if (← isArray type) || (← isUInt64List type) || (← isNodeType type) then return [true]
  return (← resultTypes type).map fun _ => false

/-- The array parameters and parameters of recursive types among `params` that the result
term `term` moves on some path, through its `let`s, matches, branches, and pairs: those it
returns, passes as the left operand of `++`, passes at an owned position of a callee in
`owners`, or places in a constructor of a recursive type.  A match on a value of a recursive
type moves the value when its record branch moves one of the record's children. -/
partial def moveSites (owners : List (Name × List Nat)) (params : List Lean.Expr)
    (term : Lean.Expr) : MetaM (List Lean.Expr) := do
  let term := term.consumeMData.headBeta
  if let .letE name type value body _ := term then
    -- A `let` of an array or tree variable is the variable, and a value moves only what the
    -- body does not use.
    if value.consumeMData.isFVar && ((← isArray type) || (← isNodeType type)) then
      return ← moveSites owners params (body.instantiate1 value.consumeMData)
    let inValue := (← moveSites owners params value).filter fun x =>
      occurrences x.fvarId! body == 0
    return inValue ++ (← withLocalDeclD name type fun x =>
      moveSites owners params (body.instantiate1 x))
  if params.contains term then return [term]
  if let .proj _ _ pair := term then return ← moveSites owners params pair
  if let some unfolded ← unfoldMatcher? term then return ← moveSites owners params unfolded
  if let some (discriminant, alternatives) ← userCases? term then
    if ← isNodeType (← inferType discriminant) then
      let discriminant := discriminant.consumeMData
      let mut sites := []
      for alternative in alternatives do
        sites := sites ++ (← withVars alternative.fields fun xs => do
          let children ← xs.filterM fun x => do isNodeType (← inferType x)
          let inner ← moveSites owners (params ++ children) (alternative.body xs)
          let outer := inner.filter (!children.contains ·)
          return if params.contains discriminant && inner.any children.contains
            then discriminant :: outer else outer)
      return sites
  if let some (fields, _) ← recordCell? term then
    return (← fields.mapM (moveSites owners params)).flatten
  match term.getAppFnArgs with
  | (``Prod.casesOn, #[_, _, _, pair, alternative]) =>
      return (← moveSites owners params pair) ++
        (← lambdaTelescope alternative fun _ body => moveSites owners params body)
  | (``Prod.fst, #[_, _, pair]) | (``Prod.snd, #[_, _, pair]) =>
      moveSites owners params pair
  | (``ite, #[type, _, _, a, b]) =>
      if (← whnfR type).isAppOfArity ``Prod 2 || (← isArray type) || (← isNodeType type) then
        return (← moveSites owners params a) ++ (← moveSites owners params b)
      return []
  | (``Prod.mk, #[_, _, a, b]) =>
      -- The first part moves only the arrays that the second does not use; it copies the rest.
      let first ← (← moveSites owners params a).filterM fun x => do
        return !(← isArray (← inferType x)) || occurrences x.fvarId! b == 0
      return first ++ (← moveSites owners params b)
  | (``LeanExe.loop, #[stateType, _, init, _]) =>
      -- A loop over a nest of arrays moves its initial components.
      unless ← isArrayNest stateType do return []
      let some terms ← nestTerms? init stateType | return []
      return terms.filter params.contains
  | (``HAppend.hAppend, #[_, _, _, _, left, _]) =>
      return if params.contains left.consumeMData then [left.consumeMData] else []
  | (``Array.set!, #[_, array, _, _]) | (``Array.setIfInBounds, #[_, array, _, _])
  | (``Array.insertIdx!, #[_, array, _, _]) | (``Array.eraseIdxIfInBounds, #[_, array, _])
  | (``Array.push, #[_, array, _]) =>
      moveSites owners params array
  | (fn, args) =>
      return (← ((owners.lookup fn).getD []).mapM fun i => do
        let some arg := args[i]? | return []
        moveSites owners params arg).flatten

/-- The arguments at position `i` of the calls of `self` in `term`. -/
partial def selfArgs (self : Name) (i : Nat) (term : Lean.Expr) : MetaM (List Lean.Expr) := do
  let term := term.consumeMData.headBeta
  if let .letE n t v body _ := term then
    return (← selfArgs self i v) ++
      (← withLocalDeclD n t fun x => selfArgs self i (body.instantiate1 x))
  if let some unfolded ← unfoldMatcher? term then return ← selfArgs self i unfolded
  if let some (discriminant, alternatives) ← userCases? term then
    let mut out ← selfArgs self i discriminant
    for alternative in alternatives do
      out := out ++ (← withVars alternative.fields fun xs => selfArgs self i (alternative.body xs))
    return out
  match term with
  | .app .. =>
    let args := term.getAppArgs
    let here := if term.getAppFn.isConstOf self then (args[i]?.map (·.consumeMData)).toList
      else []
    return here ++ (← args.toList.mapM (selfArgs self i)).flatten
  | .lam .. => lambdaTelescope term fun _ body => selfArgs self i body
  | _ => return []

/-- Releases the owned parameters that the code has not moved on the current path. -/
def releaseUnmoved (ctx : Ctx) : CompileM Unit := do
  for param in ctx.owned do
    unless (← get).consumed.contains param do
      let some local_ := (ctx.nodes ++ ctx.arrays ++ ctx.floatArrays).lookup param
        | throwError "an owned parameter has no local"
      let stmt := Project.IR.Stmt.release local_
      pushStmt stmt [mkHint ⟨[], 0⟩ (stmtLength stmt) "release owned parameter" (← sourceOf param)]
      markMoved param

/-- Makes the arrays, lists, and values of recursive types among `xs`, the components of a
call's result or of an owned pair, owned temporaries, which the code may move and the function
releases otherwise, and marks the pairs among them as owned pairs. -/
def ownComponents (ctx : Ctx) (source : String) (xs : List (Lean.Expr × Lean.Expr)) :
    CompileM Ctx := do
  let mut ctx := ctx
  for (x, type) in xs do
    if (← isArray type) || (← isUInt64List type) || (← isNodeType type) then
      unless ctx.temporaries && ctx.foldable && ctx.allocating do
        throwError "an array, a list, or a value of a recursive type may be bound from a call's result only at the top of a function body: {source}"
      let some local_ := (ctx.arrays ++ ctx.floatArrays ++ ctx.nodes).lookup x
        | throwError "a heap component has no local: {source}"
      modify fun p => { p with temporaries := p.temporaries.push (x, local_, source) }
      ctx := { ctx with owned := x :: ctx.owned }
    else if ← isTupleType type then
      ctx := { ctx with owned := x :: ctx.owned }
  return ctx

/-- Binds a fresh variable for each field type in `fields` to its slice of `components`, of
the lengths `widths`, in order, and continues with the variables. -/
def bindFields {γ : Type} (ctx : Ctx) (k : Ctx → List Lean.Expr → CompileM γ) :
    List Lean.Expr → List Nat → List (Nat × ScalarType) → List Lean.Expr → CompileM γ
  | field :: fields, width :: widths, components, xs =>
      withLocalDeclD `field field fun x => do
        let ctx ← ctx.bindTyped x field (components.take width)
        bindFields ctx k fields widths (components.drop width) (xs ++ [x])
  | _, _, _, xs => k ctx xs

/-- The field types of the pair or structure type `type`. -/
def tupleFields? (type : Lean.Expr) : MetaM (Option (List Lean.Expr)) := do
  let type ← whnfR type
  if type.isAppOfArity ``Prod 2 then return some [type.appFn!.appArg!, type.appArg!]
  let some (.struct _ fields) ← userType? type | return none
  return some fields

/-- Runs `k` on the body of `alternative` with its fields bound to `slots`. -/
def caseBody {γ : Type} (ctx : Ctx) (slots : List (Nat × ScalarType)) (alternative : CaseAlt)
    (k : Ctx → Lean.Expr → CompileM γ) : CompileM γ := do
  let widths ← alternative.fields.mapM fun field => return (← stateTypes field).length
  bindFields ctx (fun ctx xs => k ctx (alternative.body xs)) alternative.fields widths slots []

/-- Binds the fields `fields`, from slot `i` on, of the record at local `ptr` to fresh locals,
and continues with `k` given the field variables and the loads that fill the locals.  A word
or float field is loaded as its value, and a field of a recursive type as its pointer. -/
partial def bindRecordFields {γ : Type} (ctx : Ctx) (ptr : Nat)
    (k : Ctx → List Lean.Expr → List Project.IR.Stmt → CompileM γ) :
    Nat → List Lean.Expr → List Lean.Expr → List Project.IR.Stmt → CompileM γ
  | _, [], xs, loads => k ctx xs loads
  | i, field :: fields, xs, loads => do
      let address : IRExpr .u64 := .bin .add (.get ptr) (.const (UInt64.ofNat (8 * i)))
      withLocalDeclD `field field fun x => do
        if ← isFloat field then
          let local_ ← fresh .f64 "field"
          bindRecordFields { ctx with floats := (x, local_) :: ctx.floats } ptr k (i + 1) fields
            (xs ++ [x]) (loads ++ [.load .f64 local_ address])
        else if ← isWordType field then
          let local_ ← fresh .u64 "field"
          bindRecordFields { ctx with words := (x, local_) :: ctx.words } ptr k (i + 1) fields
            (xs ++ [x]) (loads ++ [.load .u64 local_ address])
        else if ← isNodeType field then
          let local_ ← fresh .u64 "field"
          bindRecordFields { ctx with nodes := (x, local_) :: ctx.nodes } ptr k (i + 1) fields
            (xs ++ [x]) (loads ++ [.load .u64 local_ address])
        else
          throwError "a field of a recursive type must be a word, a float, or a value of a recursive type: {field}"

/-- Hints for the statements `stmts`, which follow one another from `loc`, each with its rule. -/
def settleHints (loc : Loc) (source : String) (stmts : List (Project.IR.Stmt × String)) :
    List Hint :=
  (List.range stmts.length).zip stmts |>.map fun (j, (stmt, rule)) =>
    mkHint (loc.skip ((stmts.take j).map (stmtLength ·.1)).sum) (stmtLength stmt) rule source

/-- The expression that reads local `local_` of type `type`. -/
def readLocal : Nat × ScalarType → Σ type, IRExpr type
  | (local_, .f64) => ⟨.f64, .getF local_⟩
  | (local_, _) => ⟨.u64, .get local_⟩

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
    -- An owned value of a recursive type moves into the value that uses it.
    if let some local_ ← lookupNode ctx term then
      unless ctx.owned.contains term do
        throwError "a borrowed value of a recursive type may not be returned or stored: {source}"
      markMoved term
      let ir : IRExpr .u64 := .get local_
      return (ir, [hint ir "move"])
    -- A constructor of a recursive type rewrites the matched owned record when one is free and
    -- of its type, and allocates a record otherwise.
    if let some (fields, mask) ← recordCell? term then
      unless term.isAppOf ``List.cons do
        if let some (matched, _, _) := ctx.reuse then
          if !(← get).rebuilt.contains matched &&
              (← isDefEq (← inferType term) (← inferType matched)) then
            return ← translateReuse ctx loc term fields
        return ← translateNewRecord ctx loc term fields mask
    if let .const name _ := term then
      if let some index ← enumIndex? name then
        let ir : IRExpr .u64 := .const (UInt64.ofNat index)
        return (ir, [hint ir "constructor"])
      if ← isNullCtor name then
        let ir : IRExpr .u64 := .const 0
        return (ir, [hint ir "null constructor"])
    if let some field ← projectionField? ctx term then
      match field with
      | .inl reduced => return ← translateValue ctx loc reduced
      | .inr [(local_, .u64)] =>
          let ir : IRExpr .u64 := .get local_
          return (ir, [hint ir "field"])
      | .inr _ => throwError "a field used as a word must be one word: {source}"
    -- A `let` of a word: the value is assigned to a fresh local before the body's value.
    -- The value is pure, so its statement may run whenever the body's statements run.
    if let .letE name type value body _ := term then
      unless ← isWordType type do throwError "a `let` in a word value must bind a word: {source}"
      let (v, vHints) ← translateValue (ctx.movableIn body) ⟨[], 0⟩ value
      let local_ ← fresh .u64 name.eraseMacroScopes.toString
      let stmt := Project.IR.Stmt.assign local_ v
      pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "let" (← sourceOf value) :: vHints)
      return ← withLocalDeclD name type fun x =>
        translateValue (ctx.bind x [(local_, .u64)]) loc (body.instantiate1 x)
    if let some unfolded ← unfoldMatcher? term then
      return ← translateValue ctx loc unfolded
    if let some (discriminant, alternatives) ← userCases? term then
      if let some ptr ← lookupNode ctx discriminant.consumeMData then
        let result ← fresh .u64 "match result"
        translateNodeCases ctx source discriminant.consumeMData ptr alternatives
          fun ctx at_ body => do
            let (pre, ⟨_, v⟩, vHints, vAt) ← translatePrefixed ctx at_ .u64 body
            let stmt : Project.IR.Stmt := .assign result v
            return (pre ++ [stmt], vHints ++ [mkHint vAt (stmtLength stmt) "match value" source])
        let ir : IRExpr .u64 := .get result
        return (ir, [hint ir "match result"])
      let (ctx, d, slots, dHints) ← caseDiscriminant ctx loc discriminant alternatives
      let (ir, hints) ← translateWordCases { ctx with foldable := false } loc d 0 (slots.zip alternatives)
      return (ir, hint ir "case split" :: dHints ++ hints)
    match term.getAppFnArgs with
    | (``OfNat.ofNat, #[type, .lit (.natVal value), _]) =>
        unless ← isUInt64 type do throwError "unsupported literal type: {type}"
        let ir : IRExpr .u64 := .const (UInt64.ofNat value)
        return (ir, [hint ir "literal"])
    | (``ite, #[type, condition, _, thenTerm, elseTerm]) =>
        if ← isNodeType type then
          let ir : IRExpr .u64 := .get (← translateNodeIf ctx source condition thenTerm elseTerm)
          return (ir, [hint ir "if result"])
        unless ← isWordType type do throwError "unsupported conditional type in {source}"
        let inner := { ctx with foldable := false }
        let (c, cHints) ← translateCondition ctx loc condition
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
        let some arrayLocal ← lookupArray (ctx.arrays ++ ctx.floatArrays) array.consumeMData
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
    | (``Array.foldl, _) | (``List.foldl, _) =>
        let ir : IRExpr .u64 := .get (← translateFold ctx term .u64)
        return (ir, [hint ir "fold result"])
    | (``List.nil, #[element]) =>
        unless ← isUInt64 element do throwError "unsupported list element type in {source}"
        let ir : IRExpr .u64 := .const 0
        return (ir, [hint ir "empty list"])
    | (``List.cons, _) =>
        throwError "a list cell may appear only as the next state of a loop: {source}"
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
    | (``Max.max, #[type, _, a, b]) =>
        unless ← isUInt64 type do throwError "unsupported max type in {source}"
        -- `max a b` is `if a ≤ b then b else a`.  Each operand is translated once, its
        -- statements first, and its value is assigned to a fresh local, so that a call in an
        -- operand runs once.
        let (l, lHints) ← translateValue ctx ⟨[], 0⟩ a
        let (r, rHints) ← afterReads ctx (readLocals l) (translateValue ctx ⟨[], 0⟩ b)
        let x ← fresh .u64 "max operand"
        let xStmt := Project.IR.Stmt.assign x l
        pushStmt xStmt (mkHint ⟨[], 0⟩ (stmtLength xStmt) "max operand" (← sourceOf a) :: lHints)
        let y ← fresh .u64 "max operand"
        let yStmt := Project.IR.Stmt.assign y r
        pushStmt yStmt (mkHint ⟨[], 0⟩ (stmtLength yStmt) "max operand" (← sourceOf b) :: rHints)
        let ir : IRExpr .u64 := .ite (.leU (.get x) (.get y)) (.get y) (.get x)
        return (ir, [hint ir "max"])
    | (``GetElem?.getElem!, #[collection, _, element, _, _, _, array, position]) =>
        unless (← isUInt64Array collection) && (← isUInt64 element) do
          throwError "unsupported array read in {source}"
        let some arrayLocal ← lookupArray ctx.arrays array.consumeMData
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
    | (fn, _) =>
      if fn == ctx.self then
        if let some (index, depth) := ctx.selfCall then
          let result ← translateSelfCall ctx term index depth
          let ir : IRExpr .u64 := .get result
          return (ir, [hint ir "recursive call result"])
      if let some index := ctx.callees.lookup fn then
        let [(result, .u64)] ← translateCall ctx term index
          | throwError "a call used as a word must return one word: {source}"
        let ir : IRExpr .u64 := .get result
        return (ir, [hint ir "call result"])
      match term.getAppFnArgs with
      | (fn, #[left, right, out, _, a, b]) =>
        let some (_, op, rule) := binaryRules.find? (·.1 == fn)
          | throwError "unsupported operation {fn} in {source}"
        unless (← isUInt64 left) && (← isUInt64 right) && (← isUInt64 out) do
          throwError "unsupported operand types in {source}"
        let (l, lHints) ← translateValue ctx loc a
        let offset := if op = .divU ∨ op = .remU then exprLength l + 1 else exprLength l
        let (r, rHints) ← afterReads ctx (readLocals l) (translateValue ctx (loc.skip offset) b)
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
      let (r, rHints) ← afterReads ctx (readLocals l)
        (translateFloat ctx (loc.skip (exprLength l)) b)
      let ir := make l r
      return (ir, hint ir rule :: lHints ++ rHints)
    let pair (make : IRExpr .u64 → IRExpr .u64 → IRExpr .bool) (rule : String)
        (a b : Lean.Expr) : CompileM (IRExpr .bool × List Hint) := do
      let (l, lHints) ← translateValue ctx loc a
      let (r, rHints) ← afterReads ctx (readLocals l)
        (translateValue ctx (loc.skip (exprLength l)) b)
      let ir := make l r
      return (ir, hint ir rule :: lHints ++ rHints)
    let connective (make : IRExpr .bool → IRExpr .bool → IRExpr .bool) (rule : String)
        (a b : Lean.Expr) : CompileM (IRExpr .bool × List Hint) := do
      let (l, lHints) ← translateCondition ctx loc a
      let inner := (loc.skip (exprLength l)).inside (some (if rule == "and" then 0 else 1))
      let (r, rHints) ← afterReads ctx (readLocals l)
        (translateCondition { ctx with foldable := false } inner b)
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
    if let some field ← projectionField? ctx term then
      match field with
      | .inl reduced => return ← translateFloat ctx loc reduced
      | .inr [(local_, .f64)] =>
          let ir : IRExpr .f64 := .getF local_
          return (ir, [hint ir "field"])
      | .inr _ => throwError "a field used as a float must be one float: {source}"
    if let some (discriminant, alternatives) ← userCases? term then
      let (ctx, d, slots, dHints) ← caseDiscriminant ctx loc discriminant alternatives
      let (ir, hints) ← translateFloatCases { ctx with foldable := false } loc d 0 (slots.zip alternatives)
      return (ir, hint ir "case split" :: dHints ++ hints)
    if let some index := ctx.callees.lookup term.getAppFn.constName then
      let [(result, .f64)] ← translateCall ctx term index
        | throwError "a call used as a float must return one float: {source}"
      let ir : IRExpr .f64 := .getF result
      return (ir, [hint ir "call result"])
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
    | (``Array.foldl, _) | (``List.foldl, _) =>
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
    | (``Float.ofBits, #[bits]) =>
        -- The reinterpretation keeps a NaN payload, which Lean's model replaces with the
        -- canonical NaN, so a proof must show that `bits` is not a NaN pattern.
        let (w, wHints) ← translateValue ctx loc bits
        let ir : IRExpr .f64 := .ofBits w
        return (ir, hint ir "float of bits" :: wHints)
    | (``GetElem?.getElem!, #[_, _, _, _, _, _, array, position]) =>
        let some arrayLocal ← lookupArray ctx.floatArrays array.consumeMData
          | throwError "a float read must be of an `Array Float` variable: {source}"
        let (``UInt64.toNat, #[k]) := position.consumeMData.getAppFnArgs
          | throwError "a read position must be `i.toNat` for a UInt64 `i`: {source}"
        let (i, iHints) ← translateValue ctx loc k
        let ir : IRExpr .f64 := .ofBits (.read arrayLocal i)
        return (ir, hint ir "float array read" :: iHints)
    | (fn, #[left, right, out, _, a, b]) =>
        let some (_, op, rule) := floatRules.find? (·.1 == fn)
          | throwError "unsupported float operation {fn} in {source}"
        unless (← isFloat left) && (← isFloat right) && (← isFloat out) do
          throwError "unsupported operand types in {source}"
        let (l, lHints) ← translateFloat ctx loc a
        let (r, rHints) ← afterReads ctx (readLocals l)
          (translateFloat ctx (loc.skip (exprLength l)) b)
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

  /-- The field that `term` projects from a pair or structure: the field term itself when
  the projection applies to a constructor, which `whnfR` exposes, and otherwise the field's
  component locals.  `none` when `term` is not a projection. -/
  partial def projectionField? (ctx : Ctx) (term : Lean.Expr) :
      CompileM (Option (Lean.Expr ⊕ List (Nat × ScalarType))) := do
    let projection ← match term.getAppFn with
      | .const fn _ => pure ((← getProjectionFnInfo? fn).any (!·.fromClass))
      | .proj .. => pure true
      | _ => pure false
    unless projection do return none
    let reduced ← whnfR term
    let .proj _ index value := reduced | return some (.inl reduced)
    let some fields ← tupleFields? (← inferType value)
      | throwError "unsupported projection: {← sourceOf term}"
    let value := value.consumeMData
    let isVariable := (ctx.tuples.lookup value).isSome
    if isVariable && (← heapComponents fields[index]!).any id then consumeTuple ctx value
    let components ← tupleOf ctx value
    let widths ← fields.mapM fun field => return (← resultTypes field).length
    let start := (widths.take index).sum
    unless isVariable do
      -- A call's result is new: its heap components other than the projected one are released.
      let heap ← heapComponents (← inferType value)
      for h : j in [:components.length] do
        if heap[j]?.getD false && !(start ≤ j && j < start + widths[index]!) then
          let stmt := Project.IR.Stmt.release components[j].1
          pushStmt stmt [mkHint ⟨[], 0⟩ (stmtLength stmt) "release dropped component"
            (← sourceOf term)]
    return some (.inr ((components.drop start).take widths[index]!))

  /-- Marks the owned pair variable `value`, whose components include heap data, as moved:
  using it whole, projecting a heap component, or taking it apart moves it. -/
  partial def consumeTuple (ctx : Ctx) (value : Lean.Expr) : CompileM Unit := do
    unless ctx.owned.contains value do return
    unless (← heapComponents (← inferType value)).any id do return
    if (← get).consumed.contains value then
      throwError "the pair {← sourceOf value} is used after the code moved it"
    markMoved value

  /-- The constructor index of the discriminant of a case split, and for each alternative,
  the locals of its constructor's fields: none for an enumeration, whose value is the index,
  and for a sum, the slots that follow the index in its components.  A sum discriminant
  that is not a variable, such as a call, is bound as a tuple in the returned context, so
  that an alternative that refers to it reads its locals instead of computing it again. -/
  partial def caseDiscriminant (ctx : Ctx) (loc : Loc) (discriminant : Lean.Expr)
      (alternatives : List CaseAlt) :
      CompileM (Ctx × IRExpr .u64 × List (List (Nat × ScalarType)) × List Hint) := do
    if ← isWordType (← inferType discriminant) then
      let (d, hints) ← translateValue ctx loc discriminant
      return (ctx, d, alternatives.map fun _ => [], hints)
    let discriminant := discriminant.consumeMData
    let components ← tupleOf ctx discriminant
    let some (tag, _) := components.head?
      | throwError "a sum has no components: {← sourceOf discriminant}"
    let mut slots := []
    let mut rest := components.drop 1
    for alternative in alternatives do
      let width := (← alternative.fields.mapM fun field => return (← stateTypes field).length).sum
      slots := slots ++ [rest.take width]
      rest := rest.drop width
    return ({ ctx with tuples := (discriminant, components) :: ctx.tuples }, .get tag, slots, [])

  /-- Translates a case split on the constructor index `d` to a chain of conditionals whose
  last alternative is unguarded.  Each alternative's fields are bound to its slots. -/
  partial def translateWordCases (ctx : Ctx) (loc : Loc) (d : IRExpr .u64) (index : Nat) :
      List (List (Nat × ScalarType) × CaseAlt) → CompileM (IRExpr .u64 × List Hint)
    | [] => throwError "a case split needs an alternative"
    | [(slots, last)] => caseBody ctx slots last fun ctx body => translateValue ctx loc body
    | (slots, alternative) :: rest => do
        let condition : IRExpr .bool := .eq d (.const (UInt64.ofNat index))
        let branch := loc.skip (exprLength condition)
        let (a, aHints) ← caseBody ctx slots alternative fun ctx body =>
          translateValue ctx (branch.inside (some 0)) body
        let (b, bHints) ← translateWordCases ctx (branch.inside (some 1)) d (index + 1) rest
        return (.ite condition a b, aHints ++ bHints)


  /-- `translateWordCases` for a float result. -/
  partial def translateFloatCases (ctx : Ctx) (loc : Loc) (d : IRExpr .u64) (index : Nat) :
      List (List (Nat × ScalarType) × CaseAlt) → CompileM (IRExpr .f64 × List Hint)
    | [] => throwError "a case split needs an alternative"
    | [(slots, last)] => caseBody ctx slots last fun ctx body => translateFloat ctx loc body
    | (slots, alternative) :: rest => do
        let condition : IRExpr .bool := .eq d (.const (UInt64.ofNat index))
        let branch := loc.skip (exprLength condition)
        let (a, aHints) ← caseBody ctx slots alternative fun ctx body =>
          translateFloat ctx (branch.inside (some 0)) body
        let (b, bHints) ← translateFloatCases ctx (branch.inside (some 1)) d (index + 1) rest
        return (.iteF condition a b, aHints ++ bHints)

  /-- The values of the components of `term`, of type `type`: the value of a word or float,
  and for a pair or structure, those of a constructor application's parts, or the locals of a
  tuple variable, call, or loop. -/
  partial def translateComponents (ctx : Ctx) (loc : Loc) (term type : Lean.Expr) :
      CompileM (List ((type : ScalarType) × IRExpr type) × List Hint) := do
    let term := term.consumeMData
    unless ← isTupleType type do
      let (value, hints) ← translateAs ctx loc (← scalarTypeOf type) term
      return ([value], hints)
    if let some parts ← constructorParts? term type then
      let mut values := []
      let mut hints := []
      let mut here := loc
      for (part, partType) in parts do
        let (vs, hs) ← translateComponents ctx here part partType
        values := values ++ vs
        hints := hints ++ hs
        here := here.skip (vs.map fun v => exprLength v.2).sum
      return (values, hints)
    return ((← tupleOf ctx term).map readLocal, [])

  /-- Translates the fold `term`, whose accumulator has type `accType`, to
  statements in the prelude and returns the local of the accumulator.  An array
  literal becomes a temporary that is released after the fold. -/
  partial def translateFold (ctx : Ctx) (term : Lean.Expr) (accType : ScalarType) :
      CompileM Nat := do
    let source ← sourceOf term
    unless ctx.foldable do
      throwError "a fold may not appear in a branch, a fold body, or a recursive definition: {source}"
    if let (``List.foldl, #[acc, element, f, init, list]) := term.getAppFnArgs then
      unless ← isUInt64 element do throwError "unsupported fold element type in {source}"
      unless ← (if accType == .f64 then isFloat acc else isUInt64 acc) do
        throwError "unsupported fold accumulator type in {source}"
      -- A list from a call is a temporary that the fold's code releases after the fold.
      let (listLocal, temporary) ← match ctx.lists.lookup list.consumeMData with
        | some index => pure (index, false)
        | none => do
            let some index := ctx.callees.lookup list.consumeMData.getAppFn.constName
              | throwError "a list fold must run over a list variable or a call: {source}"
            let [(local_, .u64)] ← translateCall ctx list.consumeMData index
              | throwError "the call in a list fold must return one list: {source}"
            pure (local_, true)
      let (⟨_, initial⟩, initialHints) ← translateAs ctx ⟨[], 0⟩ accType init
      let before ← get
      let accLocal := before.next
      let (cursorLocal, elementLocal) := (accLocal + 1, accLocal + 2)
      let assign : Project.IR.Stmt := .assign accLocal initial
      let foldLoc : Loc := ⟨[], before.length + stmtLength assign⟩
      let bodyLoc := foldBodyLoc foldLoc
        (Stmt.listFold listLocal accLocal cursorLocal elementLocal (.const 0))
      let bind (x : Lean.Expr) (index : Nat) (ctx : Ctx) : Ctx :=
        if accType == .f64 then { ctx with floats := (x, index) :: ctx.floats }
        else { ctx with words := (x, index) :: ctx.words }
      let (⟨_, body⟩, bodyHints) ← withLocalDeclD `acc acc fun a =>
        withLocalDeclD `element element fun e =>
          translateAs (bind a accLocal { ctx with
            words := (e, elementLocal) :: ctx.words, foldable := false, pureCalls := false })
            bodyLoc accType (mkApp2 f a e).headBeta
      let fold := Stmt.listFold listLocal accLocal cursorLocal elementLocal body
      let listSource ← sourceOf list
      let releases : List (Project.IR.Stmt × Hint) := if temporary then
          [(.release listLocal, mkHint ⟨[], before.length + stmtLength assign + stmtLength fold⟩
            (stmtLength (.release listLocal)) "release-list" listSource)]
        else []
      set { before with
        stmts := (before.stmts.push assign |>.push fold) ++ (releases.map Prod.fst).toArray
        hints := before.hints ++
          (mkHint ⟨[], before.length⟩ (stmtLength assign) "fold start" (← sourceOf init) ::
            initialHints.map (Hint.shift before.length) ++
            mkHint foldLoc (stmtLength fold) "list-fold-loop" source :: bodyHints ++
            releases.map Prod.snd).toArray
        length := before.length + stmtLength assign + stmtLength fold +
          (releases.map (stmtLength ∘ Prod.fst)).sum
        vars := before.vars ++ #[accType, .u64, .u64]
        names := before.names ++ #[("accumulator", accLocal), ("cursor", cursorLocal),
          ("element", elementLocal)] }
      return accLocal
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
    let (arrayLocal, temporary) ← match ← lookupArray arrays array.consumeMData with
      | some index => pure (index, false)
      | none => do
          let some elements := arrayLiteral? array
            | throwError "a fold must run over an array variable or an array literal: {source}"
          unless elementType == .u64 do
            throwError "a fold over a Float array literal is not supported: {source}"
          unless ctx.allocating do
            throwError "a fold over an array literal may not appear in an element of `LeanExe.build`: {source}"
          pure (← translateArrayLiteral ctx array elements, true)
    let (⟨_, initial⟩, initialHints) ← afterReads ctx [arrayLocal]
      (translateAs ctx ⟨[], 0⟩ accType init)
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
          { ctx with foldable := false, pureCalls := false }) bodyLoc accType (mkApp2 f a e).headBeta
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
    let some (value, fields, alternative) ← tupleCases? term | k ctx term
    let value := value.consumeMData
    if (ctx.tuples.lookup value).isSome then consumeTuple ctx value
    -- The components of a call's result, or of an owned pair, are owned.
    let owned := (ctx.tuples.lookup value).isNone || ctx.owned.contains value
    let source ← sourceOf value
    let components ← tupleOf ctx value
    let widths ← fields.mapM fun field => return (← resultTypes field).length
    bindFields ctx (fun ctx xs => do
        let ctx ← if owned then ownComponents ctx source (xs.zip fields) else pure ctx
        peel ctx (← Core.betaReduce (mkAppN alternative xs.toArray)) k)
      fields widths components []

  /-- The locals holding the components of the pair-valued `term`: a pair
  variable, a loop, or a call of a function compiled into the same module, whose
  statements join the prelude. -/
  partial def tupleOf (ctx : Ctx) (term : Lean.Expr) : CompileM (List (Nat × ScalarType)) := do
    let term := term.consumeMData
    if let some components := ctx.tuples.lookup term then return components
    if term.isAppOf ``LeanExe.loop then return ← translateLoop ctx term
    if let some fn := term.getAppFn.constName? then
      if let some index := ctx.callees.lookup fn then return ← translateCall ctx term index
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
      let earlier := readLocals count ++ inits.toList.flatMap fun init => readLocals init.1.1.2
      inits := inits.push (← afterReads ctx earlier (translateAs ctx ⟨[], 0⟩ type component),
        ← sourceOf component)
    let mut state := #[]
    for (_, type) in initTerms do
      state := state.push (← fresh type s!"state {state.size}", type)
    let limit ← fresh .u64 "limit"
    let index ← fresh .u64 "index"
    for (((⟨_, value⟩, hints), componentSource), (local_, _)) in inits.toList.zip state.toList do
      let stmt := Project.IR.Stmt.assign local_ value
      pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "loop start" componentSource :: hints)
    let bodyCtx := { ctx with foldable := false, pureCalls := true, lendsTrees := true }
    let (bodyStmts, bodyHints) ← withLocalDeclD `i (mkConst ``UInt64) fun i =>
      withLocalDeclD `state stateType fun x =>
        translateLoopBody ((bodyCtx.bind i [(index, .u64)]).bind x state.toList)
          (loopBodyLoc ⟨[], 0⟩ count) (mkApp2 f i x).headBeta state.toList
    let loop := Stmt.loop limit index count (seqAll bodyStmts)
    pushStmt loop (mkHint ⟨[], 0⟩ (stmtLength loop) "loop" source :: countHints ++ bodyHints)
    return state.toList

  /-- Translates `LeanExe.loop n init f` with an `Array Float` state to
  `Stmt.arrayLoop`, which copies `init`, an array variable, into the state local
  and runs `f i x`, one call of a definition compiled into the same module, for
  each index.  Returns the state local. -/
  partial def translateArrayLoop (ctx : Ctx) (term : Lean.Expr) (dst? : Option Nat) :
      CompileM Nat := do
    let source ← sourceOf term
    let (``LeanExe.loop, #[stateType, n, init, f]) := term.getAppFnArgs
      | throwError "unsupported loop: {source}"
    unless ← isFloatArray stateType do
      throwError "a loop over an array must have an `Array Float` state: {source}"
    let some src ← lookupArray ctx.floatArrays init.consumeMData
      | throwError "the initial state of a loop over an array must be an array variable: {source}"
    let (count, countHints) ← translateValue ctx ⟨[], 0⟩ n
    let state ← match dst? with
      | some dst => pure dst
      | none => fresh .u64 "state"
    let size ← fresh .u64 "size"
    let limit ← fresh .u64 "limit"
    let index ← fresh .u64 "index"
    let next ← fresh .u64 "next state"
    let (idx, args, callHints) ← withLocalDeclD `i (mkConst ``UInt64) fun i =>
      withLocalDeclD `x stateType fun x => do
        let body := (mkApp2 f i x).headBeta
        let some idx := ctx.callees.lookup body.getAppFn.constName
          | throwError "the body of a loop over an array must be one call: {source}"
        let bodyCtx := { ctx.bind i [(index, .u64)] with
          floatArrays := (x, state) :: ctx.floatArrays, owned := [] }
        let (_, stmts, hints) ← withBlock (translateCall bodyCtx body idx (some [next]))
        let [.call _ args _] := stmts
          | throwError "the call in a loop over an array must need no statements before it: {source}"
        return (idx, args, hints)
    let stmt := Stmt.arrayLoop state size limit index next src idx count args
    let copyLength := stmtLength (Stmt.copy state limit index size src)
    let callLoc := loopBodyLoc ⟨[], copyLength⟩ count
    pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "array loop" source ::
      mkHint ⟨[], 0⟩ copyLength "array copy" (← sourceOf init) ::
      countHints.map (Hint.shift copyLength) ++
      callHints.map fun hint => Hint.within callLoc.prefix_ (Hint.shift callLoc.index hint))
    return state

  /-- Translates `LeanExe.loop n init f`, whose state is a nest of word arrays started from
  distinct owned arrays, to `Stmt.tupleLoop`: the state locals receive the initial arrays, and
  `f i x` is one call of a definition compiled into the same module that consumes every array
  of the state and leaves the next state in the state locals.  Returns the state locals. -/
  partial def translateTupleLoop (ctx : Ctx) (term : Lean.Expr) (dests? : Option (List Nat)) :
      CompileM (List Nat) := do
    let source ← sourceOf term
    let (``LeanExe.loop, #[stateType, n, init, f]) := term.getAppFnArgs
      | throwError "unsupported loop: {source}"
    unless ctx.foldable && ctx.allocating do
      throwError "a loop may not appear in a branch, a fold or loop body, or a recursive definition: {source}"
    let some inits ← nestTerms? init stateType
      | throwError "a loop over arrays must start from distinct owned arrays: {source}"
    let mut srcs := #[]
    for a in inits do
      unless ctx.owned.contains a && (inits.filter (· == a)).length == 1 do
        throwError "a loop over arrays must start from distinct owned arrays: {source}"
      let some src ← lookupArray ctx.arrays a
        | throwError "a loop over arrays must start from distinct owned arrays: {source}"
      srcs := srcs.push src
    inits.forM markMoved
    let (count, countHints) ← translateValue ctx ⟨[], 0⟩ n
    let states ← match dests? with
      | some dests => pure dests
      | none => (List.range inits.length).mapM fun i => fresh .u64 s!"state {i}"
    let limit ← fresh .u64 "limit"
    let index ← fresh .u64 "index"
    let (idx, args, callHints) ← withLocalDeclD `i (mkConst ``UInt64) fun i =>
      withLocalDeclD `x stateType fun x => do
        let bodyCtx := { ctx.bind i [(index, .u64)] with
          tuples := (x, states.map (·, .u64)) :: ctx.tuples, owned := [] }
        peel bodyCtx (mkApp2 f i x).headBeta fun inner body => do
          let known := ctx.arrays ++ ctx.floatArrays
          let state := (inner.arrays ++ inner.floatArrays).filterMap fun (e, _) =>
            if known.any (·.1 == e) then none else some e
          let some idx := ctx.callees.lookup body.getAppFn.constName
            | throwError "the body of a loop over arrays must be one call: {source}"
          let (_, stmts, hints) ← withBlock
            (translateCall { inner with owned := state } body idx (some states))
          let [.call _ args _] := stmts
            | throwError "the call in a loop over arrays must need no statements before it: {source}"
          let consumed := (← get).consumed
          unless state.length == states.length && state.all consumed.contains do
            throwError "the call in a loop over arrays must consume every array of the state: {source}"
          return (idx, args, hints)
    let stmt := Stmt.tupleLoop states limit index srcs.toList idx count args
    let assignLength := ((states.zip srcs.toList).map fun (s, src) =>
      stmtLength (Project.IR.Stmt.assign s (.get src))).sum
    let callLoc := loopBodyLoc ⟨[], assignLength⟩ count
    pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "tuple loop" source ::
      countHints.map (Hint.shift assignLength) ++
      callHints.map fun hint => Hint.within callLoc.prefix_ (Hint.shift callLoc.index hint))
    return states

  /-- Translates `term` as a value of `type` whose code starts at `loc`, in a block
  of its own: the statements its calls need come first, then the value.  Returns
  those statements, the value, the hints at their places, and the value's place. -/
  partial def translatePrefixed (ctx : Ctx) (loc : Loc) (type : ScalarType) (term : Lean.Expr) :
      CompileM (List Project.IR.Stmt × ((type : ScalarType) × IRExpr type) × List Hint × Loc) := do
    let ((value, valueHints), stmts, stmtHints) ← withBlock (translateAs ctx ⟨[], 0⟩ type term)
    let relocate (at_ : Loc) (hint : Hint) : Hint :=
      Hint.within at_.prefix_ (Hint.shift at_.index hint)
    let here := loc.skip (stmts.map stmtLength).sum
    return (stmts, value, stmtHints.map (relocate loc) ++ valueHints.map (relocate here), here)

  /-- Translates a loop body, which computes the next state, to statements that
  bind its `have` variables to fresh locals, evaluate the next state's
  components into fresh temporaries, and copy them to the state locals.  The
  statements a call in an expression needs precede that expression's
  assignment. -/
  partial def translateLoopBody (ctx : Ctx) (loc : Loc) (term : Lean.Expr)
      (state : List (Nat × ScalarType)) : CompileM (List Project.IR.Stmt × List Hint) :=
    peel ctx term fun ctx term => do
      match term with
      | .letE name type value body _ =>
          let scalar ← scalarTypeOf type
          let (pre, ⟨_, v⟩, vHints, at_) ← translatePrefixed ctx loc scalar value
          let local_ ← fresh scalar name.toString
          let stmt := Project.IR.Stmt.assign local_ v
          let hint := mkHint at_ (stmtLength stmt) "let" (← sourceOf value)
          withLocalDeclD name type fun x => do
            let (rest, restHints) ← translateLoopBody (ctx.bind x [(local_, scalar)])
              (at_.skip (stmtLength stmt)) (body.instantiate1 x) state
            return (pre ++ stmt :: rest, hint :: vHints ++ restHints)
      | _ =>
          if let some index := ctx.callees.lookup term.getAppFn.constName then
            if ← isTupleType (← inferType term) then
              -- The call reads the state's locals before it writes the next state into them.
              let (_, stmts, hints) ← withBlock (translateCall ctx term index (some (state.map (·.1))))
              return (stmts, hints.map fun hint => Hint.within loc.prefix_ (Hint.shift loc.index hint))
          let components ← stateTerms term (← inferType term)
          let mut stmts := #[]
          let mut hints := #[]
          let mut temps := #[]
          let mut here := loc
          for (component, type) in components do
            if let some (fields, mask) ← recordCell? component then
              let temp ← fresh .u64 "next state"
              let (cell, cellHints, after) ← translateCell ctx here fields mask temp
              stmts := stmts ++ cell.toArray
              hints := hints ++ (mkHint here (cell.map stmtLength).sum "list cell"
                (← sourceOf component) :: cellHints).toArray
              temps := temps.push (temp, .u64)
              here := after
              continue
            let (pre, ⟨_, v⟩, vHints, at_) ← translatePrefixed ctx here type component
            let temp ← fresh type "next state"
            let stmt := Project.IR.Stmt.assign temp v
            hints := hints ++ (mkHint at_ (stmtLength stmt) "next state" (← sourceOf component) ::
              vHints).toArray
            stmts := stmts ++ pre.toArray |>.push stmt
            temps := temps.push (temp, type)
            here := at_.skip (stmtLength stmt)
          for ((temp, type), (local_, _)) in temps.toList.zip state do
            let stmt : Project.IR.Stmt := match type with
              | .f64 => .assign local_ (.getF temp)
              | _ => .assign local_ (.get temp)
            hints := hints.push (mkHint here (stmtLength stmt) "state copy" "state")
            stmts := stmts.push stmt
            here := here.skip (stmtLength stmt)
          return (stmts.toList, hints.toList)

  /-- Translates a case split on the value `discriminant` of a recursive type at local `ptr`, whose
  type has one constructor without fields, the null pointer, and one with fields, a record.
  Pushes a conditional statement that tests the pointer against 0, whose record branch loads the
  fields into fresh locals.  `branch` translates each alternative's body into statements that
  leave its value in the caller's result locals.  In the record's branch of a match on an owned
  value, the value itself counts as moved: a constructor of the same type rewrites the record in
  place, releasing the children it drops; a branch that moves some children without rewriting
  the record stores 0 into their slots and releases the record; and a branch that moves none of
  them only reads the record, which stays owned.  Both branches must move the same owned values
  and rewrite the same records. -/
  partial def translateNodeCases (ctx : Ctx) (source : String) (discriminant : Lean.Expr)
      (ptr : Nat) (alternatives : List CaseAlt)
      (branch : Ctx → Loc → Lean.Expr → CompileM (List Project.IR.Stmt × List Hint)) :
      CompileM Unit := do
    let [first, second] := alternatives
      | throwError "a match on a recursive type must have two constructors: {source}"
    let (nullAlt, recordAlt, nullFirst) ← match first.fields, second.fields with
      | [], _ :: _ => pure (first, second, true)
      | _ :: _, [] => pure (second, first, false)
      | _, _ => throwError "a match on a recursive type needs one constructor without fields and one with fields: {source}"
    -- The branches' statements stay inside the conditional, so they run only on their
    -- branch whenever the match's own statement runs only when needed.  The branches may still
    -- rewrite the record that an enclosing match took apart, except the record branch of a
    -- match on an owned value, which rewrites that value's record instead.
    let owned := ctx.owned.contains discriminant
    let inner := ctx
    let condition : IRExpr .bool := if nullFirst then .eq (.get ptr) (.const 0)
      else .ne (.get ptr) (.const 0)
    let branchLoc (branch : Nat) : Loc :=
      ((⟨[], 0⟩ : Loc).skip (exprLength condition)).inside (some branch)
    let nullLoc := branchLoc (if nullFirst then 0 else 1)
    let recordLoc := branchLoc (if nullFirst then 1 else 0)
    let saved := (← get).consumed
    let savedRebuilt := (← get).rebuilt
    let changes : CompileM (List Lean.Expr × List Lean.Expr) := do
      let p ← get
      return (p.consumed.filter fun x => ctx.owned.contains x && !saved.contains x,
        p.rebuilt.filter fun x => x != discriminant && !savedRebuilt.contains x)
    let (nullStmts, nHints) ← branch inner nullLoc (nullAlt.body [])
    let (nullMoves, nullRebuilt) ← changes
    let nullState := ((← get).consumed, (← get).rebuilt)
    modify fun p => { p with consumed := saved, rebuilt := savedRebuilt }
    let (recordStmts, rHints) ← bindRecordFields inner ptr (fun ctx xs loads => do
        let children ← xs.filterM fun x => do isNodeType (← inferType x)
        let ctx := if owned then
          { ctx with owned := children ++ ctx.owned, reuse := some (discriminant, ptr, xs) }
          else ctx
        if owned then markMoved discriminant
        let here := recordLoc.skip (loads.map stmtLength).sum
        let (rStmts, rHints) ← branch ctx here (recordAlt.body xs)
        -- A record that a branch does not rewrite but takes children from loses those children
        -- to the result: their slots get 0, and the record's release frees the rest.
        let mut drops := []
        if owned && !(← get).rebuilt.contains discriminant then
          let moved := children.filter (← get).consumed.contains
          if moved.isEmpty then
            modify fun p => { p with consumed := p.consumed.erase discriminant }
          else
            for h : i in [:xs.length] do
              if moved.contains xs[i] then
                drops := drops ++ [Project.IR.Stmt.store
                  (.bin .add (.get ptr) (.const (UInt64.ofNat (8 * i)))) (.const 0)]
            drops := drops ++ [Project.IR.Stmt.release ptr]
            for child in children do
              unless moved.contains child do markMoved child
        let dropAt := here.skip (rStmts.map stmtLength).sum
        let dropHints := (List.range drops.length).zip drops |>.map fun (j, drop) =>
          mkHint (dropAt.skip ((drops.take j).map stmtLength).sum) (stmtLength drop)
            (if j + 1 == drops.length then "release record" else "clear slot") source
        let loadHints := (List.range loads.length).zip loads |>.map fun (j, load) =>
          mkHint (recordLoc.skip ((loads.take j).map stmtLength).sum) (stmtLength load)
            "field load" source
        return (loads ++ rStmts ++ drops, loadHints ++ rHints ++ dropHints))
      0 recordAlt.fields [] []
    let (recordMoves, recordRebuilt) ← changes
    -- Each branch releases the owned values that the other consumes and it does not.  A null
    -- value needs no release, so the null branch consumes the value whenever the record's
    -- branch does.
    let moves := recordMoves ++ nullMoves.filter (!recordMoves.contains ·)
    let rebuilt := recordRebuilt ++ nullRebuilt.filter (!recordRebuilt.contains ·)
    let recordSettle ← settleBranch inner source moves rebuilt
    let (recordMoves, recordRebuilt) ← changes
    let recordState := ((← get).consumed, (← get).rebuilt)
    modify fun p => { p with consumed := nullState.1, rebuilt := nullState.2 }
    if recordMoves.contains discriminant then markMoved discriminant
    let nullSettle ← settleBranch inner source moves rebuilt
    let (nullMoves, nullRebuilt) ← changes
    unless nullMoves.all recordMoves.contains && recordMoves.all nullMoves.contains &&
        nullRebuilt.all recordRebuilt.contains && recordRebuilt.all nullRebuilt.contains do
      throwError "both branches of a match must move the same owned values and rewrite the same records: {source}"
    -- The discriminant's record belongs to this match: outside it, no rewrite of it remains.
    let kept := recordState.2.filter (· != discriminant)
    modify fun p => { p with consumed := recordState.1, rebuilt := kept }
    let nullAll := nullStmts ++ nullSettle.map (·.1)
    let recordAll := recordStmts ++ recordSettle.map (·.1)
    let (thenStmts, elseStmts) := if nullFirst then (nullAll, recordAll) else (recordAll, nullAll)
    let stmt : Project.IR.Stmt := .ite condition (seqAll thenStmts) (seqAll elseStmts)
    pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "node match" source :: nHints ++ rHints ++
      settleHints (nullLoc.skip (nullStmts.map stmtLength).sum) source nullSettle ++
      settleHints (recordLoc.skip (recordStmts.map stmtLength).sum) source recordSettle)

  /-- The statements that bring a branch of a join to the join's target, which consumes the
  owned values `moves` and rewrites the records `rebuilt`, each with its hint rule.  When
  another branch rewrites the record in `ctx.reuse` and this one has not, 0 goes into the slots
  of the children this branch moved, and the record is released, which frees the other
  children.  Then each other value of a recursive type in `moves` that the branch has not
  consumed is released.  The released values become consumed and the record rewritten. -/
  partial def settleBranch (ctx : Ctx) (source : String) (moves rebuilt : List Lean.Expr) :
      CompileM (List (Project.IR.Stmt × String)) := do
    let mut stmts := []
    if let some (record, ptr, xs) := ctx.reuse then
      if rebuilt.contains record && !(← get).rebuilt.contains record then
        let consumed := (← get).consumed
        for h : i in [:xs.length] do
          if (← isNodeType (← inferType xs[i])) && consumed.contains xs[i] then
            stmts := stmts ++ [(Project.IR.Stmt.store
              (.bin .add (.get ptr) (.const (UInt64.ofNat (8 * i)))) (.const 0), "clear slot")]
        stmts := stmts ++ [(Project.IR.Stmt.release ptr, "release record")]
        for x in xs do
          if (← isNodeType (← inferType x)) && !consumed.contains x then markMoved x
        modify fun p => { p with rebuilt := record :: p.rebuilt }
    for x in moves do
      unless (← get).consumed.contains x do
        let some local_ := ctx.nodes.lookup x
          | throwError "both branches must move the same owned arrays: {source}"
        stmts := stmts ++ [(Project.IR.Stmt.release local_, "release unmoved")]
        markMoved x
    return stmts

  /-- Translates the constructor application `term` of a recursive type, with fields `fields`,
  in the record branch of a match on an owned value of the same type: the value of every field
  other than the matched record's own field in the same slot, then the release of every child
  of the record that is still unmoved, then a store of each value into its slot.  The value is
  the record's pointer, and the children that stay in their slots move into it. -/
  partial def translateReuse (ctx : Ctx) (loc : Loc) (term : Lean.Expr) (fields : List Lean.Expr) :
      CompileM (IRExpr .u64 × List Hint) := do
    let source ← sourceOf term
    let some (matched, ptr, xs) := ctx.reuse
      | throwError "no record to rewrite: {source}"
    unless ← isDefEq (← inferType term) (← inferType matched) do
      throwError "a constructor may rebuild only a record of its own type: {source}"
    if (← get).rebuilt.contains matched then
      throwError "the record of {← sourceOf matched} is rebuilt twice: {source}"
    modify fun p => { p with rebuilt := matched :: p.rebuilt }
    let mut stores := #[]
    for h : i in [:fields.length] do
      let field := fields[i].consumeMData
      if xs[i]? == some field then continue
      let address : IRExpr .u64 := .bin .add (.get ptr) (.const (UInt64.ofNat (8 * i)))
      let (value, valueHints) ← afterReads ctx (stores.toList.flatMap fun s => readLocals s.2.1)
        (translateValue ctx ⟨[], exprLength address + 1⟩ field)
      stores := stores.push (address, value, valueHints)
    for h : i in [:fields.length] do
      let field := fields[i].consumeMData
      if xs[i]? == some field && (← isNodeType (← inferType field)) then
        discard <| lookupNode ctx field
        markMoved field
    for x in xs do
      if (← isNodeType (← inferType x)) && !(← get).consumed.contains x then
        let some local_ := ctx.nodes.lookup x | throwError "a child has no local: {source}"
        let stmt := Project.IR.Stmt.release local_
        pushStmt stmt [mkHint ⟨[], 0⟩ (stmtLength stmt) "release child" source]
        markMoved x
    for (address, value, valueHints) in stores do
      let stmt := Project.IR.Stmt.store address value
      pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "slot store" source :: valueHints)
    let ir : IRExpr .u64 := .get ptr
    return (ir, [mkHint loc (exprLength ir) "record reuse" source])

  /-- Translates the constructor application `term` of a recursive type, with fields `fields` and
  child mask `mask`, to a new record in a fresh local: the statements of its fields, then
  `Stmt.record`.  The value is the record's pointer. -/
  partial def translateNewRecord (ctx : Ctx) (loc : Loc) (term : Lean.Expr)
      (fields : List Lean.Expr) (mask : UInt64) : CompileM (IRExpr .u64 × List Hint) := do
    let source ← sourceOf term
    unless ctx.foldable && ctx.allocating do
      throwError "a record may be allocated only at the top of a body or in a branch of a match or an `if` on values of a recursive type: {source}"
    let dst ← fresh .u64 "record"
    let (stmts, hints, _) ← translateCell ctx ⟨[], 0⟩ fields mask dst
    let stmt := seqAll stmts
    pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "new record" source :: hints)
    let ir : IRExpr .u64 := .get dst
    return (ir, [mkHint loc (exprLength ir) "new record value" source])

  /-- Translates `if condition then thenTerm else elseTerm`, whose value is of a recursive type,
  to a conditional statement whose branches assign their value to a fresh local, which the
  function returns.  Both branches must move the same owned values and rewrite the same
  records. -/
  partial def translateNodeIf (ctx : Ctx) (source : String) (condition thenTerm elseTerm : Lean.Expr) :
      CompileM Nat := do
    let result ← fresh .u64 "if result"
    let (c, cHints) ← translateCondition ctx ⟨[], 0⟩ condition
    let branchLoc (branch : Nat) : Loc :=
      ((⟨[], 0⟩ : Loc).skip (exprLength c)).inside (some branch)
    let saved := (← get).consumed
    let savedRebuilt := (← get).rebuilt
    let changes : CompileM (List Lean.Expr × List Lean.Expr) := do
      let p ← get
      return (p.consumed.filter fun x => ctx.owned.contains x && !saved.contains x,
        p.rebuilt.filter fun x => !savedRebuilt.contains x)
    let (tPre, ⟨_, tv⟩, tHints, tAt) ← translatePrefixed ctx (branchLoc 0) .u64 thenTerm
    let thenStmt : Project.IR.Stmt := .assign result tv
    let (thenMoves, thenRebuilt) ← changes
    let thenState := ((← get).consumed, (← get).rebuilt)
    modify fun p => { p with consumed := saved, rebuilt := savedRebuilt }
    let (ePre, ⟨_, ev⟩, eHints, eAt) ← translatePrefixed ctx (branchLoc 1) .u64 elseTerm
    let elseStmt : Project.IR.Stmt := .assign result ev
    let (elseMoves, elseRebuilt) ← changes
    -- Each branch releases the owned values that the other consumes and it does not.
    let moves := thenMoves ++ elseMoves.filter (!thenMoves.contains ·)
    let rebuilt := thenRebuilt ++ elseRebuilt.filter (!thenRebuilt.contains ·)
    let elseSettle ← settleBranch ctx source moves rebuilt
    let (elseMoves, elseRebuilt) ← changes
    modify fun p => { p with consumed := thenState.1, rebuilt := thenState.2 }
    let thenSettle ← settleBranch ctx source moves rebuilt
    let (thenMoves, thenRebuilt) ← changes
    unless thenMoves.all elseMoves.contains && elseMoves.all thenMoves.contains &&
        thenRebuilt.all elseRebuilt.contains && elseRebuilt.all thenRebuilt.contains do
      throwError "both branches of an `if` must move the same owned values and rewrite the same records: {source}"
    let thenStmts := tPre ++ [thenStmt]
    let elseStmts := ePre ++ [elseStmt]
    let stmt : Project.IR.Stmt := .ite c (seqAll (thenStmts ++ thenSettle.map (·.1)))
      (seqAll (elseStmts ++ elseSettle.map (·.1)))
    pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "node branch" source :: cHints ++ tHints ++
      mkHint tAt (stmtLength thenStmt) "branch value" source :: eHints ++
      mkHint eAt (stmtLength elseStmt) "branch value" source ::
      settleHints ((branchLoc 0).skip (thenStmts.map stmtLength).sum) source thenSettle ++
      settleHints ((branchLoc 1).skip (elseStmts.map stmtLength).sum) source elseSettle)
    return result

  /-- Translates a record cell with fields `fields` and child mask `mask`, a list cell or a
  constructor of a recursive type, whose code starts at `loc`, to the statements that its
  fields need followed by `Stmt.record dst values mask`.  Returns the statements, their
  hints, and where they end. -/
  partial def translateCell (ctx : Ctx) (loc : Loc) (fields : List Lean.Expr) (mask : UInt64)
      (dst : Nat) : CompileM (List Project.IR.Stmt × List Hint × Loc) := do
    let relocate (at_ : Loc) (hint : Hint) : Hint :=
      Hint.within at_.prefix_ (Hint.shift at_.index hint)
    let mut stmts := []
    let mut stmtHints := []
    let mut values := []
    let mut valueHints := []
    let mut here := loc
    for field in fields do
      let ((v, vHints), fStmts, fStmtHints) ← afterReads ctx (values.flatMap readLocals)
        (withBlock (translateValue ctx ⟨[], 0⟩ field))
      stmts := stmts ++ fStmts
      stmtHints := stmtHints ++ fStmtHints.map (relocate here)
      here := here.skip (fStmts.map stmtLength).sum
      values := values ++ [v]
      valueHints := valueHints ++ [vHints]
    let stmt := Stmt.record dst values mask
    let fieldHints := (List.range values.length).zip valueHints |>.flatMap fun (k, hs) =>
      hs.map (relocate (recordValueLoc here dst values mask k))
    return (stmts ++ [stmt], stmtHints ++ fieldHints, here.skip (stmtLength stmt))

  /-- Pushes the copying template for an array of `count` elements whose element
  is `element`, a function of the index local, and returns the new array's local. -/
  partial def emitBuild (ctx : Ctx) (source rule : String) (count : IRExpr .u64)
      (countHints : List Hint) (element : Nat → Loc → CompileM (IRExpr .u64 × List Hint))
      (dst? : Option Nat := none) : CompileM Nat := do
    let dst ← match dst? with
      | some dst => pure dst
      | none => fresh .u64 "array"
    let limit ← fresh .u64 "limit"
    let index ← fresh .u64 "index"
    let (elementIR, elementHints) ← element index (buildElementLoc ⟨[], 0⟩ dst limit index count)
    let stmt := Stmt.build dst limit index count elementIR
    pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) rule source :: countHints ++ elementHints)
    return dst

  /-- The local of an update's array argument, which the update reads after its position and
  value, and whether the update may write it in place: the local `arrayVar?` of an array
  variable, in place when the variable is owned, or else the new owned array that
  `translateArray` builds from the term. -/
  partial def updateTarget (ctx : Ctx) (array : Lean.Expr) (arrayVar? : Option Nat) :
      CompileM (Nat × Bool) := do
    match arrayVar? with
    | some local_ => return (local_, ctx.owned.contains array.consumeMData)
    | none => return (← translateArray ctx array, true)

  /-- Translates an `Array UInt64` term to statements that leave a new array, which
  the caller owns, in local `dst?` or a fresh local, and returns the local: an
  array literal; `set!`, `insertIdx!`, `eraseIdxIfInBounds`, or `push` on an array
  variable or on such a term; `LeanExe.build`; or an array variable, which is copied. -/
  partial def translateArray (ctx : Ctx) (term : Lean.Expr) (dst? : Option Nat := none) :
      CompileM Nat := do
    let term := term.consumeMData
    let source ← sourceOf term
    unless ctx.foldable do
      throwError "an array may not be built in a branch, a fold or loop body, or a recursive definition: {source}"
    unless ctx.allocating do
      throwError "an array may not be built in an element of `LeanExe.build`: {source}"
    if term.isAppOf ``LeanExe.loop then
      return ← translateArrayLoop ctx term dst?
    if let some elements := arrayLiteral? term then
      return ← translateArrayLiteral ctx term elements dst?
    let sizeOf (arrayLocal : Nat) : CompileM Nat := do
      let size ← fresh .u64 "size"
      let stmt := Stmt.arraySize size arrayLocal
      pushStmt stmt [mkHint ⟨[], 0⟩ (stmtLength stmt) "array-size" source]
      return size
    if let some arrayLocal ← lookupArray (ctx.arrays ++ ctx.floatArrays) term then
      -- An owned parameter is returned as it is; any other array variable is copied.
      if ctx.owned.contains term then
        markMoved term
        let some dst := dst? | return arrayLocal
        let stmt := Project.IR.Stmt.assign dst (.get arrayLocal)
        pushStmt stmt [mkHint ⟨[], 0⟩ (stmtLength stmt) "array move" source]
        return dst
      let size ← fresh .u64 "size"
      let dst ← match dst? with
        | some dst => pure dst
        | none => fresh .u64 "array"
      let limit ← fresh .u64 "limit"
      let index ← fresh .u64 "index"
      let stmt := Stmt.copy dst limit index size arrayLocal
      pushStmt stmt [mkHint ⟨[], 0⟩ (stmtLength stmt) "array copy" source]
      return dst
    match term.getAppFnArgs with
    | (``Array.set!, #[element, array, position, value])
    | (``Array.setIfInBounds, #[element, array, position, value]) =>
        unless ← isUInt64 element do throwError "unsupported array element type in {source}"
        let arrayVar? ← lookupArray ctx.arrays array.consumeMData
        let (``UInt64.toNat, #[k]) := position.consumeMData.getAppFnArgs
          | throwError "a `set!` position must be `i.toNat` for a UInt64 `i`: {source}"
        let target := arrayVar?.toList
        let (kIR, kHints) ← afterReads ctx target (translateValue ctx ⟨[], 0⟩ k)
        let kLocal ← fresh .u64 "set position"
        let kStmt := Project.IR.Stmt.assign kLocal kIR
        pushStmt kStmt (mkHint ⟨[], 0⟩ (stmtLength kStmt) "set position" (← sourceOf k) :: kHints)
        let (vIR, vHints) ← afterReads ctx target (translateValue ctx ⟨[], 0⟩ value)
        let vLocal ← fresh .u64 "set value"
        let vStmt := Project.IR.Stmt.assign vLocal vIR
        pushStmt vStmt (mkHint ⟨[], 0⟩ (stmtLength vStmt) "set value" (← sourceOf value) :: vHints)
        -- An owned array at its last use takes the new element in place.
        let (arrayLocal, inPlace) ← updateTarget ctx array arrayVar?
        if inPlace then
          let size ← fresh .u64 "size"
          let stmt := Stmt.setInPlace arrayLocal size kLocal vLocal
          pushStmt stmt [mkHint ⟨[], 0⟩ (stmtLength stmt) "set in place" source]
          if arrayVar?.isSome then markMoved array.consumeMData
          let some dst := dst? | return arrayLocal
          let move := Project.IR.Stmt.assign dst (.get arrayLocal)
          pushStmt move [mkHint ⟨[], 0⟩ (stmtLength move) "array move" source]
          return dst
        let size ← sizeOf arrayLocal
        emitBuild ctx source "array set" (.get size) [] (dst? := dst?) fun index loc =>
          let ir : IRExpr .u64 :=
            .ite (.eq (.get index) (.get kLocal)) (.get vLocal) (.read arrayLocal (.get index))
          return (ir, [mkHint loc (exprLength ir) "set element" source])
    | (``Array.insertIdx!, #[element, array, position, value]) =>
        unless ← isUInt64 element do throwError "unsupported array element type in {source}"
        let arrayVar? ← lookupArray ctx.arrays array.consumeMData
        let (``UInt64.toNat, #[k]) := position.consumeMData.getAppFnArgs
          | throwError "an `insertIdx!` position must be `i.toNat` for a UInt64 `i`: {source}"
        let target := arrayVar?.toList
        let (kIR, kHints) ← afterReads ctx target (translateValue ctx ⟨[], 0⟩ k)
        let kLocal ← fresh .u64 "insert position"
        let kStmt := Project.IR.Stmt.assign kLocal kIR
        pushStmt kStmt (mkHint ⟨[], 0⟩ (stmtLength kStmt) "insert position" (← sourceOf k) :: kHints)
        let (vIR, vHints) ← afterReads ctx target (translateValue ctx ⟨[], 0⟩ value)
        let vLocal ← fresh .u64 "insert value"
        let vStmt := Project.IR.Stmt.assign vLocal vIR
        pushStmt vStmt (mkHint ⟨[], 0⟩ (stmtLength vStmt) "insert value" (← sourceOf value) :: vHints)
        -- An owned array at its last use takes the element in place, in a larger block when
        -- its own is full.
        let (arrayLocal, inPlace) ← updateTarget ctx array arrayVar?
        if inPlace then
          let size ← fresh .u64 "size"
          let cap ← fresh .u64 "capacity"
          let dst ← fresh .u64 "new block"
          let limit ← fresh .u64 "limit"
          let index ← fresh .u64 "index"
          let stmt := Stmt.insertInPlace arrayLocal size kLocal vLocal cap dst limit index
          pushStmt stmt [mkHint ⟨[], 0⟩ (stmtLength stmt) "insert in place" source]
          if arrayVar?.isSome then markMoved array.consumeMData
          let some dst := dst? | return arrayLocal
          let move := Project.IR.Stmt.assign dst (.get arrayLocal)
          pushStmt move [mkHint ⟨[], 0⟩ (stmtLength move) "array move" source]
          return dst
        let size ← sizeOf arrayLocal
        -- `insertIdx!` past the end panics and returns the empty array.
        let count : IRExpr .u64 :=
          .ite (.leU (.get kLocal) (.get size)) (.bin .add (.get size) (.const 1)) (.const 0)
        emitBuild ctx source "array insert" count [] (dst? := dst?) fun index loc =>
          let ir : IRExpr .u64 :=
            .ite (.ltU (.get index) (.get kLocal)) (.read arrayLocal (.get index))
              (.ite (.eq (.get index) (.get kLocal)) (.get vLocal)
                (.read arrayLocal (.bin .sub (.get index) (.const 1))))
          return (ir, [mkHint loc (exprLength ir) "insert element" source])
    | (``Array.eraseIdxIfInBounds, #[element, array, position]) =>
        unless ← isUInt64 element do throwError "unsupported array element type in {source}"
        let arrayVar? ← lookupArray ctx.arrays array.consumeMData
        let (``UInt64.toNat, #[k]) := position.consumeMData.getAppFnArgs
          | throwError "an `eraseIdxIfInBounds` position must be `i.toNat` for a UInt64 `i`: {source}"
        let (kIR, kHints) ← afterReads ctx arrayVar?.toList (translateValue ctx ⟨[], 0⟩ k)
        let kLocal ← fresh .u64 "erase position"
        let kStmt := Project.IR.Stmt.assign kLocal kIR
        pushStmt kStmt (mkHint ⟨[], 0⟩ (stmtLength kStmt) "erase position" (← sourceOf k) :: kHints)
        -- An owned array at its last use loses the element in place.
        let (arrayLocal, inPlace) ← updateTarget ctx array arrayVar?
        if inPlace then
          let size ← fresh .u64 "size"
          let limit ← fresh .u64 "limit"
          let index ← fresh .u64 "index"
          let stmt := Stmt.eraseInPlace arrayLocal size kLocal limit index
          pushStmt stmt [mkHint ⟨[], 0⟩ (stmtLength stmt) "erase in place" source]
          if arrayVar?.isSome then markMoved array.consumeMData
          let some dst := dst? | return arrayLocal
          let move := Project.IR.Stmt.assign dst (.get arrayLocal)
          pushStmt move [mkHint ⟨[], 0⟩ (stmtLength move) "array move" source]
          return dst
        let size ← sizeOf arrayLocal
        let count : IRExpr .u64 :=
          .ite (.ltU (.get kLocal) (.get size)) (.bin .sub (.get size) (.const 1)) (.get size)
        emitBuild ctx source "array erase" count [] (dst? := dst?) fun index loc =>
          let ir : IRExpr .u64 :=
            .ite (.ltU (.get index) (.get kLocal)) (.read arrayLocal (.get index))
              (.read arrayLocal (.bin .add (.get index) (.const 1)))
          return (ir, [mkHint loc (exprLength ir) "erase element" source])
    | (``Array.push, #[element, array, value]) =>
        unless ← isUInt64 element do throwError "unsupported array element type in {source}"
        let arrayVar? ← lookupArray ctx.arrays array.consumeMData
        let (vIR, vHints) ← afterReads ctx arrayVar?.toList (translateValue ctx ⟨[], 0⟩ value)
        let vLocal ← fresh .u64 "push value"
        let vStmt := Project.IR.Stmt.assign vLocal vIR
        pushStmt vStmt (mkHint ⟨[], 0⟩ (stmtLength vStmt) "push value" (← sourceOf value) :: vHints)
        -- An owned array at its last use takes the element in place, in a larger block when
        -- its own is full.
        let (arrayLocal, inPlace) ← updateTarget ctx array arrayVar?
        if inPlace then
          let size ← fresh .u64 "size"
          let cap ← fresh .u64 "capacity"
          let dst ← fresh .u64 "new block"
          let limit ← fresh .u64 "limit"
          let index ← fresh .u64 "index"
          let stmt := Stmt.pushInPlace arrayLocal size vLocal cap dst limit index
          pushStmt stmt [mkHint ⟨[], 0⟩ (stmtLength stmt) "push in place" source]
          if arrayVar?.isSome then markMoved array.consumeMData
          let some dst := dst? | return arrayLocal
          let move := Project.IR.Stmt.assign dst (.get arrayLocal)
          pushStmt move [mkHint ⟨[], 0⟩ (stmtLength move) "array move" source]
          return dst
        let size ← sizeOf arrayLocal
        emitBuild ctx source "array push" (.bin .add (.get size) (.const 1)) [] (dst? := dst?)
          fun index loc =>
            let ir : IRExpr .u64 :=
              .ite (.ltU (.get index) (.get size)) (.read arrayLocal (.get index)) (.get vLocal)
            return (ir, [mkHint loc (exprLength ir) "push element" source])
    | (``HAppend.hAppend, #[leftType, rightType, _, _, left, right]) =>
        unless (← isArray leftType) && (← isDefEq leftType rightType) do
          throwError "unsupported append in {source}"
        let left := left.consumeMData
        let right := right.consumeMData
        let some src1 ← lookupArray (ctx.arrays ++ ctx.floatArrays) left
          | throwError "the left operand of `++` must be an array parameter at its last use: {source}"
        unless ctx.owned.contains left && occurrences left.fvarId! right == 0 do
          throwError "the left operand of `++` must be an array parameter at its last use: {source}"
        let some src2 ← lookupArray (ctx.arrays ++ ctx.floatArrays) right
          | throwError "the right operand of `++` must be an array variable: {source}"
        markMoved left
        let dst ← match dst? with
          | some dst => pure dst
          | none => fresh .u64 "array"
        let size1 ← fresh .u64 "size"
        let size2 ← fresh .u64 "size"
        let limit ← fresh .u64 "limit"
        let index ← fresh .u64 "index"
        let cap ← fresh .u64 "capacity"
        let stmt := Stmt.append dst size1 size2 limit index cap src1 src2
        pushStmt stmt [mkHint ⟨[], 0⟩ (stmtLength stmt) "array append" source]
        return dst
    | (``LeanExe.build, #[element, count, f]) =>
        let floatElement ← isFloat element
        unless floatElement || (← isUInt64 element) do
          throwError "unsupported array element type in {source}"
        let (countIR, countHints) ← translateValue ctx ⟨[], 0⟩ count
        let dst ← match dst? with
          | some dst => pure dst
          | none => fresh .u64 "array"
        let limit ← fresh .u64 "limit"
        let index ← fresh .u64 "index"
        -- The element may run loops, whose statements form the per-element statement;
        -- a float element is stored as its bit pattern.
        let ((elementIR, elementHints), bodyStmts, bodyHints) ← withBlock do
          withLocalDeclD `i (mkConst ``UInt64) fun i => do
            let inner := { ctx with foldable := true, allocating := false, pureCalls := true }.bind
              i [(index, .u64)]
            if floatElement then
              let (x, xHints) ← translateFloat inner ⟨[], 0⟩ (mkApp f i).headBeta
              pure ((.toBits x : IRExpr .u64), xHints)
            else translateValue inner ⟨[], 0⟩ (mkApp f i).headBeta
        let body := seqAll bodyStmts
        let relocate (loc : Loc) (hint : Hint) : Hint :=
          Hint.within loc.prefix_ (Hint.shift loc.index hint)
        let stmt := Stmt.buildWith dst limit index countIR body elementIR
        pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "array build" source :: countHints ++
          bodyHints.map (relocate (buildBodyLoc ⟨[], 0⟩ dst limit index countIR)) ++
          elementHints.map
            (relocate (buildElementLoc ⟨[], 0⟩ dst limit index countIR (stmtLength body))))
        return dst
    | _ => throwError "unsupported array: {source}"

  /-- Translates a result term of type `type` to one result expression per
  component, each with hints relative to its own code: a pair gives the results of
  its components, an array a new array's pointer, and a scalar its value.  With
  `dests?`, the code leaves each component in its local there, and the results
  read those locals. -/
  partial def translateResults (ctx : Ctx) (term type : Lean.Expr)
      (dests? : Option (List Nat) := none) :
      CompileM (List (Σ type, IRExpr type) × List (List Hint)) :=
    peel ctx term fun ctx term => do
      let type ← whnfR type
      if let .letE name letType value body _ := term then
        -- A `let` of an array or tree variable is the variable.
        if value.consumeMData.isFVar && ((← isArray letType) || (← isNodeType letType)) then
          return ← translateResults ctx (body.instantiate1 value.consumeMData) type dests?
        -- The value may move the owned values that the body does not use.
        let valueCtx := ctx.movableIn body
        if ← isNodeType letType then
          -- A call's result, a temporary that the code may move and the function releases
          -- otherwise.
          let source ← sourceOf value
          unless ctx.temporaries && ctx.foldable && ctx.allocating do
            throwError "a value of a recursive type may be bound by `let` only at the top of a function body: {source}"
          let some index := ctx.callees.lookup value.getAppFn.constName
            | throwError "a `let` of a recursive type must bind a call's result: {source}"
          let [(local_, .u64)] ← translateCall valueCtx value index
            | throwError "a `let` of a recursive type must bind a call with one result: {source}"
          return ← withLocalDeclD name letType fun x => do
            modify fun p => { p with temporaries := p.temporaries.push (x, local_, source) }
            translateResults { ctx with nodes := (x, local_) :: ctx.nodes, owned := x :: ctx.owned }
              (body.instantiate1 x) type dests?
        if ← isArray letType then
          -- A temporary array, from a call or a build, which the code may move and the
          -- function releases otherwise.
          let source ← sourceOf value
          unless ctx.temporaries && ctx.foldable && ctx.allocating do
            throwError "an array may be bound by `let` only at the top of a function body: {source}"
          let local_ ← match ctx.callees.lookup value.getAppFn.constName with
            | some index => do
                let [(result, .u64)] ← translateCall valueCtx value index
                  | throwError "a `let` array must come from a call that returns one array: {source}"
                pure result
            | none => translateArray valueCtx value
          let floatArray ← isFloatArray letType
          return ← withLocalDeclD name letType fun x => do
            modify fun p => { p with temporaries := p.temporaries.push (x, local_, source) }
            let inner := if floatArray then { ctx with floatArrays := (x, local_) :: ctx.floatArrays }
              else { ctx with arrays := (x, local_) :: ctx.arrays }
            translateResults { inner with owned := x :: inner.owned } (body.instantiate1 x) type
              dests?
        let scalar ← scalarTypeOf letType
        let (⟨_, v⟩, vHints) ← translateAs valueCtx ⟨[], 0⟩ scalar value
        let local_ ← fresh scalar name.toString
        let stmt := Project.IR.Stmt.assign local_ v
        pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "let" (← sourceOf value) :: vHints)
        return ← withLocalDeclD name letType fun x =>
          translateResults (ctx.bind x [(local_, scalar)]) (body.instantiate1 x) type dests?
      -- A tuple variable, or a term already computed into locals, such as a call that a
      -- case split examines.
      if let some components := ctx.tuples.lookup term then
        consumeTuple ctx term
        return ← resultsIn components dests? (← sourceOf term)
      if let some index := ctx.callees.lookup term.getAppFn.constName then
        let results ← translateCall ctx term index dests?
        return (results.map readLocal, results.map fun _ => [])
      let branching := (← isTupleType type) || (← isArray type)
      if let (``ite, #[_, condition, _, thenTerm, elseTerm]) := term.getAppFnArgs then
        if branching then
          return ← translateResultBranch ctx term condition thenTerm elseTerm type dests?
      if term.isAppOf ``LeanExe.loop then
        if ← isArrayNest type then
          let states ← translateTupleLoop ctx term dests?
          return (states.map fun s => readLocal (s, .u64), states.map fun _ => [])
        if ← isTupleType type then
          return ← resultsIn (← translateLoop ctx term) dests? (← sourceOf term)
      if ← isTupleType type then
        if let some (discriminant, alternatives) ← userCases? term then
          -- A match on a value of a recursive type: each branch leaves its pair in the result
          -- locals.  Temporaries stay at the top of the body, which releases them on every path.
          if let some ptr ← lookupNode ctx discriminant.consumeMData then
            let source ← sourceOf term
            let types ← resultTypes type
            let dests ← match dests? with
              | some dests => pure dests
              | none => types.mapM fun type => fresh type "match result"
            translateNodeCases ctx source discriminant.consumeMData ptr alternatives
              fun ctx at_ body => do
                let (_, stmts, hints) ← withBlock
                  (translateResults { ctx with temporaries := false } body type dests)
                return (stmts, hints.map fun hint =>
                  Hint.within at_.prefix_ (Hint.shift at_.index hint))
            return ((dests.zip types).map readLocal, dests.map fun _ => [])
          return ← translateCases ctx term discriminant alternatives type dests?
        let some parts ← constructorParts? term type
          | throwError "a pair or structure result must be a constructor, a variable, a call, a loop, or a case split: {← sourceOf term}"
        let mut results := []
        let mut hints := []
        let mut remaining := dests?
        for hi : i in [:parts.length] do
          let (part, partType) := parts[i]
          let width := (← resultTypes partType).length
          -- The earlier components run after this part's statements, and the later ones use
          -- the arrays they mention.
          let partCtx := ctx.before ((parts.drop (i + 1)).map (·.1))
          let (r, h) ← afterReads ctx (results.flatMap fun result => readLocals result.2)
            (translateResults partCtx part partType (remaining.map (·.take width)))
          results := results ++ r
          hints := hints ++ h
          remaining := remaining.map (·.drop width)
        return (results, hints)
      if ← isArray type then
        let array ← translateArray ctx term (dests?.bind (·.head?))
        let ir : IRExpr .u64 := .get array
        return ([⟨.u64, ir⟩], [[mkHint ⟨[], 0⟩ (exprLength ir) "array result" (← sourceOf term)]])
      let scalar ← if (← isUInt64List type) || (← isNodeType type) then pure .u64
        else scalarTypeOf type
      let (⟨resultType, ir⟩, hints) ← translateAs ctx ⟨[], 0⟩ scalar term
      let some dest := dests?.bind (·.head?)
        | return ([⟨resultType, ir⟩], [hints])
      let stmt := Project.IR.Stmt.assign dest ir
      pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "result" (← sourceOf term) :: hints)
      return ([readLocal (dest, scalar)], [[]])

  /-- Translates a call of a definition compiled into the same module, at function
  `index`, to a call statement that leaves the callee's results in the locals
  `dests?` or in fresh locals, which it returns.  Arguments are words or pointers
  of array variables. -/
  partial def translateCall (ctx : Ctx) (term : Lean.Expr) (index : Nat)
      (dests? : Option (List Nat) := none) : CompileM (List (Nat × ScalarType)) := do
    let source ← sourceOf term
    -- Any call may appear at the result level.  Where code must keep the store, only
    -- a call with scalar arguments and results may appear; its proof shows that the
    -- callee keeps the store.
    unless ctx.foldable && ctx.allocating do
      unless ctx.pureCalls do
        throwError "a call may not appear in a branch, a fold body, or a recursive definition: {source}"
      let callOwners := (ctx.owners.lookup term.getAppFn.constName).getD []
      for h : position in [:term.getAppArgs.size] do
        let arg := term.getAppArgs[position]
        if ← isArray (← inferType arg) then
          throwError "a call in a loop body or an array element may not take an array: {source}"
        if ← isNodeType (← inferType arg) then
          unless ctx.lendsTrees && !callOwners.contains position do
            throwError "a call in an array element, or at an owned position in a loop body, may not take a value of a recursive type: {source}"
      if ← isArray (← inferType term) then
        throwError "a call in a loop body or an array element may not return an array: {source}"
      let scalars ← try (do let _ ← stateTypes (← inferType term); pure true) catch _ => pure false
      unless scalars do
        throwError "a call in a loop body or an array element must return words and floats: {source}"
    let owners := (ctx.owners.lookup term.getAppFn.constName).getD []
    -- An owned position receives an owned variable that no other argument of its kind names, or
    -- a term whose value is new, which the call consumes; a value that such a term moves occurs
    -- in no other argument.  Word and float arguments run before the call, so they may read an
    -- owned variable.
    let callArgs := term.getAppArgs
    let arrayArgs ← callArgs.toList.filterM fun arg => do isArray (← inferType arg)
    let nodeArgs ← callArgs.toList.filterM fun arg => do isNodeType (← inferType arg)
    let mut moved := []
    let mut copies := []
    for position in owners do
      let some arg := callArgs[position]?
        | throwError "a call must supply every argument: {source}"
      let arg := arg.consumeMData
      if arg.isFVar then
        let sameKind := if ← isNodeType (← inferType arg) then nodeArgs else arrayArgs
        if ctx.owned.contains arg && (sameKind.map (occurrences arg.fvarId! ·)).sum == 1 then
          moved := arg :: moved
        else if ← isArray (← inferType arg) then
          -- An array that is borrowed, used later, or named by another argument: the call
          -- consumes a copy.
          copies := position :: copies
        else
          throwError "an owned parameter must receive an owned value at its last use: {source}"
      else
        for x in ← moveSites ctx.owners ctx.owned arg do
          for h : j in [:callArgs.size] do
            if j != position && occurrences x.fvarId! callArgs[j] != 0 then
              throwError "a value that an argument moves may occur in no other argument: {source}"
    let mut args : Array ((type : ScalarType) × IRExpr type) := #[]
    let mut hints := #[]
    let mut offset := 0
    for h : position in [:callArgs.size] do
      let arg := callArgs[position]
      let argType ← inferType arg
      let owned := owners.contains position
      -- The earlier arguments run after this argument's statements.
      let earlier := args.toList.flatMap fun value => readLocals value.2
      let (values, argHints) ← afterReads ctx earlier do
        if ← isArray argType then
          let local_ ← match ← lookupArray (ctx.arrays ++ ctx.floatArrays) arg.consumeMData with
            | some local_ =>
                if copies.contains position then
                  translateArray { ctx with owned := ctx.owned.erase arg.consumeMData }
                    arg.consumeMData
                else pure local_
            | none =>
                unless owned do
                  throwError "an array argument at a borrowed position must be an array variable: {source}"
                translateArray ctx arg.consumeMData
          let ir : IRExpr .u64 := .get local_
          pure ([(⟨.u64, ir⟩ : (type : ScalarType) × IRExpr type)],
            [mkHint ⟨[], offset⟩ (exprLength ir) "variable" (← sourceOf arg)])
        else if ← isNodeType argType then
          let local_ ← match ← lookupNode ctx arg.consumeMData with
            | some local_ => pure local_
            | none =>
                unless owned do
                  throwError "a borrowed argument of a recursive type must be a variable: {source}"
                if arg.consumeMData.getAppFn.constName == ctx.self then
                  if let some (selfIndex, depth) := ctx.selfCall then
                    return ([⟨.u64, .get (← translateSelfCall ctx arg.consumeMData selfIndex depth)⟩],
                      [mkHint ⟨[], offset⟩ 1 "recursive call result" (← sourceOf arg)])
                let some callee := ctx.callees.lookup arg.consumeMData.getAppFn.constName
                  | throwError "an owned argument of a recursive type must be a variable or a call: {source}"
                let [(result, .u64)] ← translateCall ctx arg.consumeMData callee
                  | throwError "a call argument of a recursive type must come from a call with one result: {source}"
                pure result
          let ir : IRExpr .u64 := .get local_
          pure ([(⟨.u64, ir⟩ : (type : ScalarType) × IRExpr type)],
            [mkHint ⟨[], offset⟩ (exprLength ir) "variable" (← sourceOf arg)])
        else if ← isUInt64 argType then
          let (ir, irHints) ← translateValue ctx ⟨[], offset⟩ arg
          pure ([⟨.u64, ir⟩], irHints)
        else if ← isFloat argType then
          let (ir, irHints) ← translateFloat ctx ⟨[], offset⟩ arg
          pure ([⟨.f64, ir⟩], irHints)
        else if (← isWordType argType) || (← isTupleType argType) then
          translateComponents ctx ⟨[], offset⟩ arg argType
        else throwError "a call argument must be a word, a float, an array, or a user type: {source}"
      if values.isEmpty then throwError "an argument has no components: {source}"
      for value in values do
        args := args.push value
        offset := offset + exprLength value.2
      hints := hints ++ argHints.toArray
    let types ← resultTypes (← inferType term)
    let results ← match dests? with
      | some dests => pure (dests.zip types)
      | none => types.mapM fun type => return (← fresh type "call result", type)
    -- A call from a recursive body shares its depth: a recursive callee's internal function
    -- runs at the caller's depth plus one, and any other callee is a leaf, one bounded frame
    -- on top of the recursion.
    let name := term.getAppFn.constName
    let (callIndex, callArgs) ← match ctx.selfCall with
      | none => pure (index, args)
      | some (_, depth) =>
          match ctx.internals.lookup name with
          | some internal => pure (internal, args.push ⟨.u64, .bin .add (.get depth) (.const 1)⟩)
          | none => do
              unless ctx.leaves.contains name do
                throwError "a recursive definition may call only recursive definitions and definitions that call none and hold at most {recursiveFrameLimit} values: {source}"
              pure (index, args)
    let stmt := Project.IR.Stmt.call callIndex callArgs.toList (results.map (·.1))
    pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "call" source :: hints.toList)
    moved.forM markMoved
    return results

  /-- Translates a recursive call `term` in the internal function of a definition that is
  not tail recursive to a call of the internal function, at `index`, with the depth local
  plus one as the last argument, which leaves the word result in a fresh local.  A recursive
  call may appear only where its statement runs exactly when its value is needed: at the top
  of the body or in a branch of a match on a value of a recursive type. -/
  partial def translateSelfCall (ctx : Ctx) (term : Lean.Expr) (index depth : Nat) :
      CompileM Nat := do
    let source ← sourceOf term
    unless ctx.foldable do
      throwError "a recursive call may appear only at the top of the body or in a branch of a match on a value of a recursive type: {source}"
    -- An owned position receives an owned value at its last use, which the call moves.
    let mut moved := []
    let nodeArgs ← term.getAppArgs.toList.filterM fun arg => do isNodeType (← inferType arg)
    for position in (ctx.owners.lookup ctx.self).getD [] do
      let some arg := term.getAppArgs[position]?
        | throwError "a recursive call must pass every parameter: {source}"
      let arg := arg.consumeMData
      unless arg.isFVar && ctx.owned.contains arg &&
          (nodeArgs.map (occurrences arg.fvarId! ·)).sum == 1 do
        throwError "an owned parameter of a recursive call must receive an owned value at its last use: {source}"
      moved := arg :: moved
    let mut args : Array ((type : ScalarType) × IRExpr type) := #[]
    let mut hints := #[]
    let mut offset := 0
    for h : position in [:term.getAppArgs.size] do
      let arg := term.getAppArgs[position]
      -- The earlier arguments are read where the call runs, after this argument's statements.
      let earlier := args.toList.flatMap fun value => readLocals value.2
      let (ir, argHints) ← afterReads ctx earlier do
        match ← lookupNode ctx arg.consumeMData with
        | some local_ => do
            pure ((.get local_ : IRExpr .u64),
              [mkHint ⟨[], offset⟩ 1 "variable" (← sourceOf arg)])
        | none => do
            unless ← isWordType (← inferType arg) do
              throwError "a recursive call's argument must be a word or a field of a recursive type: {source}"
            translateValue ctx ⟨[], offset⟩ arg
      args := args.push ⟨.u64, ir⟩
      hints := hints ++ argHints.toArray
      offset := offset + exprLength ir
    let next : IRExpr .u64 := .bin .add (.get depth) (.const 1)
    args := args.push ⟨.u64, next⟩
    let result ← fresh .u64 "recursive call result"
    let stmt := Project.IR.Stmt.call index args.toList [result]
    pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "recursive call" source :: hints.toList)
    moved.forM markMoved
    return result

  /-- The results read from `components`, or copied into the locals `dests?` first. -/
  partial def resultsIn (components : List (Nat × ScalarType)) (dests? : Option (List Nat))
      (source : String) : CompileM (List (Σ type, IRExpr type) × List (List Hint)) := do
    let some dests := dests? | return (components.map readLocal, components.map fun _ => [])
    for ((component, type), dest) in components.zip dests do
      let ⟨_, ir⟩ := readLocal (component, type)
      let stmt := Project.IR.Stmt.assign dest ir
      pushStmt stmt [mkHint ⟨[], 0⟩ (stmtLength stmt) "result copy" source]
    return ((dests.zip (components.map (·.2))).map readLocal, dests.map fun _ => [])

  /-- Translates a case split on an enumeration with a pair or structure result to a chain
  of `if` statements whose branches leave the result in the locals `dests?`, or in fresh
  locals, and returns expressions that read them. -/
  partial def translateCases (ctx : Ctx) (term discriminant : Lean.Expr)
      (alternatives : List CaseAlt) (type : Lean.Expr) (dests? : Option (List Nat)) :
      CompileM (List (Σ type, IRExpr type) × List (List Hint)) := do
    let source ← sourceOf term
    let types ← resultTypes type
    let dests ← match dests? with
      | some dests => pure dests
      | none => types.mapM fun type => fresh type "result"
    let (ctx, d, slots, dHints) ← caseDiscriminant ctx ⟨[], 0⟩ discriminant alternatives
    let saved := (← get).consumed
    let (stmt, hints) ← caseChain ctx saved d 0 (slots.zip alternatives) type dests
    modify fun p => { p with consumed := saved ++ ctx.owned }
    pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "case split" source :: dHints ++ hints)
    return ((dests.zip types).map readLocal, dests.map fun _ => [])

  /-- The `if` chain of `translateCases` from alternative `index` on.  Each branch releases
  the owned parameters that it does not move. -/
  partial def caseChain (ctx : Ctx) (saved : List Lean.Expr) (d : IRExpr .u64) (index : Nat) :
      List (List (Nat × ScalarType) × CaseAlt) → Lean.Expr → List Nat →
        CompileM (Project.IR.Stmt × List Hint)
    | [], _, _ => throwError "a case split needs an alternative"
    | (slots, alternative) :: rest, type, dests => do
        modify fun p => { p with consumed := saved }
        let (_, stmts, hints) ← withBlock do
          let results ← caseBody ctx slots alternative fun ctx body =>
            translateResults { ctx with temporaries := false, reuse := none } body type dests
          releaseUnmoved ctx
          return results
        if rest.isEmpty then return (seqAll stmts, hints)
        let condition : IRExpr .bool := .eq d (.const (UInt64.ofNat index))
        let (elseStmt, elseHints) ← caseChain ctx saved d (index + 1) rest type dests
        let branchAt := exprLength condition
        return (.ite condition (seqAll stmts) elseStmt,
          hints.map (Hint.within [branchAt, 0]) ++ elseHints.map (Hint.within [branchAt, 1]))

  /-- Translates a conditional result whose branches build arrays to a statement
  `if` whose branches leave the results in the locals `dests?`, or in fresh
  locals, and returns expressions that read them. -/
  partial def translateResultBranch (ctx : Ctx) (term condition thenTerm elseTerm type : Lean.Expr)
      (dests? : Option (List Nat) := none) :
      CompileM (List (Σ type, IRExpr type) × List (List Hint)) := do
    let source ← sourceOf term
    let types ← resultTypes type
    let dests ← match dests? with
      | some dests => pure dests
      | none => types.mapM fun type => fresh type "result"
    let (c, cHints) ← translateCondition ctx ⟨[], 0⟩ condition
    let branchCtx := { ctx with temporaries := false, reuse := none }
    -- Each branch releases the owned parameters that it does not move.
    let saved := (← get).consumed
    let (_, thenStmts, thenHints) ← withBlock do
      let results ← translateResults branchCtx thenTerm type dests
      releaseUnmoved ctx
      return results
    modify fun p => { p with consumed := saved }
    let (_, elseStmts, elseHints) ← withBlock do
      let results ← translateResults branchCtx elseTerm type dests
      releaseUnmoved ctx
      return results
    modify fun p => { p with consumed := saved ++ ctx.owned }
    let stmt := Project.IR.Stmt.ite c (seqAll thenStmts) (seqAll elseStmts)
    let branchAt := exprLength c
    pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "result branch" source :: cHints ++
      thenHints.map (Hint.within [branchAt, 0]) ++ elseHints.map (Hint.within [branchAt, 1]))
    return ((dests.zip types).map readLocal, dests.map fun _ => [])

  /-- Translates the array literal `term` with `elements` to an allocation and
  stores into local `dst?` or a fresh local, which it returns.  Folds in the
  elements run first. -/
  partial def translateArrayLiteral (ctx : Ctx) (term : Lean.Expr) (elements : List Lean.Expr)
      (dst? : Option Nat := none) : CompileM Nat := do
    let mut values : Array (IRExpr .u64) := #[]
    let mut valueHints : Array (List Hint) := #[]
    for element in elements do
      let (value, hints) ← afterReads ctx (values.toList.flatMap readLocals)
        (translateValue ctx ⟨[], 0⟩ element)
      values := values.push value
      valueHints := valueHints.push hints
    let before ← get
    let temp := dst?.getD before.next
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
      vars := if dst?.isSome then before.vars else before.vars.push .u64
      names := if dst?.isSome then before.names else before.names.push ("array", temp) }
    return temp
end

/-- Translates the body of a tail-recursive definition, in tail position, to a
statement that either updates the parameters for the next iteration or stores
the result and sets `done`. -/
partial def translateTail (ctx : Ctx) (loc : Loc) (term : Lean.Expr) :
    CompileM (Project.IR.Stmt × List Hint) := do
  let term := term.consumeMData
  if let some unfolded ← unfoldMatcher? term then
    return ← translateTail ctx loc unfolded
  let source ← sourceOf term
  -- A match on a value of a recursive type: the pointer is tested against 0, and the
  -- record's branch loads its fields into fresh locals.
  if let some (discriminant, alternatives) ← userCases? term then
    if let some ptr ← lookupNode ctx discriminant.consumeMData then
      let [first, second] := alternatives
        | throwError "a match on a recursive type must have two constructors: {source}"
      let (nullAlt, recordAlt, nullFirst) ← match first.fields, second.fields with
        | [], _ :: _ => pure (first, second, true)
        | _ :: _, [] => pure (second, first, false)
        | _, _ => throwError "a match on a recursive type needs one constructor without fields and one with fields: {source}"
      let condition : IRExpr .bool := if nullFirst then .eq (.get ptr) (.const 0)
        else .ne (.get ptr) (.const 0)
      let branch := loc.skip (exprLength condition)
      let nullLoc := branch.inside (some (if nullFirst then 0 else 1))
      let recordLoc := branch.inside (some (if nullFirst then 1 else 0))
      let (nullStmt, nHints) ← translateTail ctx nullLoc (nullAlt.body [])
      let (recordStmt, rHints) ← bindRecordFields ctx ptr (fun ctx xs loads => do
          let here := recordLoc.skip (loads.map stmtLength).sum
          let (s, hs) ← translateTail ctx here (recordAlt.body xs)
          let loadHints := (List.range loads.length).zip loads |>.map fun (j, load) =>
            mkHint (recordLoc.skip ((loads.take j).map stmtLength).sum) (stmtLength load)
              "field load" source
          return (seqAll (loads ++ [s]), loadHints ++ hs))
        0 recordAlt.fields [] []
      let (a, b) := if nullFirst then (nullStmt, recordStmt) else (recordStmt, nullStmt)
      let stmt : Project.IR.Stmt := .ite condition a b
      return (stmt, mkHint loc (stmtLength stmt) "node match" source :: nHints ++ rHints)
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
          let (value, valueHints) ← match ← lookupNode ctx args[i]!.consumeMData with
            | some local_ => pure (.get local_, [])
            | none => translateValue ctx here args[i]!
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

/-- Whether every call of `self` in `term` is in tail position: the whole term, a branch of
an `if` or of a case split, or the body of a `let`, with arguments that do not call `self`. -/
partial def tailOnly (self : Name) (term : Lean.Expr) : MetaM Bool := do
  let term := term.consumeMData
  let mentions (e : Lean.Expr) : Bool := (e.find? fun x => x.isConstOf self).isSome
  if let some unfolded ← unfoldMatcher? term then return ← tailOnly self unfolded
  if let (``ite, #[_, condition, _, a, b]) := term.getAppFnArgs then
    return !mentions condition && (← tailOnly self a) && (← tailOnly self b)
  if let some (discriminant, alternatives) ← userCases? term then
    if mentions discriminant then return false
    for alternative in alternatives do
      let ok ← withFieldVars alternative.fields [] fun xs => tailOnly self (alternative.body xs)
      unless ok do return false
    return true
  if let .letE name type value body _ := term then
    if mentions value then return false
    return ← withLocalDeclD name type fun x => tailOnly self (body.instantiate1 x)
  if term.getAppFn.isConstOf self then
    return !term.getAppArgs.any mentions
  return !mentions term
where
  withFieldVars {γ : Type} : List Lean.Expr → List Lean.Expr → (List Lean.Expr → MetaM γ) →
      MetaM γ
    | [], xs, k => k xs
    | field :: fields, xs, k => withLocalDeclD `field field fun x => withFieldVars fields (xs ++ [x]) k

/-- The unfolding equation's parameters and right side for `declName`. -/
def unfoldedBody {γ : Type} (declName : Name) (k : Array Lean.Expr → Lean.Expr → MetaM γ) :
    MetaM γ := do
  let some equation ← getUnfoldEqnFor? declName (nonRec := true)
    | throwError "{declName} has no unfolding equation"
  forallTelescope (← getConstInfo equation).type fun params eq => do
    let some (_, _, body) := eq.eq?
      | throwError "unexpected unfolding equation for {declName}"
    k params body

/-- Whether `declName` calls itself other than in tail position, so that it compiles to an
entry function and an internal function with a depth parameter. -/
def needsInternal (declName : Name) : MetaM Bool :=
  unfoldedBody declName fun _ body => do
    unless (body.find? fun e => e.isConstOf declName).isSome do return false
    return !(← tailOnly declName body)

/-- The depth at which an internal function traps at `unreachable`. -/
def recursionDepthLimit : UInt64 := 1000

/-- Compiles the definition `declName`, whose parameters are `UInt64`, `Float`,
`Array UInt64`, or `Array Float` and whose result is `UInt64`, `Float`, or an
`Array UInt64` literal, to an IR function with hints.  The
compiler reads the definition's unfolding equation, so a recursive call appears
as a call of `declName`.  A definition without recursive calls becomes a prelude
of folds and a result expression; a definition whose recursive calls are all in
tail position becomes a loop.  An array parameter is owned when the result term, after
the `let`s, moves it, as the left operand of `++` or as an argument at an owned position
of a callee in `owners`, and contains it nowhere else.  A parameter of a recursive type is
owned when the result term returns it or places it or one of its children in a constructor.
The compiler returns the positions of the owned parameters. -/
def compileDefinition (declName : Name) (callees : List (Name × Nat) := [])
    (owners : List (Name × List Nat) := []) (internal : Option Nat := none)
    (internals : List (Name × Nat) := []) (leaves : List Name := []) :
    MetaM (Func × Hints × List Nat × Option (Func × Hints)) := do
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
    let mut lists := []
    let mut nodes := []
    let mut tuples := []
    -- The WebAssembly parameters: one per word, float, or array, and one per component of a
    -- structure, in order.
    let mut paramTypes : Array ScalarType := #[]
    let mut paramNames : Array (String × Nat) := #[]
    for h : i in [:params.size] do
      let type ← inferType params[i]
      let name := (← params[i].fvarId!.getUserName).eraseMacroScopes.toString
      let index := paramTypes.size
      if ← isUInt64 type then
        words := (params[i], index) :: words
        paramTypes := paramTypes.push .u64
      else if ← isFloat type then
        floats := (params[i], index) :: floats
        paramTypes := paramTypes.push .f64
      else if ← isUInt64Array type then
        arrays := (params[i], index) :: arrays
        paramTypes := paramTypes.push .u64
      else if ← isFloatArray type then
        floatArrays := (params[i], index) :: floatArrays
        paramTypes := paramTypes.push .u64
      else if ← isUInt64List type then
        lists := (params[i], index) :: lists
        paramTypes := paramTypes.push .u64
      else if ← isNodeType type then
        nodes := (params[i], index) :: nodes
        paramTypes := paramTypes.push .u64
      else if ← isWordType type then
        words := (params[i], index) :: words
        paramTypes := paramTypes.push .u64
      else if ← isTupleType type then
        let types ← stateTypes type
        tuples := (params[i], types.zipIdx.map fun (type, k) => (index + k, type)) :: tuples
        paramTypes := paramTypes ++ types.toArray
        paramNames := paramNames ++ (List.range (types.length - 1)).toArray.map
          fun k => (s!"{name}.{k}", index + k)
        paramNames := paramNames.push (s!"{name}.{types.length - 1}", index + types.length - 1)
        continue
      else
        throwError "parameter {params[i]} of {declName} is not UInt64, Float, an array, a list of words, or a user type"
      paramNames := paramNames.push (name, index)
    let resultType ← inferType body
    let arrayResult ← isArray resultType
    let floatResult ← isFloat resultType
    let pairResult ← isTupleType resultType
    let listResult := (← isUInt64List resultType) || (← isNodeType resultType)
    unless arrayResult || floatResult || pairResult || listResult || (← isWordType resultType) do
      throwError "the result of {declName} is not UInt64, Float, an array, a list of words, a pair, or a user type"
    let recursive := (body.find? fun e => e.isConstOf declName).isSome
    if recursive && !(← tailOnly declName body) then
      let some index := internal
        | throwError "{declName} calls itself other than in tail position; compile it in a module list, which adds its internal function"
      let treeResult ← isNodeType resultType
      unless arrays.isEmpty && floatArrays.isEmpty && lists.isEmpty && floats.isEmpty &&
          tuples.isEmpty && ((← isWordType resultType) || treeResult) do
        throwError "a recursive definition may take only UInt64 and values of recursive types, and return only UInt64 or a value of a recursive type: {declName}"
      -- A definition that returns a tree owns the parameters in the greatest fixed point of the
      -- mode rule: every parameter of a recursive type starts owned at the self-calls, and each
      -- round keeps those that the body still moves.  A parameter that every self-call passes
      -- unchanged in its own position, and that the body moves nowhere else, is borrowed first:
      -- the calls share it.  A definition that returns a word owns none, since it could not
      -- release them.
      let positionsOf (owned : List Lean.Expr) : List Nat :=
        (List.range params.size).filter fun i => owned.contains params[i]!
      let nodeParams := nodes.map (·.1)
      let mut owned := []
      if treeResult then
        for h : i in [:params.size] do
          let p := params[i]
          unless nodeParams.contains p do continue
          let args ← selfArgs declName i body
          let others := (positionsOf nodeParams).filter (· != i)
          let sites ← moveSites ((declName, others) :: owners) nodeParams body
          unless !args.isEmpty && args.all (· == p) && !sites.contains p do
            owned := owned ++ [p]
      for _ in [:nodeParams.length + 1] do
        let sites ← moveSites ((declName, positionsOf owned) :: owners) nodeParams body
        let next := owned.filter sites.contains
        if next.length == owned.length then break
        owned := next
      -- The internal function: the parameters and the depth, a guard, and the body.
      let depth := paramTypes.size
      let ctx : Ctx :=
        { self := declName, params, words, floats, arrays, floatArrays, nodes, foldable := true,
          selfCall := some (index, depth), owned, callees := callees.filter (·.1 != declName),
          internals, leaves, owners := (declName, positionsOf owned) :: owners }
      let guard : Project.IR.Stmt :=
        .ite (.ltU (.const (recursionDepthLimit - 1)) (.get depth)) .abort .skip
      let ((results, resultHints), prelude) ←
        (translateResults ctx body resultType).run { base := depth + 1 }
      unless owned.all prelude.consumed.contains do
        throwError "an owned parameter of {declName} must move on every path; releasing it is not supported yet"
      unless prelude.temporaries.all (prelude.consumed.contains ·.1) do
        throwError "a temporary of {declName} must move on every path; releasing it in a recursive definition is not supported yet"
      let stmts := guard :: prelude.stmts.toList
      let bodyLength := (stmts.map stmtLength).sum
      let (_, shifted) := (results.zip resultHints).foldl (init := (bodyLength, []))
        fun (offset, hints) (⟨_, ir⟩, own) =>
          (offset + exprLength ir, hints ++ own.map (Hint.shift offset))
      let rec_ : Func :=
        { params := paramTypes.toList ++ [.u64], vars := prelude.vars.toList
          body := seqAll stmts, results }
      if rec_.params.length + rec_.vars.length + rec_.width > recursiveFrameLimit then
        throwError "the internal function of {declName} holds more than {recursiveFrameLimit} values in its frame"
      let recHints : Hints :=
        { locals := paramNames.toList ++ [("depth", depth)] ++ prelude.names.toList
          nodes := mkHint ⟨[], 0⟩ (stmtLength guard) "depth guard" (← sourceOf body) ::
            prelude.hints.toList.map (Hint.shift (stmtLength guard)) ++ shifted }
      -- The entry: one call of the internal function at depth 0.
      let entryArgs : List ((type : ScalarType) × IRExpr type) :=
        (List.range paramTypes.size).map (fun i => ⟨.u64, .get i⟩) ++ [⟨.u64, .const 0⟩]
      let entryCall : Project.IR.Stmt := .call index entryArgs [paramTypes.size]
      let entry : Func :=
        { params := paramTypes.toList, vars := [.u64], body := entryCall
          results := [⟨.u64, .get paramTypes.size⟩] }
      let entryHints : Hints :=
        { locals := paramNames.toList ++ [("result", paramTypes.size)]
          nodes := [mkHint ⟨[], 0⟩ (stmtLength entryCall) "recursive entry" (← sourceOf body)] }
      return (entry, entryHints, positionsOf owned, some (rec_, recHints))
    if recursive then
      unless arrays.isEmpty && floatArrays.isEmpty && lists.isEmpty && floats.isEmpty &&
          tuples.isEmpty &&
          !arrayResult && !floatResult && !pairResult && !listResult do
        throwError "a recursive definition may take only UInt64 and values of recursive types, and return only UInt64: {declName}"
      let ctx : Ctx :=
        { self := declName, params, words, floats, arrays, floatArrays, nodes, foldable := false }
      -- The loop is the first instruction of the body: a block holding a loop.
      let loopBody := ((({ prefix_ := [], index := 0 } : Loc).inside none).inside none)
      let condition : IRExpr .bool := .eq (.get ctx.done) (.const 0)
      let ((step, stepHints), prelude) ← (translateTail ctx
        (loopBody.skip (exprLength condition + 2)) body).run
          { base := ctx.params.size + ctx.vars }
      unless prelude.stmts.isEmpty do
        throwError "a recursive definition may not contain a value that needs statements before it: {declName}"
      let loop : Project.IR.Stmt := .while condition step
      let loopHint := mkHint { prefix_ := [], index := 0 } (stmtLength loop)
        "tail-recursion-loop" (← sourceOf body)
      let resultHint := mkHint { prefix_ := [], index := 1 } 1 "result" "result"
      let names := paramNames.toList ++
        [("result", ctx.result), ("done", ctx.done)] ++
        (paramNames.toList.map fun (name, i) => (s!"next {name}", ctx.temp i)) ++
        prelude.names.toList
      let func : Func :=
        { params := paramTypes.toList, vars := List.replicate ctx.vars .u64 ++ prelude.vars.toList,
          body := loop, results := [⟨.u64, .get ctx.result⟩] }
      return (func, { locals := names, nodes := loopHint :: stepHints ++ [resultHint] }, [], none)
    else
      let movable := (arrays ++ floatArrays ++ nodes).map (·.1)
      let sites ← moveSites owners movable body
      let owned := movable.filter sites.contains
      let ctx : Ctx :=
        { self := declName, params, words, floats, arrays, floatArrays, lists, nodes, tuples,
          callees, owners, owned, foldable := true }
      let ((results, resultHints), prelude) ←
        (do
          let (results, resultHints) ← translateResults ctx body resultType
          let consumed := (← get).consumed
          let temporaries := (← get).temporaries.filter
            fun (t : Lean.Expr × Nat × String) => !consumed.contains t.1
          if temporaries.isEmpty && owned.all consumed.contains then
            return (results, resultHints)
          -- With temporaries or owned parameters to release, each result is stored before
          -- the releases, so that no result reads a released array.
          let mut stored := #[]
          for (⟨resultType, ir⟩, own) in results.zip resultHints do
            let local_ ← fresh resultType "result"
            let stmt := Project.IR.Stmt.assign local_ ir
            pushStmt stmt (mkHint ⟨[], 0⟩ (stmtLength stmt) "result" "result" :: own)
            stored := stored.push (readLocal (local_, resultType))
          releaseUnmoved ctx
          for (_, local_, source) in temporaries.reverse do
            let stmt := Project.IR.Stmt.release local_
            pushStmt stmt [mkHint ⟨[], 0⟩ (stmtLength stmt) "release temporary" source]
          return (stored.toList, stored.toList.map fun _ => [])).run { base := paramTypes.size }
      -- Each result's code follows the body and the earlier results.
      let (_, shifted) := (results.zip resultHints).foldl (init := (prelude.length, []))
        fun (offset, hints) (⟨_, ir⟩, own) =>
          (offset + exprLength ir, hints ++ own.map (Hint.shift offset))
      let func : Func :=
        { params := paramTypes.toList, vars := prelude.vars.toList
          body := seqAll prelude.stmts.toList, results }
      let hints : Hints :=
        { locals := paramNames.toList ++ prelude.names.toList
          nodes := prelude.hints.toList ++ shifted }
      let positions := (List.range params.size).filter fun i => owned.contains params[i]!
      return (func, hints, positions, none)

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
  | _, .ofBits operand => mkApp (mkConst ``Project.IR.Expr.ofBits) (irToExpr operand)
  | _, .toBits operand => mkApp (mkConst ``Project.IR.Expr.toBits) (irToExpr operand)
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

/-- The term of a list of typed IR expressions. -/
def typedToExpr (list : List ((type : ScalarType) × IRExpr type)) : Lean.Expr :=
  let entryType := mkApp2 (mkConst ``Sigma [Level.zero, Level.zero]) (mkConst ``ScalarType)
    (mkConst ``Project.IR.Expr)
  list.foldr (init := mkApp (mkConst ``List.nil [Level.zero]) entryType)
    fun entry rest => mkApp3 (mkConst ``List.cons [Level.zero]) entryType
      (mkApp4 (mkConst ``Sigma.mk [Level.zero, Level.zero]) (mkConst ``ScalarType)
        (mkConst ``Project.IR.Expr) (toExpr entry.1) (irToExpr entry.2)) rest

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
  | .call func args results =>
      mkApp3 (mkConst ``Project.IR.Stmt.call) (toExpr func) (typedToExpr args) (toExpr results)
  | .abort => mkConst ``Project.IR.Stmt.abort

def funcToExpr (func : Func) : Lean.Expr :=
  mkApp4 (mkConst ``Func.mk) (toExpr func.params) (toExpr func.vars) (stmtToExpr func.body)
    (typedToExpr func.results)

end Project.Compiler
