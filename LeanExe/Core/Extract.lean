import LeanExe.Core.Native
import Lean.Meta.Eqns
import Lean.Meta.Tactic.FunInd

namespace LeanExe.Core.Extract

open Lean Meta Elab
open LeanExe.Wasm.ScalarDescriptor (U64Op)

private abbrev ScalarExpr := LeanExe.Wasm.ScalarDescriptor.Expr
private abbrev ScalarCond := LeanExe.Wasm.ScalarDescriptor.Cond

private structure Entry where
  name : Name
  equation : Name := .anonymous
  function : Option Function := none

private structure ExtractState where
  entries : Array Entry := #[]

private abbrev ExtractM := StateT ExtractState MetaM
private abbrev Bindings := Array (Expr × ScalarExpr)

private def runScoped (action : MetaM (α × ExtractState)) : ExtractM α := do
  let (result, state) ← action
  set state
  return result

private def sequence (a b : Stmt) : Stmt :=
  match a, b with
  | .skip, b => b
  | a, .skip => a
  | a, b => .seq a b

private def primitive? (name : Name) : Option U64Op :=
  if name == ``UInt64.add || name == ``HAdd.hAdd then some .add else
  if name == ``UInt64.sub || name == ``HSub.hSub then some .sub else
  if name == ``UInt64.mul || name == ``HMul.hMul then some .mul else
  if name == ``UInt64.div || name == ``HDiv.hDiv then some .divU else
  if name == ``UInt64.mod || name == ``HMod.hMod then some .remU else
  if name == ``UInt64.land || name == ``AndOp.and || name == ``HAnd.hAnd then some .bitAnd else
  if name == ``UInt64.lor || name == ``OrOp.or || name == ``HOr.hOr then some .bitOr else
  if name == ``UInt64.xor || name == ``XorOp.xor || name == ``HXor.hXor then some .bitXor else
  if name == ``UInt64.shiftLeft || name == ``HShiftLeft.hShiftLeft then some .shiftLeft else
  if name == ``UInt64.shiftRight || name == ``HShiftRight.hShiftRight then some .shiftRight else none

private def operands (expression : Expr) : MetaM (Expr × Expr) := do
  let args := expression.getAppArgs
  if args.size < 2 then throwError "expected two operands: {expression}"
  return (args[args.size - 2]!, args[args.size - 1]!)

mutual
  private partial def ensureFunction (name : Name) : ExtractM Nat := do
    if let some index := (← get).entries.findIdx? (·.name == name) then return index
    let info ← getConstInfo name
    if info.isUnsafe || info.isPartial then
      throwError "The core compiler requires safe, total definitions: {name}"
    unless info.levelParams.isEmpty do
      throwError "The core compiler requires monomorphic definitions: {name}"
    let some equation ← getUnfoldEqnFor? name (nonRec := true)
      | throwError "No kernel-checked unfolding equation for {name}"
    let index := (← get).entries.size
    modify fun state => { state with entries := state.entries.push { name, equation } }
    let equationInfo ← getConstInfo equation
    let state ← get
    let function ← runScoped <| forallTelescope equationInfo.type fun args equality => do
      for arg in args do
        unless ← isDefEq (← inferType arg) (mkConst ``UInt64) do
          throwError "Every runtime parameter must be UInt64: {name}"
      let some (_, _, rhs) := equality.eq?
        | throwError "Expected an unfolding equality for {name}"
      unless ← isDefEq (← inferType rhs) (mkConst ``UInt64) do
        throwError "The result must be UInt64: {name}"
      let bindings := args.mapIdx fun i arg => (arg, LeanExe.Wasm.ScalarDescriptor.Expr.get i)
      let ((body, result, next), state) ← (lower bindings rhs args.size).run state
      return ({ params := args.size, locals := next - args.size, body, result }, state)
    modify fun state =>
      { state with entries := state.entries.modify index fun entry => { entry with function := some function } }
    return index

  private partial def lower (bindings : Bindings) (expression : Expr) (next : Nat) :
      ExtractM (Stmt × ScalarExpr × Nat) := do
    let expression := expression.consumeMData
    if let some (_, value) := bindings.find? (·.1 == expression) then
      return (.skip, value, next)
    if let .letE name type value body _ := expression then
      unless ← isDefEq type (mkConst ``UInt64) do
        throwError "Only UInt64 runtime let bindings are supported: {expression}"
      let (first, value, next) ← lower bindings value next
      let slot := next
      let state ← get
      let (second, result, next) ← runScoped <| withLocalDeclD name type fun boundValue =>
        (lower (bindings.push (boundValue, .get slot)) (body.instantiate1 boundValue) (slot + 1)).run state
      return (sequence (sequence first (.assign slot value)) second, result, next)
    let fn := expression.getAppFn
    let args := expression.getAppArgs
    if fn.isConstOf ``OfNat.ofNat && args.size == 3 then
      if let .lit (.natVal value) := args[1]! then return (.skip, .const value, next)
    if fn.isConstOf ``UInt64.ofNat && args.size == 1 then
      if let .lit (.natVal value) := args[0]! then return (.skip, .const value, next)
    if (fn.isConstOf ``ite || fn.isConstOf ``dite) && args.size == 5 then
      let (testCode, test, next) ← lowerCondition bindings args[1]! next
      let slot := next
      let (yes, yesValue, next) ← lowerArm bindings args[3]! (slot + 1) (fn.isConstOf ``dite)
      let (no, noValue, next) ← lowerArm bindings args[4]! next (fn.isConstOf ``dite)
      return (sequence testCode (.branch test
        (sequence yes (.assign slot yesValue)) (sequence no (.assign slot noValue))), .get slot, next)
    if let .const name _ := fn then
      if let some op := primitive? name then
        let (a, b) ← operands expression
        let (first, a, next) ← lower bindings a next
        let (second, b, next) ← lower bindings b next
        return (sequence first second, .bin op a b, next)
      if name == ``Id.run || name == ``Pure.pure then
        if let some value := args.back? then
          if ← isDefEq (← inferType value) (mkConst ``UInt64) then
            return ← lower bindings value next
      if name == ``Bind.bind then
        if args.size ≥ 2 then
          let value := args[args.size - 2]!
          let continuation := args[args.size - 1]!
          let normalized ← whnf (mkApp continuation value)
          if ← isDefEq (← inferType normalized) (mkConst ``UInt64) then
            return ← lower bindings normalized next
      let callee ← ensureFunction name
      let (code, inputs, next) ← lowerArguments bindings args.toList next
      return (sequence code (.call next callee inputs), .get next, next + 1)
    let reduced ← withReducible <| whnf expression
    if reduced != expression then return ← lower bindings reduced next
    throwError "Unsupported core expression: {expression}"

  private partial def lowerArm (bindings : Bindings) (expression : Expr) (next : Nat)
      (dependent : Bool) : ExtractM (Stmt × ScalarExpr × Nat) := do
    if dependent then
      let state ← get
      runScoped <| lambdaTelescope expression fun _ body => (lower bindings body next).run state
    else lower bindings expression next

  private partial def lowerArguments (bindings : Bindings) (arguments : List Expr) (next : Nat) :
      ExtractM (Stmt × List ScalarExpr × Nat) := do
    match arguments with
    | [] => return (.skip, [], next)
    | arg :: rest =>
      let (first, value, next) ← lower bindings arg next
      let (second, values, next) ← lowerArguments bindings rest next
      return (sequence first second, value :: values, next)

  private partial def lowerCondition (bindings : Bindings) (expression : Expr) (next : Nat) :
      ExtractM (Stmt × ScalarCond × Nat) := do
    let expression := expression.consumeMData
    let fn := expression.getAppFn
    let args := expression.getAppArgs
    if fn.isConstOf ``True then return (.skip, .true, next)
    if fn.isConstOf ``False then return (.skip, .false, next)
    if fn.isConstOf ``Not || fn.isConstOf ``Bool.not then
      let (code, test, next) ← lowerCondition bindings args.back! next
      return (code, .not test, next)
    if fn.isConstOf ``Eq && args.size == 3 && args[0]!.isConstOf ``Bool then
      return ← lowerCondition bindings args[1]! next
    if let .const name _ := fn then
      let (a, b) ← operands expression
      let (first, left, next) ← lower bindings a next
      let (second, right, next) ← lower bindings b next
      let test ←
        if name == ``Eq || name == ``BEq.beq then pure (.eq left right) else
        if name == ``Ne || name == ``bne then pure (.ne left right) else
        if name == ``LT.lt || name == ``UInt64.lt then pure (.ltU left right) else
        if name == ``LE.le || name == ``UInt64.le then pure (.leU left right) else
        if name == ``GT.gt then pure (.ltU right left) else
        if name == ``GE.ge then pure (.leU right left) else
          throwError "Unsupported core comparison: {expression}"
      return (sequence first second, test, next)
    throwError "Unsupported core condition: {expression}"
end

private def quoteOp (op : U64Op) : Expr :=
  mkConst <| match op with
  | .add => ``U64Op.add | .sub => ``U64Op.sub | .mul => ``U64Op.mul
  | .divU => ``U64Op.divU | .remU => ``U64Op.remU
  | .bitAnd => ``U64Op.bitAnd | .bitOr => ``U64Op.bitOr | .bitXor => ``U64Op.bitXor
  | .shiftLeft => ``U64Op.shiftLeft | .shiftRight => ``U64Op.shiftRight

private def quoteList (type : Expr) (values : List Expr) : Expr :=
  values.foldr (fun value rest => mkApp3 (mkConst ``List.cons [.zero]) type value rest)
    (mkApp (mkConst ``List.nil [.zero]) type)

mutual
  private def quoteExpr : ScalarExpr → Expr
    | .get n => mkApp (mkConst ``LeanExe.Wasm.ScalarDescriptor.Expr.get) (mkNatLit n)
    | .const n => mkApp (mkConst ``LeanExe.Wasm.ScalarDescriptor.Expr.const) (mkNatLit n)
    | .bin op a b => mkApp3 (mkConst ``LeanExe.Wasm.ScalarDescriptor.Expr.bin) (quoteOp op) (quoteExpr a) (quoteExpr b)
    | .ite c a b => mkApp3 (mkConst ``LeanExe.Wasm.ScalarDescriptor.Expr.ite) (quoteCond c) (quoteExpr a) (quoteExpr b)
  private def quoteCond : ScalarCond → Expr
    | .true => mkConst ``LeanExe.Wasm.ScalarDescriptor.Cond.true
    | .false => mkConst ``LeanExe.Wasm.ScalarDescriptor.Cond.false
    | .eq a b => mkApp2 (mkConst ``LeanExe.Wasm.ScalarDescriptor.Cond.eq) (quoteExpr a) (quoteExpr b)
    | .ne a b => mkApp2 (mkConst ``LeanExe.Wasm.ScalarDescriptor.Cond.ne) (quoteExpr a) (quoteExpr b)
    | .ltU a b => mkApp2 (mkConst ``LeanExe.Wasm.ScalarDescriptor.Cond.ltU) (quoteExpr a) (quoteExpr b)
    | .leU a b => mkApp2 (mkConst ``LeanExe.Wasm.ScalarDescriptor.Cond.leU) (quoteExpr a) (quoteExpr b)
    | .not c => mkApp (mkConst ``LeanExe.Wasm.ScalarDescriptor.Cond.not) (quoteCond c)
    | .and a b => mkApp2 (mkConst ``LeanExe.Wasm.ScalarDescriptor.Cond.and) (quoteCond a) (quoteCond b)
    | .or a b => mkApp2 (mkConst ``LeanExe.Wasm.ScalarDescriptor.Cond.or) (quoteCond a) (quoteCond b)
end

private def quoteStmt : Stmt → Expr
  | .skip => mkConst ``Stmt.skip
  | .assign n e => mkApp2 (mkConst ``Stmt.assign) (mkNatLit n) (quoteExpr e)
  | .seq a b => mkApp2 (mkConst ``Stmt.seq) (quoteStmt a) (quoteStmt b)
  | .branch c a b => mkApp3 (mkConst ``Stmt.branch) (quoteCond c) (quoteStmt a) (quoteStmt b)
  | .loop c b => mkApp2 (mkConst ``Stmt.loop) (quoteCond c) (quoteStmt b)
  | .call n f args => mkApp3 (mkConst ``Stmt.call) (mkNatLit n) (mkNatLit f)
      (quoteList (mkConst ``LeanExe.Wasm.ScalarDescriptor.Expr) (args.map quoteExpr))
  | .effect n f args => mkApp3 (mkConst ``Stmt.effect) (mkNatLit n) (mkNatLit f)
      (quoteList (mkConst ``LeanExe.Wasm.ScalarDescriptor.Expr) (args.map quoteExpr))

private def quoteFunction (function : Function) : Expr :=
  mkApp4 (mkConst ``Function.mk) (mkNatLit function.params) (mkNatLit function.locals)
    (quoteStmt function.body) (quoteExpr function.result)

private def addDefinition (name : Name) (value : Expr) : TermElabM Unit := do
  let type ← inferType value
  addAndCompile <| .defnDecl
    { name, levelParams := [], type, value, hints := .regular 0, safety := .safe }

private partial def listCertificateProof (arguments : Array Ident) (proof : TSyntax `term) :
    TermElabM (TSyntax `tactic) := do
  let argsName := mkIdent `args
  let lengthName := mkIdent `length
  if arguments.isEmpty then
    `(tactic| cases $argsName:term with
      | nil => simpa [LeanExe.Core.applyNative] using $proof
      | cons _ _ => simp at $lengthName:ident)
  else
    let name := arguments[0]!
    let rest ← listCertificateProof (arguments.extract 1 arguments.size) proof
    `(tactic| cases $argsName:term with
      | nil => simp at $lengthName:ident
      | cons $name $argsName => ($rest:tactic))

/-- Extract ordinary definitions and synthesize native-to-core proofs. There is
no trusted connection from the metaprogram's output to the original function:
the generated proof is checked by Lean's kernel. -/
def certify (sourceName certificateName : Name) : TermElabM Unit := do
    let (_, state) ← (ensureFunction sourceName).run {}
    let functions ← state.entries.toList.mapM fun entry => do
      let some function := entry.function | throwError "Unfinished definition: {entry.name}"
      return function
    let moduleName := certificateName ++ `source
    let moduleValue := quoteList (mkConst ``Function) (functions.map quoteFunction)
    addDefinition moduleName moduleValue
    let mut proved : Array Name := #[]
    for index in (List.range state.entries.size).reverse do
      let some entry := state.entries[index]? | throwError "Missing source declaration {index}"
      let some function := functions[index]? | throwError "Missing compiled function {index}"
      let proofName := certificateName ++ Name.mkSimple s!"function_{index}"
      let nativeInfo ← getConstInfo entry.name
      let proofType ← forallTelescope nativeInfo.type fun args _ => do
        let invocation ← mkAppM ``Invokes #[mkConst moduleName, mkConst ``noEffects,
          mkNatLit index, mkConst ``Unit.unit, quoteList (mkConst ``UInt64) args.toList,
          mkConst ``Unit.unit, mkAppN (mkConst entry.name) args]
        mkForallFVars args invocation
      let identifiers := (List.range function.params).toArray.map fun i => mkIdent <| Name.mkSimple s!"arg{i}"
      let application ← `(term| $(mkIdent entry.name) $identifiers:ident*)
      let introductions ← `(tactic| intro $identifiers:ident*)
      let helperFacts ← proved.mapM fun name => `(tactic| have := $(mkIdent name))
      let inductionStep ← `(tactic| first | fun_induction $application | fun_cases $application)
      let moduleStep ← `(tactic| dsimp only [$(mkIdent moduleName):term])
      let proofGoal ← mkFreshExprSyntheticOpaqueMVar proofType
      let unfinished ← Tactic.run proofGoal.mvarId! do
        Tactic.evalTactic introductions
        for helper in helperFacts do Tactic.evalTactic helper
        Tactic.evalTactic inductionStep
        let branches ← Tactic.getGoals
        let mut remaining := []
        for goal in branches do
          Tactic.setGoals [goal]
          Tactic.evalTactic moduleStep
          Tactic.evalTactic (← `(tactic| core_native_invokes))
          remaining := remaining ++ (← Tactic.getUnsolvedGoals)
        Tactic.setGoals remaining
      unless unfinished.isEmpty do
        for goal in unfinished do
          goal.withContext do logInfo m!"Unresolved native correspondence: {← goal.getType}"
        throwError "Native proof construction left unresolved goals for {entry.name}"
      Term.synthesizeSyntheticMVarsNoPostponing
      let proof ← instantiateMVars proofGoal
      if proof.hasSorry || proof.hasMVar then
        throwError "Could not prove the native correspondence for {entry.name}"
      addAndCompile <| .thmDecl { name := proofName, levelParams := [], type := proofType, value := proof }
      proved := proved.push proofName
    let root :: _ := functions | throwError "The source module is empty"
    let identifiers := (List.range root.params).toArray.map fun i => mkIdent <| Name.mkSimple s!"arg{i}"
    let proofApplication ← `(term| $(mkIdent (certificateName ++ `function_0)) $identifiers:ident*)
    let bodyProof ← listCertificateProof identifiers proofApplication
    let constructor := mkAppN (mkConst ``NativeCertificate.mk)
      #[mkNatLit root.params, mkConst sourceName, mkConst moduleName, mkNatLit 0]
    let constructorType ← whnf (← inferType constructor)
    let proofGoal ← mkFreshExprSyntheticOpaqueMVar constructorType.bindingDomain!
    let unfinished ← Tactic.run proofGoal.mvarId! do
      Tactic.evalTactic (← `(tactic| intro $(mkIdent `args) $(mkIdent `length)))
      Tactic.evalTactic bodyProof
    unless unfinished.isEmpty do
      throwError "Argument-list certificate construction left unresolved goals for {sourceName}"
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proofGoal
    if proof.hasSorry || proof.hasMVar then
      throwError "Could not finish the native certificate for {sourceName}"
    addDefinition certificateName (mkApp constructor proof)
    logInfo m!"Compiled {sourceName}; generated kernel-checked native certificate {certificateName}."

end LeanExe.Core.Extract
