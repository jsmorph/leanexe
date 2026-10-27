import LeanExe.Native.Subset
import Verified.Native
import Verified.Reflect.Definitions
import Verified.Reflect.TailDefinition
import Verified.Reflect.TailOptions
import Verified.Reflect.RecursiveTypes
import Verified.Reflect.ScalarProof

namespace Verified.Reflect

open Lean Meta Elab Command Term

/-- The list of the addresses and names of the tables `idxs` among the program's tables `tables`,
named `tableNames`, which a wrapper's theorems state. -/
def tableEntries (tables : Name) (tableNames : Array Name) (idxs : List Nat) :
    MetaM Lean.Expr := do
  let entryTy ← mkAppM ``Prod #[mkConst ``UInt64,
    mkApp (mkConst ``Array [.zero]) (mkConst ``UInt64)]
  let entries ← idxs.mapM fun i => do
    let addr ← kernelWhnf (← mkAppM ``UInt64.toNat
      #[← mkAppM ``tableAddr #[mkConst tables, mkNatLit i]])
    let some a := natOf addr
      | throwError "verified_compile: cannot evaluate the address of table {i}"
    mkAppM ``Prod.mk #[toExpr (UInt64.ofNat a), mkConst tableNames[i]!]
  return listExpr entryTy entries

/-- The definition of `r` as a function of the tuple of its arguments. -/
def leanFun (r : Reflected) : MetaM Lean.Expr :=
  withLocalDeclD `x r.argsType fun x => do
    let projs ← argProjsE x (paramModes r.params r.modes) r.params.length
    mkLambdaFVars #[x] (mkAppN (mkConst r.name) projs.toArray)

/-- The proof of the theorem `claim` that the module computes the definition of `r`: the
compiler's theorem `h` for its source function, carried to Lean's instances by
`ImplementsA.transferAgree`.  The constant `funs` of the functions' meanings has the value
`funsVal`, a chain of `Funs.cons`.  The definition's equation `r.meaningEq` enters through
`Funs.get_there` and `Funs.get_here`, which take `funs.get` to the meaning of the definition's
function, and through plain lambdas for the flattenings, so that the kernel checks each step by
matching terms and by beta reduction and never unfolds the definition or its loops. -/
def implementsProof (funs : Name) (funsVal h F : Lean.Expr) (r : Reflected)
    (argsAgree resultAgree : Name) : MetaM Lean.Expr := do
  let hTy ← inferType h
  let #[α, γ, ia, ic, aborts, m, entry, f, pre, post] := hTy.getAppArgs
    | throwError "verified_compile: the compiler's theorem {hTy}"
  let β := r.argsType
  let δ := r.resultType
  let modes := paramModes r.params r.modes
  let hF ← withLocalDeclD `y β fun y => do
    let a := mkApp f (mkApp r.flatArgs y)
    let get := a.headBeta
    let #[_, _, _, fv, env] := get.getAppArgs
      | throwError "verified_compile: the meaning {get}"
    let get' := get.replace fun e => if e.isConstOf funs then some funsVal else none
    let step ← mkExpectedTypeHint (← mkEqRefl a) (← mkEq a get')
    let chain ← getChain funsVal fv env
    let some (_, _, b) := (← inferType chain).eq?
      | throwError "verified_compile: the meaning of {get}"
    let c := mkApp r.flatResult (mkApp F y)
    let projs ← argProjsE y modes r.params.length
    let eq ← mkExpectedTypeHint (mkAppN (mkConst r.meaningEq) projs.toArray) (← mkEq b c)
    mkLambdaFVars #[y] (← transHint (← transHint step chain) eq)
  return mkAppN (mkConst ``ImplementsA.transferAgree)
    #[α, β, γ, δ, ia, ← userInst β, ic, ← userInst δ, aborts, m, entry, f, pre, post, h,
      r.flatArgs, r.flatResult, F, hF, mkConst argsAgree, mkConst resultAgree]

/-- `implementsProof` for a wrapper, whose theorem `h` is `ImplementsTables`. -/
def wrapperProof (funs : Name) (funsVal h F : Lean.Expr) (r : Reflected)
    (argsAgree resultAgree : Name) : MetaM Lean.Expr := do
  let hTy ← inferType h
  let #[α, γ, ia, ic, aborts, m, entry, f, tables, pre, post] := hTy.getAppArgs
    | throwError "verified_compile: the wrapper's theorem {hTy}"
  let β := r.argsType
  let δ := r.resultType
  let modes := paramModes r.params r.modes
  let hF ← withLocalDeclD `y β fun y => do
    let a := mkApp f (mkApp r.flatArgs y)
    let get := a.headBeta
    let #[_, _, _, fv, env] := get.getAppArgs
      | throwError "verified_compile: the meaning {get}"
    let get' := get.replace fun e => if e.isConstOf funs then some funsVal else none
    let step ← mkExpectedTypeHint (← mkEqRefl a) (← mkEq a get')
    -- The callee, a projection of the wrapper's record.
    let chain ← getChain funsVal (← whnf fv) env
    let some (_, _, b) := (← inferType chain).eq?
      | throwError "verified_compile: the meaning of {get}"
    let c := mkApp r.flatResult (mkApp F y)
    let projs ← argProjsE y modes r.params.length
    let eq ← mkExpectedTypeHint (mkAppN (mkConst r.meaningEq) projs.toArray) (← mkEq b c)
    mkLambdaFVars #[y] (← transHint (← transHint step chain) eq)
  return mkAppN (mkConst ``ImplementsTables.transferAgree)
    #[α, β, γ, δ, ia, ← userInst β, ic, ← userInst δ, aborts, m, entry, f, tables, pre, post,
      h, r.flatArgs, r.flatResult, F, hF, mkConst argsAgree, mkConst resultAgree]

/-- The callee and the tables of a wrapper definition `fun params => g T₁ … Tₖ params`: `g` is a
listed definition and each `Tᵢ` a constant of type `Array UInt64`, which `g` takes as borrowed
arrays of words before the definition's own parameters. -/
def wrapperShape? (name : Name) (callees : List Callee) : MetaM (Option (Callee × List Name)) := do
  let info ← getConstInfoDefn name
  lambdaTelescope (← instantiateMVars info.value) fun params body => do
    let .const fn _ := body.getAppFn | return none
    let some callee := callees.find? (·.name == fn) | return none
    let args := body.getAppArgs
    unless params.size < args.size do return none
    let k := args.size - params.size
    unless args.extract k args.size == params do return none
    let words := mkApp (mkConst ``Array [.zero]) (mkConst ``UInt64)
    let mut tables := #[]
    for t in args.extract 0 k do
      let .const c _ := t | return none
      unless ← isDefEq (← inferType t) words do return none
      tables := tables.push c
    unless callee.sig.params.take k == List.replicate k (.array .word) &&
        (callee.sig.modes.take k).all (· == .borrowed) do
      throwError "verified_compile: {fn} must take the tables of {name} as borrowed arrays of \
        words before its other parameters"
    return some (callee, tables.toList)

/-- Reflects the wrapper definition `name`, which applies `callee` to the tables `tables` and its
own parameters, and adds `base.denote_eq`: the callee's meaning at the tables and the parameters
is the flattening of `name` at the parameters, from the callee's own equation. -/
def reflectWrapper (base name : Name) (callee : Callee) (tables : List Name) :
    MetaM Reflected := do
  let info ← getConstInfoDefn name
  lambdaTelescope (← instantiateMVars info.value) fun params body => do
    let types ← params.toList.mapM fun p => do tyOf (← inferType p)
    let resultShape ← shapeOf (← inferType body)
    let calleeEq := mkAppN (Lean.mkConst callee.denoteEq)
      (tables.toArray.map Lean.mkConst ++ params)
    let some (_, lhs, _) := (← inferType calleeEq).eq?
      | throwError "verified_compile: the equation of {callee.name}"
    let eq ← mkEq lhs (resultShape.apply (mkAppN (mkConst name) params))
    addTheorem (base ++ `denote_eq) (← mkForallFVars params eq)
      (← mkLambdaFVars params (← mkExpectedTypeHint calleeEq eq))
    let k := tables.length
    finishReflected base name params types resultShape.ty (← inferType body) callee.sig.aborts
      (callee.sig.modes.drop k) callee.sig.depth (base ++ `denote_eq)

/-- Adds `base.bound_eq` for the wrapper `name` of `callee`, whose bound is `boundName`: the
wrapper's bound at its arguments is the callee's bound at the tables and the arguments, or the
numeral that the callee's own equation states.  The proof is the chain of `Prog.bounds` from the
callee's index, which the kernel checks against the wrapper's bound by unfolding `Wrapper.bound`
and comparing the callee's index and environments. -/
def wrapperBoundEquation (base name boundName : Name) (callee : Callee)
    (progVal funsVal : Lean.Expr) : MetaM Unit := do
  let cb := callee.bound
  let info ← getConstInfoDefn name
  lambdaTelescope (← instantiateMVars info.value) fun params body => do
    let args := body.getAppArgs
    let k := args.size - params.size
    let owned (i : Nat) := callee.sig.mode i == .owned && !callee.sig.params[i]!.scalar
    let wTuple ← argsTuple
      (params.toList.zip ((List.range params.size).map fun i => owned (k + i)))
    let lhs := mkApp (mkConst boundName) wTuple
    let target := mkApp (mkConst cb.bound)
      (← argsTuple (args.toList.zip ((List.range args.size).map owned)))
    -- `Wrapper.bound tables w flags bounds env` unfolds to the credits of the callee's paid
    -- owned parameters plus `bounds.get w.callee env'`.  For a callee with a paid parameter, the
    -- sum is the callee's `bound`, the credits plus its entry `cost`, and otherwise the credits
    -- are 0.
    let some sum ← unfoldDefinition? ((← getConstInfoDefn boundName).value.beta #[wTuple])
      | throwError "verified_compile: the bound of {name}"
    let sum := sum.headBeta
    let (``HAdd.hAdd, #[_, _, _, _, credit, get]) := sum.getAppFnArgs
      | throwError "verified_compile: the bound of {name}: {sum}"
    let (``Env.credit, #[sel, _, envC]) := credit.getAppFnArgs
      | throwError "verified_compile: the credits of {name}: {credit}"
    let (``Sig.paidSel, #[g, pf]) := sel.getAppFnArgs
      | throwError "verified_compile: the credits of {name}: {sel}"
    let notFn := Lean.mkLambda `b .default (mkConst ``Bool)
      (mkApp (mkConst ``Bool.not) (.bvar 0))
    let unpaid := mkApp3 (mkConst ``List.all [Level.zero]) (mkConst ``Bool) pf notFn
    let unpaidV ← evalBool m!"whether {callee.name} has no paid parameter" unpaid
    let #[_, _, bounds, fv, env] := get.getAppArgs
      | throwError "verified_compile: the bound of {name}: {get}"
    let chain ← tableChain false progVal funsVal (← whnfR fv) env bounds.appArg!
    let some (_, _, chainRhs) := (← inferType chain).eq?
      | throwError "verified_compile: the bounds of {name}"
    checkEntryTarget m!"{name}" chainRhs target
    let hget ← mkExpectedTypeHint chain (← mkEq get target)
    let hlhs ← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs sum)
    let (rhs, h) ← match unpaidV, cb.credited?, cb.numeralEq with
      | false, some credited, _ => do
        -- The kernel unfolds the callee's `bound` to compare it with the credits plus `cost`.
        let full := mkApp (mkConst credited) target.appArg!
        let hsum ← congr2 natAdd credit credit get target none (some hget)
        let hfull ← mkExpectedTypeHint (← mkEqRefl full) (← mkEq (mkApp2 natAdd credit target) full)
        pure (full, ← mkEqTrans hlhs (← mkEqTrans hsum hfull))
      | false, none, _ =>
        throwError "verified_compile: {callee.name} has a paid parameter but no bound with credits"
      | true, _, numeralEq? => do
        let hnone ← mkAppOptM ``Sig.paidSel_none
          #[some g, some pf, some (← evalEq unpaid (boolConst true))]
        let hzero ← mkAppM ``Env.credit_eq_zero #[hnone, envC]
        let hsum ← congr2 natAdd credit natZero get target (some hzero) (some hget)
        let h ← mkEqTrans hlhs (← mkEqTrans hsum (← mkAppM ``Nat.zero_add #[target]))
        match numeralEq? with
        | some n => do
          let hn := mkAppN (mkConst n) args
          let some (_, _, c) := (← inferType hn).eq?
            | throwError "verified_compile: the bound equation of {callee.name}"
          pure (c, ← mkEqTrans h hn)
        | none => pure (target, h)
    addTheorem (base ++ `bound_eq) (← mkForallFVars params (← mkEq lhs rhs))
      (← mkLambdaFVars params h)

/-- `h0` with `old`, a table's entry `table.get f` in its statement, replaced by the function's own
entry, from `chainAt env : old env = own`.  The kernel then never compares the table's entry with
the function's own, which would unfold the compiler's bound. -/
def rewriteEntry (h0 old : Lean.Expr) (chainAt : Lean.Expr → MetaM Lean.Expr) :
    MetaM Lean.Expr := do
  let .forallE _ envTy _ _ ← inferType old
    | throwError "verified_compile: the table entry {old}"
  let hfun ← withLocalDeclD `env envTy fun env => do
    let chain ← chainAt env
    let some (_, _, own) := (← inferType chain).eq?
      | throwError "verified_compile: the table entry {old}"
    mkLambdaFVars #[env] (← mkExpectedTypeHint chain (← mkEq (mkApp old env) own))
  let hfun ← mkAppM ``funext #[hfun]
  let some (_, _, new) := (← inferType hfun).eq?
    | throwError "verified_compile: the table entry {old}"
  let ty ← instantiateMVars (← inferType h0)
  let motive ← withLocalDeclD `B (← inferType old) fun B => do
    mkLambdaFVars #[B] (ty.replace fun e => if e == old then some B else none)
  let h ← mkAppM ``Eq.mp #[← mkCongrArg motive hfun, h0]
  mkExpectedTypeHint h (ty.replace fun e => if e == old then some new else none)

/-- The most positions that the reflector accepts in a function whose code takes the call depth.
Wasmtime 44 on aarch64 keeps 8 bytes for each value live across a call and 16 bytes per frame, so
`depthLimit` frames of 32 positions take at most 272,000 bytes of its 512 KiB default stack, and
the rest holds the functions without the depth parameter at the top of the chain.  The example
`Recursion.deep` runs a frame of 32 positions, 26 of them live across the self-call, at depth 999,
and its deepest frame calls two functions without the depth parameter. -/
def depthPositions : Nat := 32

/-- Rejects a function whose code takes the call depth and needs more than `depthPositions`
positions, from its body `body`. -/
def checkPositions (name : Name) (body : Lean.Expr) : MetaM Unit := do
  let n ← kernelWhnf (← mkAppM ``positions #[body, toExpr true])
  let some k := natOf n
    | throwError "verified_compile: cannot evaluate the positions of {name}"
  if k > depthPositions then
    throwError "verified_compile: the code of {name} takes the call depth and needs {k} \
      positions, more than the {depthPositions} that {depthLimit} nested calls may use"

/-- `FVar.there (… (FVar.there FVar.here))` with `k` applications of `there`. -/
def fvarStx {m : Type → Type} [Monad m] [MonadQuotation m] : Nat → m Term
  | 0 => `(Verified.FVar.here)
  | k + 1 => do `(Verified.FVar.there $(← fvarStx k))

private structure ProgramReflection where
  sigs : List Sig := []
  prog : Lean.Expr := Lean.mkConst ``Prog.nil
  funs : Lean.Expr := Lean.mkConst ``Funs.nil
  meaning : Lean.Expr := Lean.mkConst ``Prog.Meaning.nil
  out : Array Reflected := #[]
  callees : List Callee := []
  wraps : Array (Reflected × Callee × List Nat) := #[]
  tableNames : Array Name := #[]

private def closedReflectionExpr (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← instantiateMVars e
  if e.hasExprMVar || e.hasLevelMVar || e.hasFVar then
    throwError "verified_compile: an expression remains open between definitions: {e}"
  return e

private def closeReflected (r : Reflected) : MetaM Reflected := do
  return { r with
    argsType := ← closedReflectionExpr r.argsType
    resultType := ← closedReflectionExpr r.resultType
    flatArgs := ← closedReflectionExpr r.flatArgs
    flatResult := ← closedReflectionExpr r.flatResult }

private def closeReflection (state : ProgramReflection) : MetaM ProgramReflection := do
  return { state with
    prog := ← closedReflectionExpr state.prog
    funs := ← closedReflectionExpr state.funs
    meaning := ← closedReflectionExpr state.meaning
    out := ← state.out.mapM closeReflected
    wraps := ← state.wraps.mapM fun (r, callee, indices) => do
      return (← closeReflected r, callee, indices) }

private def reflectProgramFunction (base name : Name) (state : ProgramReflection) :
    TermElabM ProgramReflection := do
  let mut sigs := state.sigs
  let mut prog := state.prog
  let mut funs := state.funs
  let mut meaning := state.meaning
  let mut out := state.out
  let mut callees := state.callees
  let mut wraps := state.wraps
  let mut tableNames := state.tableNames
  trace[Verified.reflect] "reflect {name}, {(← getRemainingHeartbeats) / 1000} heartbeats remaining"
  let sigsExpr := listExpr (Lean.mkConst ``Sig) (sigs.map sigExpr)
  let fbase := base ++ Name.mkSimple name.getString!
  -- A wrapper passes constant tables to a listed function; it is no function of the
  -- program, and the module exports it after the entries.
  if let some (callee, tnames) ← wrapperShape? name callees then
    let mut idxs := #[]
    for t in tnames do
      match tableNames.findIdx? (· == t) with
      | some i => idxs := idxs.push i
      | none =>
        idxs := idxs.push tableNames.size
        tableNames := tableNames.push t
    wraps := wraps.push (← reflectWrapper fbase name callee tnames, callee, idxs.toList)
    return ← closeReflection { sigs, prog, funs, meaning, out, callees, wraps, tableNames }
  let f := Lean.mkConst (fbase ++ `func)
  -- `getUnfoldEqnFor?` also returns the unfolding equation of a definition that is not
  -- recursive when an imported module has generated it, so recursion is tested first.
  let eqn? ← if ← isRecursiveDefinition name then getUnfoldEqnFor? name else pure none
  let r ← match eqn? with
    | none =>
      let r ← reflectDefinition fbase name sigsExpr funs prog callees
      if r.depth then checkPositions name (mkApp2 (mkConst ``Func.body) sigsExpr f)
      let sig := sigExpr ⟨r.params, r.result, r.aborts, r.modes, r.depth⟩
      meaning := mkAppN (Lean.mkConst ``Prog.Meaning.cons) #[sigsExpr, f, prog, funs, meaning]
      funs := mkAppN (Lean.mkConst ``Funs.cons) #[sigsExpr, sig,
        mkAppN (Lean.mkConst ``Func.denote) #[sigsExpr, f, funs], funs]
      prog := mkAppN (Lean.mkConst ``Prog.cons) #[sigsExpr, f, prog]
      pure r
    | some eqName =>
      if verified.tailLoops.get (← getOptions) && (← isTailDefinition name eqName) then
        let r ← reflectTailSource fbase name eqName sigsExpr funs prog callees
        if r.depth then
          let positions ← kernelWhnf (← mkAppM ``TailFunc.positions #[f])
          let some n := natOf positions
            | throwError "verified_compile: cannot evaluate the tail positions of {name}"
          if n > depthPositions then
            throwError "verified_compile: tail function {name} takes call depth and needs {n} positions, more than {depthPositions}"
        let sig := sigExpr ⟨r.params, r.result, r.aborts, r.modes, r.depth⟩
        let M := Lean.mkConst (fbase ++ `meaning)
        meaning := mkAppN (Lean.mkConst ``Prog.Meaning.consTail)
          #[sigsExpr, f, prog, funs, M, meaning, Lean.mkConst (fbase ++ `decreases),
            Lean.mkConst (fbase ++ `fixed)]
        funs := mkAppN (Lean.mkConst ``Funs.cons) #[sigsExpr, sig, M, funs]
        prog := mkAppN (Lean.mkConst ``Prog.consTail) #[sigsExpr, f, prog]
        pure r
      else
        let r ← reflectRecursive fbase name eqName sigsExpr funs prog meaning callees
        checkPositions name (mkApp2 (mkConst ``RecFunc.body) sigsExpr f)
        let sig := sigExpr ⟨r.params, r.result, r.aborts, r.modes, r.depth⟩
        let M := Lean.mkConst (fbase ++ `meaning)
        meaning := mkAppN (Lean.mkConst ``Prog.Meaning.consRec)
          #[sigsExpr, f, prog, funs, M, meaning, Lean.mkConst (fbase ++ `fixed)]
        funs := mkAppN (Lean.mkConst ``Funs.cons) #[sigsExpr, sig, M, funs]
        prog := mkAppN (Lean.mkConst ``Prog.consRec) #[sigsExpr, f, prog]
        pure r
  let sig : Sig := ⟨r.params, r.result, r.aborts, r.modes, r.depth⟩
  sigs := sig :: sigs
  let some bound := r.bound? | throwError "verified_compile: the bound of {name}"
  callees := { name := name, sig := sig, denoteEq := r.meaningEq, bound } :: callees
  out := out.push r
  trace[Verified.reflect] "reflected {name}, {(← getRemainingHeartbeats) / 1000} heartbeats remaining"
  closeReflection { sigs, prog, funs, meaning, out, callees, wraps, tableNames }

syntax (name := verifiedCompile) "verified_compile " ident " := " "[" ident,* "]" : command

/-- `verified_compile p := [f, g, …]` adds the program `p.program` of the listed definitions, in
order, each of which may call those before it and, when recursive, itself; the meanings
`p.funs` of its functions and the proof `p.meaning : Prog.Meaning p.program p.funs`; the module
`p.module`; the tables `p.tables` and the wrappers `p.wrappers`; for each definition `f`, the
theorem `p.f.implements` that the module computes `f`, at the function's index, at its exported
entry when its code takes the call depth, or, for a wrapper, at the wrapper's entry from a store
that holds the tables; `p.initial`, that the store in which the module starts meets the
allocator invariant and holds the tables; `p.inSubset`, that the module is in the subset that
the translator to C accepts, when it is; when the module translates, its translation
`p.translation` to C, with `lx_mem` of `nativeCap` pages, the list `p.translation_funcs` of the
functions that the translation contains, the equation `p.translation_eq`, and, for each
definition `f` whose function the translation contains, the theorem `p.f.native` that the C
function computes `f` as `p.f.implements` states; and `p.bytes`, the module's bytes with all the
functions' theorems. -/
@[command_elab verifiedCompile]
def elabVerifiedCompile : CommandElab
  | `(verified_compile $target := [$sources,*]) => do
    let names ← sources.getElems.mapM fun s => liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
    let base := (← getCurrNamespace) ++ target.getId
    prepareRecursiveTypes names
    let mut state : ProgramReflection := {}
    for name in names do
      state ← liftTermElabM (reflectProgramFunction base name state)
    let (reflected, wraps, tableNames, funsVal) ← liftTermElabM do
      let sigs := state.sigs
      let prog := state.prog
      let funs := state.funs
      let meaning := state.meaning
      let out := state.out
      let wraps := state.wraps
      let tableNames := state.tableNames
      let sigsExpr := listExpr (Lean.mkConst ``Sig) (sigs.map sigExpr)
      addDefinition (base ++ `program) (mkApp (Lean.mkConst ``Prog) sigsExpr) prog
      addDefinition (base ++ `funs) (mkApp (Lean.mkConst ``Funs) sigsExpr) funs
      addTheorem (base ++ `meaning)
        (mkApp3 (Lean.mkConst ``Prog.Meaning) sigsExpr (Lean.mkConst (base ++ `program))
          (Lean.mkConst (base ++ `funs))) meaning
      -- The tables, in the order of their first use, and the wrappers.
      let words := mkApp (Lean.mkConst ``Array [.zero]) (Lean.mkConst ``UInt64)
      addDefinition (base ++ `tables) (mkApp (Lean.mkConst ``List [.zero]) words)
        (listExpr words (tableNames.toList.map Lean.mkConst))
      let T := mkApp2 (Lean.mkConst ``List.length [.zero]) words
        (Lean.mkConst (base ++ `tables))
      let mut wexprs : Array Lean.Expr := #[]
      for (r, callee, idxs) in wraps do
        let some pos := out.findIdx? (·.name == callee.name)
          | throwError "verified_compile: the callee {callee.name}"
        let fvarTy := mkApp2 (Lean.mkConst ``FVar) sigsExpr (sigExpr callee.sig)
        let fvar ← Term.elabTermEnsuringType (← fvarStx (out.size - 1 - pos)) (some fvarTy)
        Term.synthesizeSyntheticMVarsNoPostponing
        let fvar ← instantiateMVars fvar
        let fins ← idxs.mapM fun i => do
          mkAppM ``Fin.mk #[mkNatLit i, ← mkDecideProof (← mkLt (mkNatLit i) T)]
        wexprs := wexprs.push (mkAppN (Lean.mkConst ``Wrapper.mk)
          #[sigsExpr, T, toExpr r.name.getString!, listExpr (mkApp (Lean.mkConst ``Fin) T) fins,
            ctxExpr r.params, tyExpr r.result, toExpr callee.sig.aborts,
            modesExpr callee.sig.modes, toExpr callee.sig.depth, fvar, ← mkEqRefl (toExpr true)])
      let wrapperTy := mkApp2 (Lean.mkConst ``Wrapper) sigsExpr T
      addDefinition (base ++ `wrappers) (mkApp (Lean.mkConst ``List [.zero]) wrapperTy)
        (listExpr wrapperTy wexprs.toList)
      addDefinition (base ++ `module) (Lean.mkConst ``Wasm.Module)
        (mkAppN (Lean.mkConst ``compileWith) #[sigsExpr, Lean.mkConst (base ++ `program),
          Lean.mkConst (base ++ `tables), Lean.mkConst (base ++ `wrappers)])
      return (out, wraps, tableNames, funs)
    -- The store in which the module starts.
    let initialProof ← `(Verified.compileWith_initialStore $(mkIdent (base ++ `program))
      $(mkIdent (base ++ `tables)) $(mkIdent (base ++ `wrappers)) (by decide +kernel))
    elabCommand (← `(theorem $(mkIdent (target.getId ++ `initial)) : type_of% $initialProof :=
      $initialProof))
    let progId := mkIdent (base ++ `program)
    let funsId := mkIdent (base ++ `funs)
    let meaningId := mkIdent (base ++ `meaning)
    let moduleId := mkIdent (base ++ `module)
    let tablesId := mkIdent (base ++ `tables)
    let wrappersId := mkIdent (base ++ `wrappers)
    let n := reflected.size
    let mut claims : Array Term := #[]
    let mut proofs : Array Term := #[]
    let mut entries := 0
    let mut scalarCallees : List (Nat × Lean.Expr) := []
    -- Each function's simple name, the index of its theorem, and whether it is a wrapper.
    let mut natives : Array (Name × Nat × Bool) := #[]
    for k in [0:n] do
      let r := reflected[k]!
      trace[Verified.reflect] "prove {r.name}"
      let simple := Name.mkSimple r.name.getString!
      let implName := base ++ simple ++ `implements
      let fvar ← fvarStx (n - 1 - k)
      -- The compiler's theorem at the function's index, or at its entry, the `j`-th, when its
      -- code takes the call depth.
      let (hStx, index) ← if r.depth then
          let j := entries
          entries := entries + 1
          pure (← `(Verified.Prog.correct_entryWith $progId $funsId $meaningId $tablesId
            $wrappersId $fvar rfl (j := $(Lean.quote j)) (by decide +kernel)), 2 + n + j)
        else if r.paid then
          pure (← `(Verified.ImplementsB.implementsA (Verified.FunSpec.implementsB
            (Verified.Prog.correctWith $progId $funsId $meaningId $tablesId $wrappersId $fvar 0)
            rfl)), 2 + k)
        else
          pure (← `(Verified.ImplementsB.implementsA (Verified.FunSpec.implementsB_unpaid
            (Verified.Prog.correctWith $progId $funsId $meaningId $tablesId $wrappersId $fvar 0)
            rfl (by decide +kernel))), 2 + k)
      -- The theorem for the flattened types, carried to Lean's types: each argument is
      -- represented as its flattening is, and the flattening of the result represents it.
      liftTermElabM do
        let h ← Term.elabTerm (← `(Verified.ImplementsA.lean $hStx)) none
        Term.synthesizeSyntheticMVarsNoPostponing
        let h ← instantiateMVars h
        let F ← leanFun r
        let proof ← implementsProof (base ++ `funs) funsVal h F r (base ++ simple ++ `argsAgree)
          (base ++ simple ++ `resultAgree)
        -- The statement with the trap flag, the module, and the index as constants, and the
        -- precondition and postcondition beta-reduced.
        let ty ← inferType proof
        let args := ty.getAppArgs
        let claim := mkAppN ty.getAppFn (args.set! 4 (toExpr r.aborts)
          |>.set! 5 (mkConst (base ++ `module)) |>.set! 6 (mkNatLit index)
          |>.set! 8 (← Core.betaReduce args[8]!) |>.set! 9 (← Core.betaReduce args[9]!))
        addTheorem implName claim proof
      let uniform? ← liftTermElabM <| addScalarProof base r index fun i =>
        (scalarCallees.find? (fun pair => pair.1 == i)).map Prod.snd
      if let some uniform := uniform? then scalarCallees := (index, uniform) :: scalarCallees
      claims := claims.push (← `(type_of% $(mkIdent implName)))
      proofs := proofs.push (mkIdent implName)
      natives := natives.push (simple, index, false)
      -- The theorem without a trap, with the growth of `top` bounded by the function's bound on
      -- Lean's argument tuple.  For a function whose code takes no call depth, it holds when the
      -- bound fits, if the function may trap; for one whose code does, with the frames that the
      -- entry's depth 0 leaves, when its calls find their frames and the bound fits.
      let boundId := mkIdent (base ++ simple ++ `bound)
      liftTermElabM do
        let progVal := (← getConstInfoDefn (base ++ `program)).value
        let (h, pre?, post) ← if r.depth then
            let frames ← evalNat (mkApp (mkConst ``framesAt) (toExpr (0 : UInt64)))
            let h0 ← Term.elabTerm (← if r.paid then
                `(Verified.Prog.entry_trapFreeWith $progId $funsId
                  $meaningId $tablesId $wrappersId $fvar rfl (j := $(Lean.quote (index - 2 - n)))
                  (by decide +kernel))
              else
                `(Verified.Prog.entry_trapFreeWith_unpaid $progId $funsId
                  $meaningId $tablesId $wrappersId $fvar rfl (j := $(Lean.quote (index - 2 - n)))
                  (by decide +kernel) (by decide +kernel))) none
            Term.synthesizeSyntheticMVarsNoPostponing
            let h0 ← instantiateMVars h0
            -- The precondition
            -- `fun x heap store => fits.get f x = true ∧ Within … (bounds.get f x)`, with the
            -- credits before `bounds.get f x` for a function with a paid parameter.
            let (fitsFn, boundFn) ← lambdaTelescope (← inferType h0).getAppArgs[8]! fun _ pre => do
              let (``And, #[l, w]) := pre.getAppFnArgs
                | throwError "verified_compile: the precondition {pre}"
              let some (_, fl, _) := l.eq? | throwError "verified_compile: the precondition {pre}"
              let entry := if r.paid then w.appArg!.appArg! else w.appArg!
              return (fl.appFn!, entry.appFn!)
            let fv := boundFn.appArg!
            -- The chains hold the numeral of `framesAt 0`, which the kernel compares with
            -- `framesAt 0` by evaluating the subtraction of two words' values.
            let h0 ← rewriteEntry h0 boundFn fun env =>
              tableChain false progVal funsVal fv env frames
            let h0 ← rewriteEntry h0 fitsFn fun env => tableChain true progVal funsVal fv env frames
            let fitsId := mkIdent (base ++ simple ++ `fits)
            let fr := Lean.quote (natOf frames).get!
            pure (← mkAppM ``ImplementsA.lean #[h0],
              some (← `(fun x heap store => $fitsId $fr x = true ∧
                LeanExe.Pipeline.Heap.Within heap store $moduleId ($boundId $fr x))),
              ← `(fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + $boundId $fr x))
          else
            let h0 ← Term.elabTerm (← if r.paid then
                `(Verified.FunSpec.implementsB (Verified.Prog.correctWith $progId $funsId
                  $meaningId $tablesId $wrappersId $fvar 0) rfl)
              else
                `(Verified.FunSpec.implementsB_unpaid (Verified.Prog.correctWith $progId $funsId
                  $meaningId $tablesId $wrappersId $fvar 0) rfl (by decide +kernel))) none
            Term.synthesizeSyntheticMVarsNoPostponing
            let h0 ← instantiateMVars h0
            let #[_, _, _, _, _, _, _, _, boundFn] := (← inferType h0).getAppArgs
              | throwError "verified_compile: the bounded theorem {← inferType h0}"
            -- The table's entry `bounds.get f`, after the credits for a function with a paid
            -- parameter.
            let boundEnv ← if r.paid then
                lambdaTelescope boundFn fun _ body => pure body.appArg!.appFn!
              else pure boundFn
            let h0 ← rewriteEntry h0 boundEnv fun env =>
              tableChain false progVal funsVal boundEnv.appArg! env boundEnv.appFn!.appArg!.appArg!
            let h0 ←
              mkAppM (if r.aborts then ``ImplementsB.trapFree else ``ImplementsB.noTrap) #[h0]
            pure (← mkAppM ``ImplementsA.lean #[h0],
              ← if r.aborts then
                  some <$> `(fun x heap store =>
                    LeanExe.Pipeline.Heap.Within heap store $moduleId ($boundId x))
                else pure none,
              ← `(fun x heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + $boundId x))
        let proof ← implementsProof (base ++ `funs) funsVal h (← leanFun r) r
          (base ++ simple ++ `argsAgree) (base ++ simple ++ `resultAgree)
        let ty ← inferType proof
        let args := ty.getAppArgs
        let pre ← match pre? with
          | some stx => Term.elabTermEnsuringType stx (← inferType args[8]!)
          | none => Core.betaReduce args[8]!
        let post ← Term.elabTermEnsuringType post (← inferType args[9]!)
        Term.synthesizeSyntheticMVarsNoPostponing
        let claim := mkAppN ty.getAppFn (args.set! 4 (toExpr false)
          |>.set! 5 (mkConst (base ++ `module)) |>.set! 6 (mkNatLit index)
          |>.set! 8 (← instantiateMVars pre) |>.set! 9 (← instantiateMVars post))
        addTheorem (base ++ simple ++ `trapFree) claim proof
    -- The wrappers' theorems, at their positions after the entries.
    let mut j := 0
    for (r, callee, idxs) in wraps do
      let simple := Name.mkSimple r.name.getString!
      let implName := base ++ simple ++ `implements
      let hStx ← `(Verified.Prog.correct_wrapper $progId $funsId $meaningId $tablesId $wrappersId
        (j := $(Lean.quote j)) rfl)
      liftTermElabM do
        let h ← Term.elabTerm (← `(Verified.ImplementsTables.lean $hStx)) none
        Term.synthesizeSyntheticMVarsNoPostponing
        let h ← instantiateMVars h
        let F ← leanFun r
        let proof ← wrapperProof (base ++ `funs) funsVal h F r (base ++ simple ++ `argsAgree)
          (base ++ simple ++ `resultAgree)
        -- The statement with the trap flag, the module, the index, and the tables' addresses
        -- and names as constants.
        let ty ← inferType proof
        let args := ty.getAppArgs
        let claim := mkAppN ty.getAppFn (args.set! 4 (toExpr (r.aborts || r.depth))
          |>.set! 5 (mkConst (base ++ `module)) |>.set! 6 (mkNatLit (2 + n + entries + j))
          |>.set! 8 (← tableEntries (base ++ `tables) tableNames idxs)
          |>.set! 9 (← Core.betaReduce args[9]!) |>.set! 10 (← Core.betaReduce args[10]!))
        addTheorem implName claim proof
      claims := claims.push (← `(type_of% $(mkIdent implName)))
      proofs := proofs.push (mkIdent implName)
      natives := natives.push (simple, 2 + n + entries + j, true)
      -- For a wrapper whose callee's code takes no call depth, its bound and its theorem without
      -- a trap, as for a function.
      unless r.depth do
        let boundName := base ++ simple ++ `bound
        liftTermElabM do
          let h0Stx ← if r.aborts then
              `(Verified.Prog.wrapper_trapFree $progId $funsId $meaningId $tablesId $wrappersId
                (j := $(Lean.quote j)) rfl rfl)
            else
              `(Verified.Prog.wrapper_noTrap $progId $funsId $meaningId $tablesId $wrappersId
                (j := $(Lean.quote j)) rfl rfl rfl)
          let h0 ← Term.elabTerm h0Stx none
          Term.synthesizeSyntheticMVarsNoPostponing
          let h0 ← instantiateMVars h0
          let h0Ty ← instantiateMVars (← inferType h0)
          let #[_, _, ia, _, _, _, _, _, _, _, post] := h0Ty.getAppArgs
            | throwError "verified_compile: the wrapper's bounded theorem {h0Ty}"
          let #[ps, ms] := ia.getAppArgs
            | throwError "verified_compile: the instance {ia}"
          -- The wrapper's bound on the source arguments, `Wrapper.bound` in the postcondition.
          let boundEnv ← lambdaTelescope post fun xs body => do
            let some (_, _, rhs) := body.le?
              | throwError "verified_compile: the wrapper's postcondition {body}"
            mkLambdaFVars #[xs[0]!] rhs.appArg!
          let boundVal ← withLocalDeclD `x r.argsType fun x =>
            mkLambdaFVars #[x] (mkApp boundEnv
              (mkAppN (mkConst ``Env.ofArgs) #[ps, ms, (mkApp r.flatArgs x).headBeta])).headBeta
          addBoundDefinition boundName (← mkArrow r.argsType (mkConst ``Nat)) boundVal
          wrapperBoundEquation (base ++ simple) r.name boundName callee
            (← getConstInfoDefn (base ++ `program)).value funsVal
          let h ← mkAppM ``ImplementsTables.lean #[h0]
          let proof ← wrapperProof (base ++ `funs) funsVal h (← leanFun r) r
            (base ++ simple ++ `argsAgree) (base ++ simple ++ `resultAgree)
          let ty ← inferType proof
          let args := ty.getAppArgs
          let boundId := mkIdent boundName
          let pre ← if r.aborts then
              Term.elabTermEnsuringType (← `(fun x heap store =>
                LeanExe.Pipeline.Heap.Within heap store $moduleId ($boundId x)))
                (← inferType args[9]!)
            else Core.betaReduce args[9]!
          let post ← Term.elabTermEnsuringType (← `(fun x heap _ heap' _ =>
            heap'.top.toNat ≤ heap.top.toNat + $boundId x)) (← inferType args[10]!)
          Term.synthesizeSyntheticMVarsNoPostponing
          let claim := mkAppN ty.getAppFn (args.set! 4 (toExpr false)
            |>.set! 5 (mkConst (base ++ `module)) |>.set! 6 (mkNatLit (2 + n + entries + j))
            |>.set! 8 (← tableEntries (base ++ `tables) tableNames idxs)
            |>.set! 9 (← instantiateMVars pre) |>.set! 10 (← instantiateMVars post))
          addTheorem (base ++ simple ++ `trapFree) claim proof
      j := j + 1
    let evaluated ← match evalModule (← getEnv) (← getOptions) (base ++ `module) with
      | .ok m => pure m
      | .error e => throwError "verified_compile: cannot evaluate the module: {e}"
    -- The subset of WebAssembly that the translator to C accepts.  The native check gives the
    -- reason for a module outside it, which has no native path; the kernel checks the theorem.
    match LeanExe.Native.violation evaluated with
    | some reason =>
        logWarning m!"verified_compile: the module is outside the subset of the translator to C: \
          {reason}"
    | none =>
        let inSubsetId := mkIdent (target.getId ++ `inSubset)
        elabCommand (← `(set_option maxRecDepth 100000 in
          theorem $inSubsetId : LeanExe.Native.InSubset $(mkIdent (base ++ `module)) := by
            decide +kernel))
        -- The translation to C.  The native translator gives the list of the functions that it
        -- contains, which the kernel checks once; each function's theorem then follows from the
        -- function's theorem and its membership in that list.
        match LeanExe.Native.translate LeanExe.Native.nativeCap evaluated with
        | none =>
            logWarning m!"verified_compile: the module does not translate to C with \
              {LeanExe.Native.nativeCap} pages"
        | some t =>
            let funcsId := mkIdent (target.getId ++ `translation_funcs)
            let translationId := mkIdent (target.getId ++ `translation)
            let eqId := mkIdent (target.getId ++ `translation_eq)
            elabCommand (← `(set_option maxRecDepth 100000 in
              theorem $funcsId : (LeanExe.Native.translate LeanExe.Native.nativeCap $moduleId).map
                  LeanExe.Native.Translation.funcs = some $(Lean.quote t.funcs) := by
                decide +kernel))
            elabCommand (← `(noncomputable def $translationId : LeanExe.Native.Translation :=
              (LeanExe.Native.translate LeanExe.Native.nativeCap $moduleId).get
                (LeanExe.Native.translate_isSome $funcsId)))
            elabCommand (← `(theorem $eqId :
                LeanExe.Native.translate LeanExe.Native.nativeCap $moduleId = some $translationId :=
              (Option.some_get _).symm))
            elabCommand (← `(attribute [irreducible] $translationId:ident))
            for (simple, index, wrapper) in natives do
              unless t.funcs.contains index do continue
              let implId := mkIdent (base ++ simple ++ `implements)
              let nativeId := mkIdent (target.getId ++ simple ++ `native)
              let hk ← `(LeanExe.Native.translate_mem_funcs $eqId $funcsId (by decide))
              if wrapper then
                elabCommand (← `(theorem $nativeId (A : LClight.Archi) (X : LClight.ExtSem) :
                    Verified.NativeTablesImpl $implId A X LeanExe.Native.nativeCap $translationId :=
                  Verified.ImplementsTables.nativeImpl _ $eqId $hk))
              else
                elabCommand (← `(theorem $nativeId (A : LClight.Archi) (X : LClight.ExtSem) :
                    LeanExe.Native.NativeImpl $implId A X LeanExe.Native.nativeCap $translationId :=
                  LeanExe.Native.ImplementsA.nativeImpl _ $eqId $hk))
    -- The encoding, part by part: the native encoder gives the bytes of each part, and the kernel
    -- checks each function's body in its own theorem, so that one check holds one function.
    let parts ← match Wasm.Encoding.encodeParts evaluated with
      | .ok parts => pure parts
      | .error e => throwError "verified_compile: the module does not encode: {e}"
    let (secs, bodies, data) := parts
    let bytesTy := mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``UInt8)
    let bytesListTy := mkApp (Lean.mkConst ``List [.zero]) bytesTy
    -- A literal of `n` bytes is a term nested `n` deep, which the kernel checks recursively.
    let literalOptions := maxRecDepth.set (← getOptions) 100000
    liftCoreM <| withReader (fun ctx => { ctx with maxRecDepth := 100000, options := literalOptions }) do
      addLiteral (base ++ `sections) bytesListTy (toExpr secs)
      addLiteral (base ++ `bodies) bytesListTy (toExpr bodies)
      addLiteral (base ++ `data) bytesTy (toExpr data)
    let sectionsId := mkIdent (base ++ `sections)
    let bodiesId := mkIdent (base ++ `bodies)
    let dataId := mkIdent (base ++ `data)
    -- Declarations take names relative to the current namespace, as `bytes` does.
    let restId := mkIdent (target.getId ++ `rest_ok)
    let dataOkId := mkIdent (target.getId ++ `data_ok)
    let countId := mkIdent (target.getId ++ `funcs_count)
    let lengthId := mkIdent (target.getId ++ `funcs_length)
    let codesId := mkIdent (target.getId ++ `codes_ok)
    let nb := bodies.length
    -- The kernel walks lists of bytes recursively, as the file theorems' comparisons do.
    elabCommand (← `(set_option maxRecDepth 100000 in
      theorem $restId : Wasm.Encoding.restOk $moduleId $sectionsId = true := by
        decide +kernel))
    elabCommand (← `(set_option maxRecDepth 100000 in
      theorem $dataOkId : Wasm.Encoding.dataOk $moduleId $dataId = true := by
        decide +kernel))
    elabCommand (← `(theorem $countId : ($moduleId).funcs.length = $(Lean.quote nb) := by
      decide +kernel))
    elabCommand (← `(theorem $lengthId : ($moduleId).funcs.length = ($bodiesId).length := by
      decide +kernel))
    elabCommand (← `(set_option maxRecDepth 100000 in
      theorem $codesId : Wasm.Encoding.codesOk $bodiesId = true := by
        decide +kernel))
    let P ← `(fun k : Nat => Wasm.Encoding.funcOk ($moduleId).funcs[k]! ($bodiesId)[k]! = true)
    let mut chain ← `(Wasm.Encoding.forall_lt_zero $P)
    for k in [0:nb] do
      trace[Verified.reflect] "encode function {k}"
      let funcId := mkIdent (target.getId ++ Name.mkSimple s!"func_ok_{k}")
      elabCommand (← `(set_option maxRecDepth 100000 in
        theorem $funcId :
          Wasm.Encoding.funcOk ($moduleId).funcs[$(Lean.quote k)]! ($bodiesId)[$(Lean.quote k)]! =
            true := by
          decide +kernel))
      chain ← `(Wasm.Encoding.forall_lt_succ (P := $P) (n := $(Lean.quote k)) $chain $funcId)
    let encodingId := mkIdent (target.getId ++ `encoding)
    let encodedId := mkIdent (target.getId ++ `encoded)
    elabCommand (← `(noncomputable def $encodingId : List UInt8 :=
      Wasm.Encoding.assemble $sectionsId $bodiesId $dataId))
    elabCommand (← `(theorem $encodedId : Wasm.Encoding.encode $moduleId = .ok ⟨($encodingId).toArray⟩ ∧
        ∀ f ∈ ($moduleId).funcs, f.locals.length ≤ Wasm.Encoding.Decoder.maxLocals :=
      Wasm.Encoding.encode_of_parts $moduleId $sectionsId $bodiesId $dataId $restId $dataOkId $lengthId
        $codesId
        (by rw [$countId:ident]; exact $chain)))
    let bytesId := mkIdent (target.getId ++ `bytes)
    let conj ← claims.pop.foldrM (fun c acc => `($c ∧ $acc)) claims.back!
    let impls ← proofs.pop.foldrM (fun p acc => `(⟨$p, $acc⟩)) proofs.back!
    elabCommand (← `(theorem $bytesId : ∃ bytes, Wasm.Encoding.encode $moduleId = .ok bytes ∧
        Wasm.Encoding.decode bytes = .ok $moduleId ∧ $conj := by
      obtain ⟨success, locals⟩ := $encodedId
      exact ⟨_, success, Wasm.Encoding.decode_encode $moduleId _ locals success, $impls⟩))
  | _ => throwUnsupportedSyntax

end Verified.Reflect
