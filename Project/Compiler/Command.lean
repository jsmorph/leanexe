import Project.Compiler.Scalar

namespace Project.Compiler

open Lean Elab Command Meta Project.IR

/-- `leanexe_compile p := f` compiles the definition `f` and adds `p.ir`, the IR
function; `p.module`, defined as `compile [(p.ir, name)]` with `f`'s last name
component as the export name, so `f` is function 2; and `p.hints`, the
compiler's hints. -/
syntax (name := leanexeCompile) "leanexe_compile " ident " := " ident : command

def addDefinition (name : Name) (type value : Lean.Expr) : CoreM Unit :=
  addAndCompile <| .defnDecl <|
    mkDefinitionValEx name [] type value (.regular 1) .safe [name]

@[command_elab leanexeCompile]
def elabLeanexeCompile : CommandElab
  | `(leanexe_compile $target := $source) => do
      let sourceName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
      let base := (← getCurrNamespace) ++ target.getId
      let exportName := sourceName.getString!
      let funcEntry := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Func)
        (mkConst ``String)
      liftTermElabM do
        let (func, hints, _, _, _, _) ← compileDefinition sourceName
        addDefinition (base ++ `ir) (mkConst ``Func) (funcToExpr func)
        let entry := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (mkConst ``Func)
          (mkConst ``String) (mkConst (base ++ `ir)) (toExpr exportName)
        let entries := mkApp3 (mkConst ``List.cons [Level.zero]) funcEntry entry
          (mkApp (mkConst ``List.nil [Level.zero]) funcEntry)
        addDefinition (base ++ `module) (mkConst ``Wasm.Module) (mkApp (mkConst ``compile) entries)
        addDefinition (base ++ `hints) (mkConst ``Hints) (toExpr hints)
  | _ => throwUnsupportedSyntax

/-- `leanexe_compile p := [f, g, …]` compiles the listed definitions into one
module.  For each definition `f` with last name component `n`, it adds `p.n.ir`
and `p.n.hints`; it adds `p.funcs`, the list of IR functions with their export
names, and `p.module := compile p.funcs`, in which the `i`-th definition is
function `2 + i`.  A call of a listed definition compiles to a call of its
function, and a definition's owned parameters may receive only moved array parameters of the
caller.  The definitions compile callees first, in the list order among those whose callees are
compiled, so each call knows its callee's owned parameters; listed definitions that call each
other in a cycle are rejected.  A definition that calls itself other than in tail position also
gets an internal function with a depth parameter, `p.n.rec.ir`, exported as `n.rec`; the internal
functions follow the listed ones, in list order. -/
syntax (name := leanexeCompileModule) "leanexe_compile " ident " := " "[" ident,* "]" : command

/-- The listed definitions that `name` calls, other than itself: the constants of its unfolding
equation's body, and of the bodies of the `@[inline]` and reducible definitions it uses, which
the compiler unfolds. -/
partial def listedCallees (names : Array Name) (name : Name) : MetaM (List Name) := do
  let found ← unfoldedBody name fun _ body => do
    let mut seen : NameSet := {}
    let mut pending := body.getUsedConstants.toList
    let mut found := []
    while true do
      match pending with
      | [] => break
      | c :: rest =>
        pending := rest
        if seen.contains c then continue
        seen := seen.insert c
        if names.contains c then
          if c != name then found := c :: found
          continue
        let some info := (← getEnv).find? c | continue
        let unfolds := Lean.Compiler.hasInlineAttribute (← getEnv) c ||
          (← getReducibilityStatus c) == .reducible
        if unfolds then
          if let some value := info.value? then
            pending := pending ++ value.getUsedConstants.toList
    return found
  return found

/-- The order in which to compile `names`: each definition after the listed definitions it
calls, and otherwise in list order. -/
def compileOrder (names : Array Name) : MetaM (List Name) := do
  let calls ← names.toList.mapM fun name => do return (name, ← listedCallees names name)
  let mut done : List Name := []
  while done.length < names.size do
    let ready := names.toList.find? fun name =>
      !done.contains name && ((calls.lookup name).getD []).all done.contains
    let some next := ready
      | throwError "the definitions {names.toList.filter (!done.contains ·)} call each other; a module list may not contain mutual recursion"
    done := done ++ [next]
  return done

@[command_elab leanexeCompileModule]
def elabLeanexeCompileModule : CommandElab
  | `(leanexe_compile $target := [$sources,*]) => do
      let names ← sources.getElems.mapM fun source =>
        liftCoreM <| realizeGlobalConstNoOverloadWithInfo source
      let base := (← getCurrNamespace) ++ target.getId
      let callees := names.toList.zipIdx.map fun (name, i) => (name, 2 + i)
      let funcEntry := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (mkConst ``Func)
        (mkConst ``String)
      liftTermElabM do
        let mut owners := []
        -- The internal functions follow the listed ones, in list order.
        let mut internalIndex : List (Name × Nat) := []
        for name in names do
          if ← needsInternal name then
            internalIndex := internalIndex ++ [(name, 2 + names.size + internalIndex.length)]
        -- The copy functions follow the internal functions, in the order of their first use.
        let mut copies : List (Name × Nat) := []
        let mut nextCopy := 2 + names.size + internalIndex.length
        -- What a recursive body may call: each recursive definition's internal function, and
        -- the leaves.
        let mut recInternals := []
        let mut leaves := []
        let mut entryOf : List (Name × Lean.Expr) := []
        let mut internalOf : List (Name × Lean.Expr) := []
        for name in ← compileOrder names do
          let short := name.getString!
          let internal := internalIndex.lookup name
          let (func, hints, owned, rec_, copies', nextCopy') ←
            compileDefinition name callees owners internal recInternals leaves copies
              (some nextCopy)
          copies := copies'
          nextCopy := nextCopy'.getD nextCopy
          owners := (name, owned) :: owners
          match internal with
          | some index => recInternals := (name, index) :: recInternals
          | none => if isLeaf func then leaves := name :: leaves
          let irName := base ++ Name.mkSimple short ++ `ir
          addDefinition irName (mkConst ``Func) (funcToExpr func)
          addDefinition (base ++ Name.mkSimple short ++ `hints) (mkConst ``Hints) (toExpr hints)
          entryOf := (name, mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero])
            (mkConst ``Func) (mkConst ``String) (mkConst irName) (toExpr short)) :: entryOf
          if let some (recFunc, recHints) := rec_ then
            let recName := base ++ Name.mkSimple short ++ `rec ++ `ir
            addDefinition recName (mkConst ``Func) (funcToExpr recFunc)
            addDefinition (base ++ Name.mkSimple short ++ `rec ++ `hints) (mkConst ``Hints)
              (toExpr recHints)
            internalOf := (name, mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero])
              (mkConst ``Func) (mkConst ``String) (mkConst recName) (toExpr (short ++ ".rec")))
              :: internalOf
        let mut entries := names.toList.filterMap fun name => entryOf.lookup name
        let mut internals := names.toList.filterMap fun name => internalOf.lookup name
        for (type, index) in copies do
          let (children, copyHints) ← copyLayout type
          let short := type.getString!
          let copyName := base ++ Name.mkSimple short ++ `copy ++ `ir
          addDefinition copyName (mkConst ``Func)
            (mkApp2 (mkConst ``Func.copy) (toExpr children) (toExpr index))
          addDefinition (base ++ Name.mkSimple short ++ `copy ++ `hints) (mkConst ``Hints)
            (toExpr copyHints)
          internals := internals ++ [mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero])
            (mkConst ``Func) (mkConst ``String) (mkConst copyName) (toExpr (short ++ ".copy"))]
        entries := entries ++ internals
        let list := entries.foldr (init := mkApp (mkConst ``List.nil [Level.zero]) funcEntry)
          fun entry rest => mkApp3 (mkConst ``List.cons [Level.zero]) funcEntry entry rest
        addDefinition (base ++ `funcs) (mkApp (mkConst ``List [Level.zero]) funcEntry) list
        addDefinition (base ++ `module) (mkConst ``Wasm.Module)
          (mkApp (mkConst ``compile) (mkConst (base ++ `funcs)))
  | _ => throwUnsupportedSyntax

end Project.Compiler
