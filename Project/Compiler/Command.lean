import Project.Compiler.Scalar

namespace Project.Compiler

open Lean Elab Command Meta Project.IR

/-- `leanexe_compile p := f` compiles the definition `f` and adds `p.ir`, the IR
function; `p.module`, defined as `compile [(p.ir, name)]` with `f`'s last name
component as the export name, so `f` is function 3; and `p.hints`, the
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
function, and a definition's owned parameters, inferred in list order, may receive only
moved array parameters of the caller.  A definition that calls itself other than in tail
position also gets an internal function with a depth parameter, `p.n.rec.ir`, exported as
`n.rec`; the internal functions follow the listed ones, in list order. -/
syntax (name := leanexeCompileModule) "leanexe_compile " ident " := " "[" ident,* "]" : command

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
        let mut entries := []
        let mut internals := []
        let mut owners := []
        let mut nextInternal := 2 + names.size
        -- The copy functions follow the internal functions, in the order of their first use.
        let internalCount := (← names.filterM fun name => needsInternal name).size
        let mut copies : List (Name × Nat) := []
        let mut nextCopy := 2 + names.size + internalCount
        -- What a recursive body may call: each recursive definition's internal function, and
        -- the leaves.
        let mut recInternals := []
        let mut leaves := []
        for name in names do
          let short := name.getString!
          let internal ← if ← needsInternal name then
              let index := nextInternal
              nextInternal := nextInternal + 1
              pure (some index)
            else pure none
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
          entries := entries ++ [mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero])
            (mkConst ``Func) (mkConst ``String) (mkConst irName) (toExpr short)]
          if let some (recFunc, recHints) := rec_ then
            let recName := base ++ Name.mkSimple short ++ `rec ++ `ir
            addDefinition recName (mkConst ``Func) (funcToExpr recFunc)
            addDefinition (base ++ Name.mkSimple short ++ `rec ++ `hints) (mkConst ``Hints)
              (toExpr recHints)
            internals := internals ++ [mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero])
              (mkConst ``Func) (mkConst ``String) (mkConst recName) (toExpr (short ++ ".rec"))]
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
