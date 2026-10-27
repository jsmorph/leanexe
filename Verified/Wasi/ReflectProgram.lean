import Verified.Wasi.ReflectDefinition

namespace Verified.Wasi

def combinedLiteralPool (pure : Prog pureSigs) (effects : EffectProg pureSigs effectSigs)
    (base : Nat) : Bytes.LiteralPool :=
  ⟨base, (pure.literals ++ effects.literals).eraseDups⟩

theorem combinedLiteralPool_pure (pure : Prog pureSigs) (effects : EffectProg pureSigs effectSigs)
    (base : Nat) : pure.Covered (combinedLiteralPool pure effects base) := by
  intro bytes present
  exact List.mem_eraseDups.mpr (List.mem_append_left _ present)

theorem combinedLiteralPool_effects (pure : Prog pureSigs) (effects : EffectProg pureSigs effectSigs)
    (base : Nat) : effects.Covered (combinedLiteralPool pure effects base) := by
  intro bytes present
  exact List.mem_eraseDups.mpr (List.mem_append_right _ present)

namespace Reflect

open Lean Meta Elab Term
open Verified.Reflect

structure ProgramReflection where
  pure : Verified.Reflect.ProgramReflection
  sigs : List EffectSig
  prog : Lean.Expr
  funs : Lean.Expr
  out : Array Reflected := #[]
  callees : List Callee := []

def pureSignatures (program : Verified.Reflect.ProgramReflection) : Lean.Expr :=
  listExpr (mkConst ``Sig) (program.sigs.map sigExpr)

def ProgramReflection.signatures (program : ProgramReflection) : Lean.Expr :=
  listExpr (mkConst ``EffectSig) (program.sigs.map effectSigExpr)

def ProgramReflection.empty (pure : Verified.Reflect.ProgramReflection) : ProgramReflection :=
  { pure
    sigs := []
    prog := mkApp (mkConst ``EffectProg.nil) (pureSignatures pure)
    funs := mkConst ``EffectFuns.nil }

def ProgramReflection.context (base : Name) (program : ProgramReflection)
    (fuel : Lean.Expr := mkNatLit 0) : MetaM Ctx := do
  let sigs := pureSignatures program.pure
  let pureContext : Verified.Reflect.Ctx :=
    { base, sigs, funs := program.pure.funs, callees := program.pure.callees,
      vars := [], ctx := ctxExpr [], env := mkConst ``Env.nil,
      tables := { sigs, prog := program.pure.prog, funs := program.pure.funs, fuel } }
  return {
    pure := pureContext
    sigs := program.signatures
    funs := program.funs
    callees := program.callees
    bindings := ← pureBindingsOf program.pure }

private def closedExpr (expression : Lean.Expr) : MetaM Lean.Expr := do
  let expression ← instantiateMVars expression
  if expression.hasExprMVar || expression.hasLevelMVar || expression.hasFVar then
    throwError "verified_compile_wasi: an expression remains open between definitions: {expression}"
  return expression

def reflectProgramFunction (base name : Name) (program : ProgramReflection)
    (fuel : Lean.Expr := mkNatLit 0) : MetaM ProgramReflection := do
  let context ← program.context base fuel
  let reflected ← reflectDefinition (base ++ Name.mkSimple name.getString!) name context
    (staticTablesOf program.pure)
  let sigs := reflected.signature :: program.sigs
  let signatures := listExpr (mkConst ``EffectSig) (sigs.map effectSigExpr)
  let prog ← closedExpr (← mkAppM ``EffectProg.cons #[mkConst reflected.function, program.prog])
  let prog ← mkExpectedTypeHint prog
    (mkApp2 (mkConst ``EffectProg) (pureSignatures program.pure) signatures)
  let funs ← closedExpr (← mkAppM ``EffectProg.funs #[program.pure.funs, prog])
  let funs ← mkExpectedTypeHint funs (mkApp (mkConst ``EffectFuns) signatures)
  for type in reflected.nativeParams do discard (closedExpr type)
  discard (closedExpr reflected.nativeResult)
  return { program with
    sigs, prog, funs
    out := program.out.push reflected
    callees := reflected.callee :: program.callees }

def tableValues (program : Verified.Reflect.ProgramReflection) : Lean.Expr :=
  let words := mkApp (mkConst ``Array [.zero]) (mkConst ``UInt64)
  listExpr words (program.tableNames.toList.map mkConst)

def tableAddresses (program : Verified.Reflect.ProgramReflection) (tables : List StaticTable) :
    MetaM (List Lean.Expr) :=
  tables.mapM fun table => mkAppM ``tableAddr #[tableValues program, mkNatLit table.index]

def hiddenTablesExpr : List Ty → List Mode → List Lean.Expr → MetaM Lean.Expr
  | params, modes, [] =>
    mkAppOptM ``HiddenTables.nil #[some (ctxExpr params), some (modesExpr modes)]
  | .array .word :: params, .borrowed :: modes, address :: rest => do
    let tail ← hiddenTablesExpr params modes rest
    mkAppM ``HiddenTables.cons #[address, tail]
  | _, _, _ => throwError "verified_compile_wasi: hidden tables require borrowed Array UInt64 parameters"

private def findFunction (program : ProgramReflection) (name : Name) : MetaM (Reflected × Nat) := do
  let some reflected := program.out.find? (·.name == name)
    | throwError "verified_compile_wasi: no reflected effectful definition {name}"
  let some index := program.callees.findIdx? (·.name == name)
    | throwError "verified_compile_wasi: no effectful callee {name}"
  return (reflected, index)

def entryExpr (program : ProgramReflection) (name : Name) : MetaM Lean.Expr := do
  let (reflected, index) ← findFunction program name
  let addresses ← tableAddresses program.pure reflected.tables
  let tables ← hiddenTablesExpr reflected.signature.params reflected.signature.modes addresses
  let callee ← effectVarAt program.signatures index
  let constructor ← LemmaApp.start ``EffectEntry.mk
    [(`effectSigs, program.signatures), (`signature, effectSigExpr reflected.signature),
      (`callee, callee), (`tables, tables)]
  constructor.finish

def mainExpr (program : ProgramReflection) (name : Name) : MetaM Lean.Expr := do
  let (reflected, index) ← findFunction program name
  unless reflected.nativeParams.isEmpty && (← isDefEq reflected.nativeResult (mkConst ``UInt64)) do
    throwError "verified_compile_wasi: main {name} must be a closed Action UInt64"
  let addresses ← tableAddresses program.pure reflected.tables
  let callee ← effectVarAt program.signatures index
  let constructor ← LemmaApp.start ``EffectMain.mk
    [(`effectSigs, program.signatures), (`name, toExpr reflected.signature.name),
      (`tables, listExpr (mkConst ``UInt64) addresses)]
  constructor.assign `callee (← mkExpectedTypeHint callee (← constructor.hypType `callee))
  constructor.finish

structure MaterializedProgram where
  base : Name
  pure : Verified.Reflect.MaterializedProgram

def materializeProgram (base : Name) (program : ProgramReflection)
    (selected : List Name) (main? : Option Name := none) : TermElabM MaterializedProgram := do
  let pool ← mkAppM ``combinedLiteralPool
    #[program.pure.prog, program.prog, ← mkAppM ``tablesEnd #[tableValues program.pure]]
  let materializedPure ← Verified.Reflect.materializeProgram (base ++ `pure) program.pure (some pool)
  let signatures := program.signatures
  addDefinition (base ++ `program)
    (mkApp2 (mkConst ``EffectProg) (pureSignatures program.pure) signatures) program.prog
  addDefinition (base ++ `funs) (mkApp (mkConst ``EffectFuns) signatures) program.funs
  for reflected in program.out do
    let (_, index) ← findFunction program reflected.name
    let callee ← effectVarAt signatures index
    addDefinition (base ++ Name.mkSimple reflected.name.getString! ++ `callee)
      (← inferType callee) callee
  addDefinition (base ++ `literalPool) (mkConst ``Bytes.LiteralPool)
    (mkConst (materializedPure.base ++ `literalPool))
  let entryType := mkApp (mkConst ``EffectEntry) signatures
  let entries ← selected.mapM fun name => do entryExpr program name
  let entries := listExpr entryType entries
  addDefinition (base ++ `entries) (mkApp (mkConst ``List [.zero]) entryType) entries
  let mainType := mkApp (mkConst ``EffectMain) signatures
  let main ← match main? with
    | none => pure (mkApp (mkConst ``Option.none [Level.zero]) mainType)
    | some name => do
      let value ← mainExpr program name
      pure (mkApp2 (mkConst ``Option.some [Level.zero]) mainType value)
  addDefinition (base ++ `mainEntry) (mkApp (mkConst ``Option [.zero]) mainType) main
  let compiled ← mkAppM ``Verified.Wasi.compile
    #[mkConst (materializedPure.base ++ `module), mkConst (base ++ `program),
      mkConst (base ++ `entries), mkConst (base ++ `mainEntry),
      mkConst (base ++ `literalPool)]
  addDefinition (base ++ `module) (mkConst ``Wasm.Module) compiled
  let pureCovered ← mkAppM ``combinedLiteralPool_pure
    #[program.pure.prog, program.prog, ← mkAppM ``tablesEnd #[tableValues program.pure]]
  let effectsCovered ← mkAppM ``combinedLiteralPool_effects
    #[program.pure.prog, program.prog, ← mkAppM ``tablesEnd #[tableValues program.pure]]
  addTheorem (base ++ `pure_covered) (← inferType pureCovered) pureCovered
  addTheorem (base ++ `effects_covered) (← inferType effectsCovered) effectsCovered
  return { base, pure := materializedPure }

end Reflect

end Verified.Wasi
