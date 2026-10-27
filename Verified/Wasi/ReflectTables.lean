import Verified.Reflect.Command
import Lean.Meta.Transform

namespace Verified.Wasi.Reflect

open Lean Meta
open Verified.Reflect

structure StaticTable where
  name : Name
  index : Nat

structure TableBinding where
  table : StaticTable
  term : Lean.Expr

structure PureBinding where
  name : Name
  callee : Verified.Reflect.Callee
  tables : List StaticTable
  arity : Nat
  meaning : Name

def staticTablesOf (program : ProgramReflection) : List StaticTable :=
  program.tableNames.toList.zipIdx.map fun (name, index) => ⟨name, index⟩

def pureBindingsOf (program : ProgramReflection) : MetaM (List PureBinding) :=
  program.wraps.toList.mapM fun (wrapper, callee, indices) => do
    let tables ← indices.mapM fun index => do
      let some name := program.tableNames[index]?
        | throwError "verified_compile_wasi: wrapper {wrapper.name} has no table {index}"
      return ({ name, index } : StaticTable)
    return {
      name := wrapper.name
      callee := callee
      tables := tables
      arity := wrapper.params.length
      meaning := wrapper.meaningEq }

def tableTerm (tables : List TableBinding) (name : Name) : MetaM Lean.Expr := do
  let some binding := tables.find? (·.table.name == name)
    | throwError "verified_compile_wasi: constant table {name} has no borrowed source binding"
  return binding.term

def withStaticTables {α : Type} (context : Verified.Reflect.Ctx) : List StaticTable →
    (List TableBinding → Verified.Reflect.Ctx → MetaM α) → MetaM α
  | [], next => next [] context
  | table :: rest, next => do
    let type := mkApp (mkConst ``Array [.zero]) (mkConst ``UInt64)
    let native := mkConst table.name
    unless ← isDefEq (← inferType native) type do
      throwError "verified_compile_wasi: constant table {table.name} is not an Array UInt64"
    withLetDecl table.name type native fun term =>
      withStaticTables context rest fun bindings restContext => do
        let env ← mkAppOptM ``Env.cons
          #[some restContext.ctx, some (tyExpr (.array .word)), some term, some restContext.env]
        let extended := { restContext with
          vars := (term, .array .word) :: restContext.vars
          ctx := consCtx (.array .word) restContext.ctx
          env }
        next (⟨table, term⟩ :: bindings) extended

/-- Wrapper expansion and table aliases have a kernel-checked definitional equation.  The
table terms are local definitions of the named constants and denote borrowed source places. -/
def normalizeTables (bindings : List PureBinding) (tables : List TableBinding)
    (expression : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let normalized ← transform expression (pre := fun term => do
    if let .const name _ := term then
      if let some binding := tables.find? (·.table.name == name) then
        return .done binding.term
    let (name, args) := term.getAppFnArgs
    if let some binding := bindings.find? (·.name == name) then
      if args.size == binding.arity then
        let tableArgs ← binding.tables.mapM fun table => tableTerm tables table.name
        return .visit (mkAppN (mkConst binding.callee.name) (tableArgs.toArray ++ args))
    return .continue)
  return (normalized, ← bareEq normalized expression)

end Verified.Wasi.Reflect
