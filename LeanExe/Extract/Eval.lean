import LeanExe.Extract.Core

namespace LeanExe.Extract.Eval

open Lean
open LeanExe.Extract.Core

inductive Outcome where
  | results (values : List UInt64)
  | outsideFragment (reason : String)

def scalarTy : Ty → Bool
  | .unit => true
  | .bool => true
  | .u8 => true
  | .u32 => true
  | .u64 => true
  | .nat => true
  | _ => false

partial def scalarSlotsTy : Ty → Bool
  | .product left right => scalarSlotsTy left && scalarSlotsTy right
  | .struct _ _ fields => fields.all scalarSlotsTy
  | ty => scalarTy ty

mutual
  partial def scalarExpr : IRExpr → Bool
    | .local _ => true
    | .trap => true
    | .u64 _ => true
    | .u64Bin _ left right => scalarExpr left && scalarExpr right
    | .ite cond thenValue elseValue =>
        scalarCond cond && scalarExpr thenValue && scalarExpr elseValue
    | .letE _ value body => scalarExpr value && scalarExpr body
    | .letCall _ _ args body => args.all scalarExpr && scalarExpr body
    | .letLets lets body => lets.all scalarLocalLet && scalarExpr body
    | .rangeFoldMultiSlot _ start stop step initValues _ _ bodyValues bodyLets bodyDone _ _ =>
        scalarExpr start && scalarExpr stop && scalarExpr step &&
          initValues.all scalarExpr && bodyValues.all scalarExpr &&
          bodyLets.all scalarLocalLet && scalarExpr bodyDone
    | .loopFoldMultiSlot _ initValues _ bodyValues bodyLets bodyDone _ _ =>
        initValues.all scalarExpr && bodyValues.all scalarExpr &&
          bodyLets.all scalarLocalLet && scalarExpr bodyDone
    | .call _ args => args.all scalarExpr
    | _ => false

  partial def scalarCond : IRCond → Bool
    | .true => true
    | .false => true
    | .eqU64 left right => scalarExpr left && scalarExpr right
    | .ltU64 left right => scalarExpr left && scalarExpr right
    | .leU64 left right => scalarExpr left && scalarExpr right
    | .not cond => scalarCond cond
    | .and left right => scalarCond left && scalarCond right
    | .or left right => scalarCond left && scalarCond right

  partial def scalarLocalLet : LeanExe.IR.LocalLet → Bool
    | .expr _ value => scalarExpr value
    | .call _ _ args => args.all scalarExpr
    | .slots _ values => values.all scalarExpr
    | .branch cond thenLets elseLets =>
        scalarCond cond && thenLets.all scalarLocalLet && elseLets.all scalarLocalLet

  partial def scalarStmt : IRStmt → Bool
    | .skip => true
    | .assign _ value => scalarExpr value
    | .call _ _ args => args.all scalarExpr
    | .rangeFoldMultiSlotAssign _ start stop step initValues _ _ bodyValues bodyLets bodyDone
        _ _ =>
        scalarExpr start && scalarExpr stop && scalarExpr step &&
          initValues.all scalarExpr && bodyValues.all scalarExpr &&
          bodyLets.all scalarLocalLet && scalarExpr bodyDone
    | .loopFoldMultiSlotAssign _ initValues _ bodyValues bodyLets bodyDone _ _ =>
        initValues.all scalarExpr && bodyValues.all scalarExpr &&
          bodyLets.all scalarLocalLet && scalarExpr bodyDone
    | .ite cond thenStmt elseStmt =>
        scalarCond cond && scalarStmt thenStmt && scalarStmt elseStmt
    | .seq first second => scalarStmt first && scalarStmt second
    | .while cond body => scalarCond cond && scalarStmt body
    | _ => false
end

def scalarFunc (func : IRFunc) : Bool :=
  scalarStmt func.body && func.results.all scalarExpr

def scalarModule (module_ : IRModule) : Bool :=
  module_.funcs.all scalarFunc

def evalEntry (moduleText entryText : String) (args : List UInt64) : IO Outcome := do
  let moduleName := LeanExe.Extract.Env.parseName moduleText
  let entryName := LeanExe.Extract.Env.parseName entryText
  let env ← LeanExe.Extract.Env.loadEnvironment moduleName
  let entryInfo ←
    match env.find? entryName with
    | some info => pure info
    | none => throw <| IO.userError s!"entry not found: {entryName}"
  let sig ←
    match supportedEntryFunction? env entryInfo with
    | some sig => pure sig
    | none => throw <| IO.userError (functionTypeRejectionMessage env entryName entryInfo.type)
  if !sig.params.all scalarTy then
    return .outsideFragment s!"eval-ir accepts scalar parameters only: {entryName}"
  if !scalarSlotsTy sig.result then
    return .outsideFragment s!"eval-ir accepts scalar-slot results only: {entryName}"
  if sig.params.length != args.length then
    throw <| IO.userError
      s!"{entryName} expects {sig.params.length} arguments, got {args.length}"
  let module_ ←
    match compileEnvironment env moduleName entryName with
    | .ok module_ => pure module_
    | .error error => throw <| IO.userError error
  if !scalarModule module_ then
    return .outsideFragment s!"compiled module uses heap constructs outside the scalar IR fragment: {entryName}"
  let func ←
    match module_.funcs.toList.find? (fun func => func.sourceName == entryName) with
    | some func => pure func
    | none => throw <| IO.userError s!"entry function missing from IR module: {entryName}"
  return .results (func.evalResults module_ args)

end LeanExe.Extract.Eval
