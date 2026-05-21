import Lean
import LeanExe.Extract.Core
import LeanExe.Extract.Report

open Lean

namespace LeanExe.Extract.OwnershipReport

abbrev Context := LeanExe.Extract.Core.Context
abbrev Signature := LeanExe.Extract.Core.Signature
abbrev CompiledModule := LeanExe.Extract.Core.CompiledModule
abbrev IRExpr := LeanExe.IR.Expr
abbrev IRCond := LeanExe.IR.Cond
abbrev IRLocalLet := LeanExe.IR.LocalLet
abbrev IRStmt := LeanExe.IR.Stmt
abbrev IRFunc := LeanExe.IR.Func

def displayName (name : Name) : String :=
  LeanExe.Extract.Report.displayName name

def tyText (ty : LeanExe.IR.Ty) : String :=
  LeanExe.Extract.Report.tyText ty

def signatureText (sig : Signature) : String :=
  LeanExe.Extract.Report.signatureText sig

def natListText (values : List Nat) : String :=
  "[" ++ String.intercalate ", " (values.map toString) ++ "]"

def natListOrNone (values : List Nat) : String :=
  if values.isEmpty then "none" else natListText values

def childPath (path label : String) : String :=
  if path.isEmpty then label else s!"{path}.{label}"

def indexedPath (path label : String) (index : Nat) : String :=
  let indexLabel := if label.isEmpty then s!"[{index}]" else s!"{label}[{index}]"
  if path.isEmpty then
    indexLabel
  else if label.isEmpty then
    s!"{path}{indexLabel}"
  else
    s!"{path}.{indexLabel}"

def shorten (limit : Nat) (text : String) : String :=
  if text.length <= limit then
    text
  else
    String.ofList (text.toList.take limit) ++ " [truncated]"

def exprText (expr : IRExpr) : String :=
  shorten 240 (reprStr expr)

structure ReleaseSite where
  path : String
  ptr : IRExpr
  deriving Repr

structure FoldSite where
  path : String
  kind : String
  resultWidth : Nat
  accStart : Nat
  releaseOffsets : List Nat
  resultSlot : Option Nat
  targets : List Nat
  deriving Repr

structure Scan where
  statementReleases : List ReleaseSite
  explicitReleaseExprs : List ReleaseSite
  foldSites : List FoldSite
  deriving Inhabited, Repr

def Scan.empty : Scan :=
  { statementReleases := [], explicitReleaseExprs := [], foldSites := [] }

def Scan.append (left right : Scan) : Scan :=
  { statementReleases := left.statementReleases ++ right.statementReleases,
    explicitReleaseExprs := left.explicitReleaseExprs ++ right.explicitReleaseExprs,
    foldSites := left.foldSites ++ right.foldSites }

def Scan.many : List Scan → Scan :=
  List.foldl Scan.append Scan.empty

mutual
  partial def scanExpr (path : String) : IRExpr → Scan
    | .local _ => Scan.empty
    | .trap => Scan.empty
    | .u64 _ => Scan.empty
    | .u64Bin _ left right =>
        Scan.many [
          scanExpr (childPath path "left") left,
          scanExpr (childPath path "right") right
        ]
    | .ite cond thenValue elseValue =>
        Scan.many [
          scanCond (childPath path "cond") cond,
          scanExpr (childPath path "then") thenValue,
          scanExpr (childPath path "else") elseValue
        ]
    | .letE slot value body =>
        Scan.many [
          scanExpr (childPath path s!"let[{slot}].value") value,
          scanExpr (childPath path s!"let[{slot}].body") body
        ]
    | .letCall slots _ args body =>
        Scan.append
          (scanExprListFrom (childPath path s!"letCall{natListText slots}.arg") 0 args)
          (scanExpr (childPath path "letCall.body") body)
    | .letLets lets body =>
        Scan.append
          (scanLocalLetsFrom (childPath path "letLets") 0 lets)
          (scanExpr (childPath path "letLets.body") body)
    | .runtimeStat _ => Scan.empty
    | .release ptr =>
        Scan.append
          { Scan.empty with explicitReleaseExprs := [{ path := path, ptr := ptr }] }
          (scanExpr (childPath path "ptr") ptr)
    | .arrayAllocSlots _ _ cells =>
        scanExpr (childPath path "cells") cells
    | .heapAllocSlots _ _ values =>
        scanExprListFrom (childPath path "heapValue") 0 values
    | .heapLoadSlot ptr _ =>
        scanExpr (childPath path "ptr") ptr
    | .arrayReplicateSlots _ _ _ cells values =>
        Scan.append
          (scanExpr (childPath path "cells") cells)
          (scanExprListFrom (childPath path "value") 0 values)
    | .arraySize array =>
        scanExpr (childPath path "array") array
    | .arrayGetSlot _ _ array index =>
        Scan.many [
          scanExpr (childPath path "array") array,
          scanExpr (childPath path "index") index
        ]
    | .arraySetSlots _ _ _ array index values =>
        Scan.many [
          scanExpr (childPath path "array") array,
          scanExpr (childPath path "index") index,
          scanExprListFrom (childPath path "value") 0 values
        ]
    | .arrayPushSlots _ _ _ array values =>
        Scan.append
          (scanExpr (childPath path "array") array)
          (scanExprListFrom (childPath path "value") 0 values)
    | .arrayPopSlots _ _ array =>
        scanExpr (childPath path "array") array
    | .arrayAppendSlots _ _ left right =>
        Scan.many [
          scanExpr (childPath path "left") left,
          scanExpr (childPath path "right") right
        ]
    | .arrayExtractSlots _ _ array start stop =>
        Scan.many [
          scanExpr (childPath path "array") array,
          scanExpr (childPath path "start") start,
          scanExpr (childPath path "stop") stop
        ]
    | .arrayMapSlots _ _ _ _ array _ bodyValues =>
        Scan.append
          (scanExpr (childPath path "array") array)
          (scanExprListFrom (childPath path "bodyValue") 0 bodyValues)
    | .arrayFoldMultiSlot _ resultWidth _reverse array start stop initValues accStart _ bodyValues
        bodyLets bodyDone releaseOffsets resultSlot =>
        Scan.many [
          { Scan.empty with foldSites := [
              { path := path,
                kind := "arrayFoldMultiSlot",
                resultWidth := resultWidth,
                accStart := accStart,
                releaseOffsets := releaseOffsets,
                resultSlot := some resultSlot,
                targets := [] }] },
          scanExpr (childPath path "array") array,
          scanExpr (childPath path "start") start,
          scanExpr (childPath path "stop") stop,
          scanExprListFrom (childPath path "init") 0 initValues,
          scanExprListFrom (childPath path "bodyValue") 0 bodyValues,
          scanLocalLetsFrom (childPath path "bodyLet") 0 bodyLets,
          scanExpr (childPath path "bodyDone") bodyDone
        ]
    | .arrayFindIdxSlots _ array _ predicate _ =>
        Scan.append
          (scanExpr (childPath path "array") array)
          (scanExpr (childPath path "predicate") predicate)
    | .arrayFindSlot _ array _ predicate _ =>
        Scan.append
          (scanExpr (childPath path "array") array)
          (scanExpr (childPath path "predicate") predicate)
    | .arrayEqSlots _ left right _ _ predicate =>
        Scan.many [
          scanExpr (childPath path "left") left,
          scanExpr (childPath path "right") right,
          scanExpr (childPath path "predicate") predicate
        ]
    | .arrayAnySlots _ array start stop _ predicate _ =>
        Scan.many [
          scanExpr (childPath path "array") array,
          scanExpr (childPath path "start") start,
          scanExpr (childPath path "stop") stop,
          scanExpr (childPath path "predicate") predicate
        ]
    | .arrayFilterSlots _ _ array start stop _ predicate =>
        Scan.many [
          scanExpr (childPath path "array") array,
          scanExpr (childPath path "start") start,
          scanExpr (childPath path "stop") stop,
          scanExpr (childPath path "predicate") predicate
        ]
    | .arrayInsertIfInBoundsSlots _ _ _ array index values =>
        Scan.many [
          scanExpr (childPath path "array") array,
          scanExpr (childPath path "index") index,
          scanExprListFrom (childPath path "value") 0 values
        ]
    | .arrayEraseIfInBoundsSlots _ _ array index =>
        Scan.many [
          scanExpr (childPath path "array") array,
          scanExpr (childPath path "index") index
        ]
    | .arraySwapIfInBoundsSlots _ _ array left right =>
        Scan.many [
          scanExpr (childPath path "array") array,
          scanExpr (childPath path "left") left,
          scanExpr (childPath path "right") right
        ]
    | .arrayReverseSlots _ _ array =>
        scanExpr (childPath path "array") array
    | .byteArrayGet ptr len index =>
        Scan.many [
          scanExpr (childPath path "ptr") ptr,
          scanExpr (childPath path "len") len,
          scanExpr (childPath path "index") index
        ]
    | .byteArrayPushPtr ptr len value =>
        Scan.many [
          scanExpr (childPath path "ptr") ptr,
          scanExpr (childPath path "len") len,
          scanExpr (childPath path "value") value
        ]
    | .byteArrayAppendPtr leftPtr leftLen rightPtr rightLen =>
        Scan.many [
          scanExpr (childPath path "leftPtr") leftPtr,
          scanExpr (childPath path "leftLen") leftLen,
          scanExpr (childPath path "rightPtr") rightPtr,
          scanExpr (childPath path "rightLen") rightLen
        ]
    | .byteArraySetPtr ptr len index value =>
        Scan.many [
          scanExpr (childPath path "ptr") ptr,
          scanExpr (childPath path "len") len,
          scanExpr (childPath path "index") index,
          scanExpr (childPath path "value") value
        ]
    | .byteArrayFromArrayPtr array =>
        scanExpr (childPath path "array") array
    | .byteArrayCopySlicePtr srcPtr srcLen srcOff destPtr destLen destOff copyLen =>
        Scan.many [
          scanExpr (childPath path "srcPtr") srcPtr,
          scanExpr (childPath path "srcLen") srcLen,
          scanExpr (childPath path "srcOff") srcOff,
          scanExpr (childPath path "destPtr") destPtr,
          scanExpr (childPath path "destLen") destLen,
          scanExpr (childPath path "destOff") destOff,
          scanExpr (childPath path "copyLen") copyLen
        ]
    | .byteArrayEq leftPtr leftLen rightPtr rightLen =>
        Scan.many [
          scanExpr (childPath path "leftPtr") leftPtr,
          scanExpr (childPath path "leftLen") leftLen,
          scanExpr (childPath path "rightPtr") rightPtr,
          scanExpr (childPath path "rightLen") rightLen
        ]
    | .byteArrayFindIdx ptr len start _ predicate _ =>
        Scan.many [
          scanExpr (childPath path "ptr") ptr,
          scanExpr (childPath path "len") len,
          scanExpr (childPath path "start") start,
          scanExpr (childPath path "predicate") predicate
        ]
    | .byteArrayFoldMultiSlot resultWidth ptr len start stop initValues accStart _ bodyValues
        bodyLets bodyDone releaseOffsets resultSlot =>
        Scan.many [
          { Scan.empty with foldSites := [
              { path := path,
                kind := "byteArrayFoldMultiSlot",
                resultWidth := resultWidth,
                accStart := accStart,
                releaseOffsets := releaseOffsets,
                resultSlot := some resultSlot,
                targets := [] }] },
          scanExpr (childPath path "ptr") ptr,
          scanExpr (childPath path "len") len,
          scanExpr (childPath path "start") start,
          scanExpr (childPath path "stop") stop,
          scanExprListFrom (childPath path "init") 0 initValues,
          scanExprListFrom (childPath path "bodyValue") 0 bodyValues,
          scanLocalLetsFrom (childPath path "bodyLet") 0 bodyLets,
          scanExpr (childPath path "bodyDone") bodyDone
        ]
    | .rangeFoldMultiSlot resultWidth start stop step initValues accStart _ bodyValues bodyLets
        bodyDone releaseOffsets resultSlot =>
        Scan.many [
          { Scan.empty with foldSites := [
              { path := path,
                kind := "rangeFoldMultiSlot",
                resultWidth := resultWidth,
                accStart := accStart,
                releaseOffsets := releaseOffsets,
                resultSlot := some resultSlot,
                targets := [] }] },
          scanExpr (childPath path "start") start,
          scanExpr (childPath path "stop") stop,
          scanExpr (childPath path "step") step,
          scanExprListFrom (childPath path "init") 0 initValues,
          scanExprListFrom (childPath path "bodyValue") 0 bodyValues,
          scanLocalLetsFrom (childPath path "bodyLet") 0 bodyLets,
          scanExpr (childPath path "bodyDone") bodyDone
        ]
    | .loopFoldMultiSlot resultWidth initValues accStart bodyValues bodyLets bodyDone
        releaseOffsets resultSlot =>
        Scan.many [
          { Scan.empty with foldSites := [
              { path := path,
                kind := "loopFoldMultiSlot",
                resultWidth := resultWidth,
                accStart := accStart,
                releaseOffsets := releaseOffsets,
                resultSlot := some resultSlot,
                targets := [] }] },
          scanExprListFrom (childPath path "init") 0 initValues,
          scanExprListFrom (childPath path "bodyValue") 0 bodyValues,
          scanLocalLetsFrom (childPath path "bodyLet") 0 bodyLets,
          scanExpr (childPath path "bodyDone") bodyDone
        ]
    | .heapLinearPredicate ptr _ _ _ _ predicate _ _ =>
        Scan.append
          (scanExpr (childPath path "ptr") ptr)
          (scanExpr (childPath path "predicate") predicate)
    | .call _ args =>
        scanExprListFrom (childPath path "arg") 0 args

  partial def scanCond (path : String) : IRCond → Scan
    | .true => Scan.empty
    | .false => Scan.empty
    | .eqU64 left right =>
        Scan.many [
          scanExpr (childPath path "left") left,
          scanExpr (childPath path "right") right
        ]
    | .ltU64 left right =>
        Scan.many [
          scanExpr (childPath path "left") left,
          scanExpr (childPath path "right") right
        ]
    | .leU64 left right =>
        Scan.many [
          scanExpr (childPath path "left") left,
          scanExpr (childPath path "right") right
        ]
    | .not cond =>
        scanCond (childPath path "not") cond
    | .and left right =>
        Scan.many [
          scanCond (childPath path "left") left,
          scanCond (childPath path "right") right
        ]
    | .or left right =>
        Scan.many [
          scanCond (childPath path "left") left,
          scanCond (childPath path "right") right
        ]

  partial def scanExprListFrom (path : String) (index : Nat) : List IRExpr → Scan
    | [] => Scan.empty
    | expr :: rest =>
        Scan.append
          (scanExpr (indexedPath path "" index) expr)
          (scanExprListFrom path (index + 1) rest)

  partial def scanLocalLet (path : String) : IRLocalLet → Scan
    | .expr slot value =>
        scanExpr (childPath path s!"expr[{slot}]") value
    | .call slots _ args =>
        scanExprListFrom (childPath path s!"call{natListText slots}.arg") 0 args
    | .slots slots values =>
        scanExprListFrom (childPath path s!"slots{natListText slots}.value") 0 values
    | .branch cond thenLets elseLets =>
        Scan.many [
          scanCond (childPath path "cond") cond,
          scanLocalLetsFrom (childPath path "then") 0 thenLets,
          scanLocalLetsFrom (childPath path "else") 0 elseLets
        ]

  partial def scanLocalLetsFrom (path : String) (index : Nat) : List IRLocalLet → Scan
    | [] => Scan.empty
    | localLet :: rest =>
        Scan.append
          (scanLocalLet (indexedPath path "" index) localLet)
          (scanLocalLetsFrom path (index + 1) rest)

  partial def scanStmt (path : String) : IRStmt → Scan
    | .skip => Scan.empty
    | .assign index value =>
        scanExpr (childPath path s!"assign[{index}]") value
    | .call slots _ args =>
        scanExprListFrom (childPath path s!"call{natListText slots}.arg") 0 args
    | .release ptr =>
        Scan.append
          { Scan.empty with statementReleases := [{ path := path, ptr := ptr }] }
          (scanExpr (childPath path "ptr") ptr)
    | .arrayFoldMultiSlotAssign _ resultWidth _reverse array start stop initValues accStart _ bodyValues
        bodyLets bodyDone releaseOffsets targets =>
        Scan.many [
          { Scan.empty with foldSites := [
              { path := path,
                kind := "arrayFoldMultiSlotAssign",
                resultWidth := resultWidth,
                accStart := accStart,
                releaseOffsets := releaseOffsets,
                resultSlot := none,
                targets := targets }] },
          scanExpr (childPath path "array") array,
          scanExpr (childPath path "start") start,
          scanExpr (childPath path "stop") stop,
          scanExprListFrom (childPath path "init") 0 initValues,
          scanExprListFrom (childPath path "bodyValue") 0 bodyValues,
          scanLocalLetsFrom (childPath path "bodyLet") 0 bodyLets,
          scanExpr (childPath path "bodyDone") bodyDone
        ]
    | .byteArrayFoldMultiSlotAssign resultWidth ptr len start stop initValues accStart _
        bodyValues bodyLets bodyDone releaseOffsets targets =>
        Scan.many [
          { Scan.empty with foldSites := [
              { path := path,
                kind := "byteArrayFoldMultiSlotAssign",
                resultWidth := resultWidth,
                accStart := accStart,
                releaseOffsets := releaseOffsets,
                resultSlot := none,
                targets := targets }] },
          scanExpr (childPath path "ptr") ptr,
          scanExpr (childPath path "len") len,
          scanExpr (childPath path "start") start,
          scanExpr (childPath path "stop") stop,
          scanExprListFrom (childPath path "init") 0 initValues,
          scanExprListFrom (childPath path "bodyValue") 0 bodyValues,
          scanLocalLetsFrom (childPath path "bodyLet") 0 bodyLets,
          scanExpr (childPath path "bodyDone") bodyDone
        ]
    | .rangeFoldMultiSlotAssign resultWidth start stop step initValues accStart _ bodyValues
        bodyLets bodyDone releaseOffsets targets =>
        Scan.many [
          { Scan.empty with foldSites := [
              { path := path,
                kind := "rangeFoldMultiSlotAssign",
                resultWidth := resultWidth,
                accStart := accStart,
                releaseOffsets := releaseOffsets,
                resultSlot := none,
                targets := targets }] },
          scanExpr (childPath path "start") start,
          scanExpr (childPath path "stop") stop,
          scanExpr (childPath path "step") step,
          scanExprListFrom (childPath path "init") 0 initValues,
          scanExprListFrom (childPath path "bodyValue") 0 bodyValues,
          scanLocalLetsFrom (childPath path "bodyLet") 0 bodyLets,
          scanExpr (childPath path "bodyDone") bodyDone
        ]
    | .loopFoldMultiSlotAssign resultWidth initValues accStart bodyValues bodyLets bodyDone
        releaseOffsets targets =>
        Scan.many [
          { Scan.empty with foldSites := [
              { path := path,
                kind := "loopFoldMultiSlotAssign",
                resultWidth := resultWidth,
                accStart := accStart,
                releaseOffsets := releaseOffsets,
                resultSlot := none,
                targets := targets }] },
          scanExprListFrom (childPath path "init") 0 initValues,
          scanExprListFrom (childPath path "bodyValue") 0 bodyValues,
          scanLocalLetsFrom (childPath path "bodyLet") 0 bodyLets,
          scanExpr (childPath path "bodyDone") bodyDone
        ]
    | .ite cond thenStmt elseStmt =>
        Scan.many [
          scanCond (childPath path "cond") cond,
          scanStmt (childPath path "then") thenStmt,
          scanStmt (childPath path "else") elseStmt
        ]
    | .seq first second =>
        Scan.many [
          scanStmt (childPath path "first") first,
          scanStmt (childPath path "second") second
        ]
    | .while cond body =>
        Scan.many [
          scanCond (childPath path "cond") cond,
          scanStmt (childPath path "body") body
        ]
end

def scanFunc (func : IRFunc) : Scan :=
  Scan.append
    (scanStmt "body" func.body)
    (scanExprListFrom "result" 0 func.results)

def signatureForFunc? (ctx : Context) (func : IRFunc) : Option Signature :=
  if func.exportName.isSome then
    match ctx.env.find? func.sourceName with
    | some info => LeanExe.Extract.Core.supportedEntryFunction? ctx.env info
    | none => none
  else
    LeanExe.Extract.Core.functionSignature? ctx func.sourceName

def resultOwnerOffsets (func : IRFunc) (sig : Signature) : List Nat :=
  if func.exportName.isSome then [] else LeanExe.Extract.Core.tyReleaseOwnerSlotOffsets sig.result

def returnedOwnerExprLines (func : IRFunc) (offsets : List Nat) : List String :=
  offsets.filterMap fun offset =>
    match func.results[offset]? with
    | some expr => some s!"  - result[{offset}]: {exprText expr}"
    | none => none

def renderReleaseSites (label : String) (sites : List ReleaseSite) : List String :=
  if sites.isEmpty then
    [s!"{label}: none"]
  else
    [s!"{label}: {sites.length}"] ++
      sites.map (fun site => s!"  - {site.path}: {exprText site.ptr}")

def renderResultSlot : Option Nat → String
  | some slot => s!", resultSlot={slot}"
  | none => ""

def renderTargets (targets : List Nat) : String :=
  if targets.isEmpty then "" else s!", targets={natListText targets}"

def renderFoldSite (site : FoldSite) : String :=
  s!"  - {site.path}: {site.kind}, resultWidth={site.resultWidth}, accStart={site.accStart}, releaseOffsets={natListText site.releaseOffsets}{renderResultSlot site.resultSlot}{renderTargets site.targets}"

def renderFoldSites (sites : List FoldSite) : List String :=
  if sites.isEmpty then
    ["fold accumulator release offsets: none"]
  else
    ["fold accumulator release offsets:"] ++ sites.map renderFoldSite

def exportText : Option String → String
  | some name => name
  | none => "none"

def functionReport (compiled : CompiledModule) (item : IRFunc × Nat) : List String :=
  let func := item.fst
  let index := item.snd
  let sig? := signatureForFunc? compiled.ctx func
  let scan := scanFunc func
  let freshOffsets :=
    match compiled.ctx.freshResultOwnerOffsets[index]? with
    | some offsets => offsets
    | none => []
  let ownerOffsets :=
    match sig? with
    | some sig => resultOwnerOffsets func sig
    | none => []
  let returnedLines := returnedOwnerExprLines func ownerOffsets
  let returnedOwnerLines :=
    if returnedLines.isEmpty then
      ["returned owner expressions: none"]
    else
      ["returned owner expressions:"] ++ returnedLines
  [
    "",
    s!"[{index}] {displayName func.sourceName}",
    s!"export: {exportText func.exportName}",
    s!"type: {sig?.map signatureText |>.getD "unknown"}",
    s!"locals: {func.locals}",
    s!"result owner offsets: {natListOrNone ownerOffsets}",
    s!"helper fresh result owner offsets: {natListOrNone freshOffsets}"
  ] ++
    returnedOwnerLines ++
    renderReleaseSites "compiler statement releases" scan.statementReleases ++
    renderReleaseSites "explicit release expressions" scan.explicitReleaseExprs ++
    renderFoldSites scan.foldSites

def moduleReport (moduleName entryName : Name) (compiled : CompiledModule) : String :=
  let functionLines :=
    compiled.module.funcs.toList.zipIdx.flatMap (functionReport compiled)
  String.intercalate "\n" <|
    [
      "LeanExe ownership report",
      "",
      s!"module: {displayName moduleName}",
      s!"entry: {displayName entryName}",
      s!"functions: {compiled.module.funcs.size}"
    ] ++ functionLines ++ [""]

def makeReport (moduleText entryText : String) : IO String := do
  let moduleName := LeanExe.Extract.Env.parseName moduleText
  let entryName := LeanExe.Extract.Env.parseName entryText
  let env ← LeanExe.Extract.Env.loadEnvironment moduleName
  match LeanExe.Extract.Core.compileEnvironmentWithEntryModeDetailed true env moduleName entryName with
  | .ok compiled => pure (moduleReport moduleName entryName compiled)
  | .error error => throw <| IO.userError error

end LeanExe.Extract.OwnershipReport
