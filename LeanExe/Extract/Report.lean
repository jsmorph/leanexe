import Lean
import LeanExe.Core
import LeanExe.Extract.Core
import LeanExe.Examples.Collatz

open Lean

namespace LeanExe.Extract.Report

structure Classification where
  status : String
  reason : String
  deriving Inhabited, BEq, Repr

structure DeclReport where
  name : Name
  kind : String
  classification : Classification
  deps : Array Name
  deriving Inhabited, Repr

structure GraphState where
  seen : NameSet := {}
  nodes : Array DeclReport := #[]
  frontier : Array DeclReport := #[]
  deriving Inhabited

def parseName (s : String) : Name :=
  s.splitOn "." |>.foldl
    (fun acc part => if part.isEmpty then acc else Name.str acc part)
    .anonymous

def displayName (n : Name) : String :=
  n.toString (escape := false)

def rootName (n : Name) : Name :=
  n.getRoot

def rootString (n : Name) : String :=
  displayName n.getRoot

def pushName (names : Array Name) (name : Name) : Array Name :=
  if names.contains name then names else names.push name

def sortNames (names : Array Name) : Array Name :=
  names.qsort (fun left right => displayName left < displayName right)

def namesToString (names : Array Name) : String :=
  if names.isEmpty then
    "none"
  else
    String.intercalate ", " (names.toList.map displayName)

def usedConstantsOf (info : ConstantInfo) : Array Name :=
  let fromType := info.type.getUsedConstants
  let fromValue :=
    match info.value? with
    | some value => value.getUsedConstants
    | none =>
        match info with
        | .inductInfo val => val.ctors.toArray
        | .ctorInfo val => #[val.induct]
        | .recInfo val => val.all.toArray
        | .opaqueInfo val => val.value.getUsedConstants
        | _ => #[]
  sortNames <| fromValue.foldl pushName fromType

def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def isConstNamed (expr : Expr) (name : Name) : Bool :=
  expr.consumeMData.getAppFn.isConstOf name

def typeIsByteArrayToBool (expr : Expr) : Bool :=
  match expr.consumeMData with
  | .forallE _ domain body _ =>
      isConstNamed domain ``ByteArray && isConstNamed body ``Bool
  | _ => false

def typeIsUInt64ToUInt64 (expr : Expr) : Bool :=
  match expr.consumeMData with
  | .forallE _ domain body _ =>
      isConstNamed domain ``UInt64 && isConstNamed body ``UInt64
  | _ => false

partial def hasFunctionDomain (expr : Expr) : Bool :=
  match expr.consumeMData with
  | .forallE _ domain body _ =>
      domain.consumeMData.isForall || hasFunctionDomain domain || hasFunctionDomain body
  | .lam _ domain body _ => hasFunctionDomain domain || hasFunctionDomain body
  | .letE _ type value body _ =>
      hasFunctionDomain type || hasFunctionDomain value || hasFunctionDomain body
  | .app fn arg => hasFunctionDomain fn || hasFunctionDomain arg
  | .mdata _ body => hasFunctionDomain body
  | .proj _ _ body => hasFunctionDomain body
  | _ => false

def effectRoots : List String :=
  ["IO", "EIO", "BaseIO", "Task"]

def exprUsesEffect (expr : Expr) : Bool :=
  expr.getUsedConstants.any (fun name => effectRoots.contains (rootString name))

def infoUsesEffect (info : ConstantInfo) : Bool :=
  exprUsesEffect info.type ||
    match info.value? with
    | some value => exprUsesEffect value
    | none => false

def validatorImplementedNames : List Name :=
  [
    ``LeanExe.Examples.AsciiDigits.isAsciiDigit,
    ``LeanExe.Examples.AsciiDigits.validate,
    ``LeanExe.Examples.AsciiDigits.WellFormed,
    ``LeanExe.Core.asciiDigits,
    ``LeanExe.Core.lower
  ]

def knownExternal? (name : Name) : Option Classification :=
  let root := rootString name
  if effectRoots.contains root then
    some { status := "rejected", reason := "unsupported effect dependency" }
  else if [``Bool, ``UInt8, ``UInt32, ``UInt64, ``ByteArray, ``Unit].contains name then
    some { status := "implemented", reason := "primitive type in the intended subset" }
  else if name == ``Array then
    some { status := "implemented", reason := "implemented for Array UInt64 in the generic compiler fragment" }
  else if [``Nat, ``Option, ``Except, ``String, ``List].contains name then
    some { status := "reported", reason := "planned type or library type" }
  else if [``And, ``Or, ``True, ``False, ``Eq].contains name then
    some { status := "reported", reason := "logical connective in a decidable predicate" }
  else if [``Bool.and, ``Bool.or, ``Bool.not, ``Bool.true, ``Bool.false].contains name then
    some { status := "implemented", reason := "boolean primitive in the generic compiler fragment" }
  else if [``BEq.beq, ``LT.lt, ``LE.le, ``ite].contains name then
    some { status := "implemented", reason := "control, equality, or comparison primitive in the generic compiler fragment" }
  else if [``Array.replicate, ``Array.get!Internal, ``Array.set!, ``GetElem?.getElem!].contains name then
    some { status := "implemented", reason := "Array UInt64 primitive in the generic compiler fragment" }
  else if [``ByteArray.size, ``ByteArray.get!].contains name then
    some { status := "implemented", reason := "read-only ByteArray primitive in the generic compiler fragment" }
  else if name == ``Array.size then
    some { status := "reported", reason := "indexing validity predicate erased by array primitive lowering" }
  else if [``UInt64.toNat, ``UInt8.toNat].contains name then
    some { status := "implemented", reason := "representation-preserving conversion for bounded Nat use" }
  else if [``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv, ``HMod.hMod, ``UInt64.land].contains name then
    some { status := "implemented", reason := "numeric primitive in the generic compiler fragment" }
  else if name == ``Decidable.decide then
    some { status := "reported", reason := "decidable proposition needs specialization to Bool code" }
  else if name == ``OfNat.ofNat then
    some { status := "reported", reason := "numeric literal needs target-type resolution" }
  else if (displayName name).contains "inst" then
    some { status := "reported", reason := "typeclass instance dependency requiring specialization" }
  else if root == "Nat" then
    some { status := "reported", reason := "bounded Nat use needs representation analysis" }
  else if root == "UInt8" || root == "ByteArray" || root == "List" then
    some { status := "reported", reason := "library operation needs a primitive or extracted implementation" }
  else
    none

def classifyLocal (info : ConstantInfo) : Classification :=
  if validatorImplementedNames.contains info.name then
    { status := "implemented", reason := "accepted by the validator demo compiler path" }
  else if LeanExe.Extract.Core.supportedFunction? info |>.isSome then
    {
      status := "reported",
      reason := "function type is in the first generic compiler fragment; body support is checked by compile"
    }
  else if (displayName info.name).contains ".match_" then
    {
      status := "reported",
      reason := "generated match helper; supported recursion patterns consume it during extraction"
    }
  else if info.isUnsafe then
    { status := "rejected", reason := "unsafe declaration" }
  else if info.isPartial then
    { status := "rejected", reason := "partial declaration" }
  else if infoUsesEffect info then
    { status := "rejected", reason := "unsupported effect in type or value" }
  else if hasFunctionDomain info.type then
    { status := "rejected", reason := "higher-order argument requires closure or specialization support" }
  else if !info.levelParams.isEmpty then
    { status := "reported", reason := "polymorphic declaration requires monomorphization" }
  else
    match info with
    | .defnInfo _ =>
        { status := "reported", reason := "definition body traversed, generic compilation pending" }
    | .thmInfo _ =>
        { status := "implemented", reason := "proof declaration erased from runtime extraction" }
    | .opaqueInfo _ =>
        { status := "rejected", reason := "opaque executable constant" }
    | .axiomInfo _ =>
        { status := "rejected", reason := "axiom in executable dependency graph" }
    | .quotInfo _ =>
        { status := "rejected", reason := "quotient dependency" }
    | .inductInfo _ =>
        { status := "reported", reason := "inductive layout analysis pending" }
    | .ctorInfo _ =>
        { status := "reported", reason := "constructor layout analysis pending" }
    | .recInfo _ =>
        { status := "reported", reason := "recursor lowering pending" }

def classifyExternal (name : Name) : Classification :=
  knownExternal? name |>.getD
    { status := "rejected", reason := "external dependency has no LeanExe primitive" }

def shouldExpand (moduleName entryName name : Name) : Bool :=
  name == entryName || rootName name == rootName moduleName

def addFrontier (name : Name) (classification : Classification) : StateM GraphState Unit := do
  modify fun state =>
    { state with
      frontier := state.frontier.push {
        name := name,
        kind := "external",
        classification := classification,
        deps := #[]
      }
    }

partial def visit (env : Environment) (moduleName entryName name : Name) :
    StateM GraphState Unit := do
  let state ← get
  if state.seen.contains name then
    return ()
  modify fun state => { state with seen := state.seen.insert name }
  match env.find? name with
  | none =>
      addFrontier name { status := "rejected", reason := "constant not found in imported environment" }
  | some info =>
      if shouldExpand moduleName entryName name then
        let deps := usedConstantsOf info |>.filter (fun dep => dep != name)
        modify fun state =>
          { state with
            nodes := state.nodes.push {
              name := name,
              kind := declarationKind info,
              classification := classifyLocal info,
              deps := deps
            }
          }
        for dep in deps do
          visit env moduleName entryName dep
      else
        addFrontier name (classifyExternal name)

def loadEnvironment (moduleName : Name) : IO Environment := do
  let cwd ← IO.currentDir
  let projectLean := cwd / ".lake" / "build" / "lib" / "lean"
  initSearchPath (← findSysroot) [projectLean, cwd]
  importModules #[{ module := moduleName, importAll := false, isExported := true, isMeta := false }] {}

def entryShape (env : Environment) (entryName : Name) : String :=
  match env.find? entryName with
  | none => "missing"
  | some info =>
      if typeIsByteArrayToBool info.type then
        "ByteArray -> Bool"
      else if typeIsUInt64ToUInt64 info.type then
        "UInt64 -> UInt64"
      else if isConstNamed info.type ``UInt64 then
        "UInt64"
      else if infoUsesEffect info then
        "effectful or effect-dependent"
      else if hasFunctionDomain info.type then
        "higher-order"
      else
        "unsupported or unclassified"

def compileStatus (env : Environment) (moduleName entryName : Name) : String :=
  if entryName == ``LeanExe.Examples.AsciiDigits.validate then
    "implemented by the validator demo compiler path"
  else
    match LeanExe.Extract.Core.compileEnvironment env moduleName entryName with
    | .ok _ => "implemented by the first generic scalar/array/bytearray compiler fragment"
    | .error error => s!"reported only; generic compile rejects this entry: {error}"

def renderNode (node : DeclReport) : List String :=
  [
    s!"- {displayName node.name}",
    s!"  kind: {node.kind}",
    s!"  status: {node.classification.status}",
    s!"  reason: {node.classification.reason}",
    s!"  dependencies: {namesToString node.deps}"
  ]

def renderSection (title : String) (items : Array DeclReport) : List String :=
  if items.isEmpty then
    [title, "", "- none", ""]
  else
    [title, ""] ++ (items.toList.flatMap renderNode) ++ [""]

def renderReport
    (moduleText entryText : String)
    (moduleName entryName : Name)
    (env : Environment)
    (state : GraphState) : String :=
  String.intercalate "\n" <|
    [
      "LeanExe checked-environment report",
      "",
      s!"module: {moduleText}",
      s!"entry: {entryText}",
      s!"entry shape: {entryShape env entryName}",
      s!"compile status: {compileStatus env moduleName entryName}",
      s!"expanded declarations: {state.nodes.size}",
      s!"external frontier: {state.frontier.size}",
      ""
    ]
    ++ renderSection "Expanded declarations" state.nodes
    ++ renderSection "External frontier" state.frontier
    ++ [
      "Notes",
      "",
      "The report expands declarations whose root namespace matches the imported module root.",
      "External dependencies are classified at the frontier and are not recursively expanded.",
      "Use `lean-wasm compile --module <module> --entry <name> --out <path>` for supported Wasm emission.",
      ""
    ]

def makeReport (moduleText entryText : String) : IO String := do
  let moduleName := parseName moduleText
  let entryName := parseName entryText
  let env ← loadEnvironment moduleName
  match env.find? entryName with
  | none =>
      throw <| IO.userError s!"entry not found in imported environment: {entryText}"
  | some _ =>
      let result := (visit env moduleName entryName entryName).run {}
      let state := result.snd
      pure <| renderReport moduleText entryText moduleName entryName env state

end LeanExe.Extract.Report
