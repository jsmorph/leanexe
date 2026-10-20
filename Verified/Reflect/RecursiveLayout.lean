import Verified.Tree
import Lean

namespace Verified.Reflect

open Lean Meta

structure RecursiveLayout where
  name : Name
  empty : Name
  node : Name
  shape : TreeShape

def RecursiveLayout.decl (layout : RecursiveLayout) (part : Name) : Name :=
  layout.name.getPrefix ++ Name.mkSimple ("verified" ++ layout.name.getString!) ++ part

def recursiveLayout? (type : Lean.Expr) : MetaM (Option RecursiveLayout) := do
  let .const name _ ← withReducible (whnf type) | return none
  if name == ``Nat || name == ``Int then return none
  let some (.inductInfo info) := (← getEnv).find? name | return none
  unless info.isRec && info.numParams == 0 && info.numIndices == 0 &&
      info.numNested == 0 && info.all.length == 1 && info.ctors.length == 2 &&
      info.levelParams.isEmpty do return none
  let ctors ← info.ctors.mapM fun ctor => do
    let fields ← forallTelescope (← getConstInfoCtor ctor).type fun xs _ => xs.toList.mapM inferType
    return (ctor, fields)
  let some (empty, _) := ctors.find? (·.2.isEmpty) | return none
  let some (node, fields) := ctors.find? (!·.2.isEmpty) | return none
  let mut bits := []
  for field in fields do
    let field ← withReducible (whnf field)
    if field.isConstOf ``UInt64 then bits := bits ++ [false]
    else if field.isConstOf name then bits := bits ++ [true]
    else return none
  if hn : bits ≠ [] then
    if hs : bits.length ≤ 64 then return some ⟨name, empty, node, ⟨bits, hn, hs⟩⟩
  return none

end Verified.Reflect
