import Verified.Tree
import Lean

namespace Verified.Reflect

open Lean Meta

/-- A Lean type that compiles as a recursive type: its name, its constructors in declaration order
with the kinds of their fields, `false` for a `UInt64` and `true` for a child, and its shape. -/
structure RecursiveLayout where
  name : Name
  ctors : List (Name × List Bool)
  shape : TreeShape

def RecursiveLayout.decl (layout : RecursiveLayout) (part : Name) : Name :=
  layout.name.getPrefix ++ Name.mkSimple ("verified" ++ layout.name.getString!) ++ part

/-- The name of the null constructor, when the type has one. -/
def RecursiveLayout.null? (layout : RecursiveLayout) : Option Name :=
  (nullIndex layout.shape.ctors).bind fun i => (layout.ctors[i]?).map (·.1)

/-- The record constructor that constructor `ctor` is, or `none` for the null constructor or a
name that is no constructor of the type. -/
def RecursiveLayout.record? (layout : RecursiveLayout) (ctor : Name) :
    Option (Fin layout.shape.records) := do
  let i ← layout.ctors.findIdx? (·.1 == ctor)
  let r ← (recordIndices layout.shape.ctors).findIdx? (· == i)
  if h : r < layout.shape.records then some ⟨r, h⟩ else none

/-- The name and field kinds of record constructor `r`. -/
def RecursiveLayout.recordCtor (layout : RecursiveLayout) (r : Fin layout.shape.records) :
    Name × List Bool :=
  layout.ctors.getD (layout.shape.ctorIndex r) (.anonymous, [])

/-- The layout of `type` when it is an inductive type without parameters or indices, neither
mutual nor nested, whose constructors' fields are `UInt64` or the type itself, and whose
constructors meet `shapeValid`. -/
def recursiveLayout? (type : Lean.Expr) : MetaM (Option RecursiveLayout) := do
  let .const name _ ← withReducible (whnf type) | return none
  if name == ``Nat || name == ``Int then return none
  let some (.inductInfo info) := (← getEnv).find? name | return none
  unless info.isRec && info.numParams == 0 && info.numIndices == 0 &&
      info.numNested == 0 && info.all.length == 1 && info.levelParams.isEmpty do return none
  let mut ctors : Array (Name × List Bool) := #[]
  for ctor in info.ctors do
    let fields ← forallTelescope (← getConstInfoCtor ctor).type fun xs _ =>
      xs.toList.mapM inferType
    let mut bits := []
    for field in fields do
      let field ← withReducible (whnf field)
      if field.isConstOf ``UInt64 then bits := bits ++ [false]
      else if field.isConstOf name then bits := bits ++ [true]
      else return none
    ctors := ctors.push (ctor, bits)
  let kinds := ctors.toList.map (·.2)
  if h : shapeValid kinds = true then return some ⟨name, ctors.toList, ⟨kinds, h⟩⟩
  return none

end Verified.Reflect
