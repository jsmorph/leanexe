import Verified.Tree
import Lean

namespace Verified.Reflect

open Lean Meta

instance : ToExpr Elem where
  toExpr := go
  toTypeExpr := mkConst ``Elem
where
  go : Elem → Lean.Expr
    | .word => mkConst ``Elem.word
    | .bool => mkConst ``Elem.bool
    | .float => mkConst ``Elem.float
    | .float32 => mkConst ``Elem.float32
    | .prod a b => mkApp2 (mkConst ``Elem.prod) (go a) (go b)

instance : ToExpr TreeField where
  toExpr
    | .word e => mkApp (mkConst ``TreeField.word) (toExpr e)
    | .child => mkConst ``TreeField.child
  toTypeExpr := mkConst ``TreeField

instance : Quote Elem where
  quote := go
where
  go : Elem → Term
    | .word => Unhygienic.run `(Verified.Elem.word)
    | .bool => Unhygienic.run `(Verified.Elem.bool)
    | .float => Unhygienic.run `(Verified.Elem.float)
    | .float32 => Unhygienic.run `(Verified.Elem.float32)
    | .prod a b => Unhygienic.run `(Verified.Elem.prod $(go a) $(go b))

instance : Quote TreeField where
  quote
    | .word e => Unhygienic.run `(Verified.TreeField.word $(quote e))
    | .child => Unhygienic.run `(Verified.TreeField.child)

/-- How a field of a constructor occupies its record: a child, a word field of an element, or a
field of a type with a `Flat` instance, one word field for each leaf of its flattening.  A leaf has
an element and segments of steps, `false` for a pair's first component: its term takes the steps
of the first segment from the field, and the steps of each later segment from `Flat.flat` of the
term before. -/
inductive NativeField where
  | child
  | leaf (e : Elem)
  | flat (type : Lean.Expr) (leaves : List (Elem × List (List Bool)))
  deriving Inhabited

/-- The kinds of the slots that a field occupies. -/
def NativeField.kinds : NativeField → List TreeField
  | .child => [.child]
  | .leaf e => [.word e]
  | .flat _ leaves => leaves.map fun (e, _) => .word e

/-- The `Flat` instance of a type and its tuple type, if Lean finds one. -/
def flatInstance? (type : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let β ← mkFreshTypeMVar
  let some inst ← synthInstance? (mkApp2 (mkConst ``LeanExe.Pipeline.Flat) type β)
    | return none
  return some (← instantiateMVars β, inst)

/-- `Flat.flat x`. -/
def flatTerm (x : Lean.Expr) : MetaM Lean.Expr := do
  let type ← inferType x
  let some (β, inst) ← flatInstance? type
    | throwError "verified_compile: {type} has no `Flat` instance"
  return mkApp4 (mkConst ``LeanExe.Pipeline.Flat.flat) type β inst x

/-- The component of `value` along `steps`, `false` for a pair's first component. -/
def stepsTerm (value : Lean.Expr) : List Bool → MetaM Lean.Expr
  | [] => pure value
  | false :: rest => do stepsTerm (← mkAppM ``Prod.fst #[value]) rest
  | true :: rest => do stepsTerm (← mkAppM ``Prod.snd #[value]) rest

/-- The term of the leaf of `x` with segments `segments`. -/
def leafTerm (x : Lean.Expr) : List (List Bool) → MetaM Lean.Expr
  | [] => pure x
  | first :: rest => do
    let mut term ← stepsTerm x first
    for steps in rest do term ← stepsTerm (← flatTerm term) steps
    return term

/-- A Lean type that compiles as a recursive type: its name, its constructors in declaration order
with their fields, and its shape, whose constructors list the kinds of the fields' slots. -/
structure RecursiveLayout where
  name : Name
  ctors : List (Name × List NativeField)
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

/-- The name and fields of record constructor `r`. -/
def RecursiveLayout.recordCtor (layout : RecursiveLayout) (r : Fin layout.shape.records) :
    Name × List NativeField :=
  layout.ctors.getD (layout.shape.ctorIndex r) (.anonymous, [])

/-- The element of a field of type `field`: a word, a `Bool`, or a float of either width. -/
def fieldElem? (field : Lean.Expr) : Option Elem :=
  if field.isConstOf ``UInt64 then some .word
  else if field.isConstOf ``Bool then some .bool
  else if field.isConstOf ``Float then some .float
  else if field.isConstOf ``Float32 then some .float32
  else none

/-- The Lean type of a word field's element. -/
def elemType : Elem → Lean.Expr
  | .word => mkConst ``UInt64
  | .bool => mkConst ``Bool
  | .float => mkConst ``Float
  | .float32 => mkConst ``Float32
  | .prod a b => mkApp2 (mkConst ``Prod [.zero, .zero]) (elemType a) (elemType b)

/-- The elements and segments of the leaves of a value of `type` whose current segment has the
steps `path`: a word, a `Bool`, or a float is a leaf, a pair has the leaves of its components, and
a value of a type with a `Flat` instance has the leaves of its tuple, which start a segment. -/
partial def flatLeaves? (type : Lean.Expr) (path : List Bool) :
    MetaM (Option (List (Elem × List (List Bool)))) := do
  let type ← withReducible (whnf type)
  if let some e := fieldElem? type then return some [(e, [path])]
  if let (``Prod, #[a, b]) := type.getAppFnArgs then
    let some la ← flatLeaves? a (path ++ [false]) | return none
    let some lb ← flatLeaves? b (path ++ [true]) | return none
    return some (la ++ lb)
  let .const _ _ := type | return none
  let some (β, _) ← flatInstance? type | return none
  let some leaves ← flatLeaves? β [] | return none
  return some (leaves.map fun (e, segments) => (e, path :: segments))

/-- The field of type `field` as a flat field: a type with a `Flat` instance whose flattening holds
words, `Bool`s, and floats, such as a structure, an enumeration, or a sum. -/
def flatField? (field : Lean.Expr) : MetaM (Option NativeField) := do
  let .const _ _ := field | return none
  if (← flatInstance? field).isNone then return none
  let some leaves ← flatLeaves? field [] | return none
  return some (.flat field leaves)

/-- The layout of `type` when it is an inductive type without parameters or indices, neither
mutual nor nested, whose constructors' fields are `UInt64`, `Bool`, `Float`, `Float32`, types
whose `Flat` instance gives a tuple of these, or the type itself, and whose constructors meet
`shapeValid`. -/
def recursiveLayout? (type : Lean.Expr) : MetaM (Option RecursiveLayout) := do
  let .const name _ ← withReducible (whnf type) | return none
  if name == ``Nat || name == ``Int then return none
  let some (.inductInfo info) := (← getEnv).find? name | return none
  unless info.isRec && info.numParams == 0 && info.numIndices == 0 &&
      info.numNested == 0 && info.all.length == 1 && info.levelParams.isEmpty do return none
  let mut ctors : Array (Name × List NativeField) := #[]
  for ctor in info.ctors do
    let fields ← forallTelescope (← getConstInfoCtor ctor).type fun xs _ =>
      xs.toList.mapM inferType
    let mut natives := []
    for field in fields do
      let field ← withReducible (whnf field)
      if let some e := fieldElem? field then natives := natives ++ [.leaf e]
      else if field.isConstOf name then natives := natives ++ [.child]
      else if let some flat ← flatField? field then natives := natives ++ [flat]
      else return none
    ctors := ctors.push (ctor, natives)
  let kinds := ctors.toList.map fun (_, natives) => natives.flatMap NativeField.kinds
  if h : shapeValid kinds = true then return some ⟨name, ctors.toList, ⟨kinds, h⟩⟩
  return none

end Verified.Reflect
