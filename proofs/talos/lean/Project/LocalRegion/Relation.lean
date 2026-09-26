import Project.LocalRegion.Syntax

namespace Project.LocalRegion
open Wasm

structure FrameMap (rename : Nat → Nat) (domain : Nat → Prop)
    (Related : Locals → Locals → Prop) : Prop where
  values : ∀ {source target}, Related source target → source.values = target.values
  stack : ∀ {source target}, Related source target → ∀ values,
    Related { source with values := values } { target with values := values }
  get : ∀ {source target}, Related source target → ∀ i, domain i →
    source.get i = target.get (rename i)
  set : ∀ {source target}, Related source target → ∀ i, domain i → ∀ value,
    match source.set? i value, target.set? (rename i) value with
    | some source', some target' => Related source' target'
    | none, none => True
    | _, _ => False

inductive ContinuationRel (Related : Locals → Locals → Prop) :
    Continuation α → Continuation α → Prop
  | fallthrough {st source target} : Related source target →
      ContinuationRel Related (.Fallthrough st source) (.Fallthrough st target)
  | break {label st source target} : Related source target →
      ContinuationRel Related (.Break label st source) (.Break label st target)
  | returned (st values) : ContinuationRel Related (.Return st values) (.Return st values)
  | trap (st message) : ContinuationRel Related (.Trap st message) (.Trap st message)
  | invalid (message) : ContinuationRel Related (.Invalid message) (.Invalid message)
  | outOfFuel : ContinuationRel Related .OutOfFuel .OutOfFuel
  | returnCall (id st values) :
      ContinuationRel Related (.ReturnCall id st values) (.ReturnCall id st values)
  | throwing {tag values st source target} : Related source target →
      ContinuationRel Related (.Throwing tag values st source) (.Throwing tag values st target)

end Project.LocalRegion
