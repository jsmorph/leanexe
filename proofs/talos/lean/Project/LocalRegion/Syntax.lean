import Project.FunctionRegion.Exec

/-!
# Transport across local-frame layouts

A frame relation describes reads, writes, and operand-stack replacement.
Only locals actually named by a program must be related. This supports moving
loop-carried values between parameter slots and ordinary local slots.
-/
namespace Project.LocalRegion
open Wasm

mutual
  def renameInstruction (calls slots : Nat → Nat) : Instruction → Instruction
    | .localGet i => .localGet (slots i)
    | .localSet i => .localSet (slots i)
    | .localTee i => .localTee (slots i)
    | .block p r body pt rt => .block p r (renameProgram calls slots body) pt rt
    | .loop p r body pt rt => .loop p r (renameProgram calls slots body) pt rt
    | .iff p r yes no pt rt => .iff p r (renameProgram calls slots yes)
        (renameProgram calls slots no) pt rt
    | .call i => .call (calls i)
    | inst => inst
  def renameProgram (calls slots : Nat → Nat) : Program → Program
    | [] => []
    | i :: rest => renameInstruction calls slots i :: renameProgram calls slots rest
end

mutual
  def AllowedInstruction (domain : Nat → Prop) : Instruction → Prop
    | .localGet i | .localSet i | .localTee i => domain i
    | .block _ _ body _ _ | .loop _ _ body _ _ => AllowedProgram domain body
    | .iff _ _ yes no _ _ => AllowedProgram domain yes ∧ AllowedProgram domain no
    | _ => True
  def AllowedProgram (domain : Nat → Prop) : Program → Prop
    | [] => True
    | i :: rest => AllowedInstruction domain i ∧ AllowedProgram domain rest
end

structure Frame (slots : Nat → Nat) (domain : Nat → Prop) where
  Related : Locals → Locals → Prop
  values : Related s t → t.values = s.values
  stack : Related s t → ∀ values,
    Related { s with values := values } { t with values := values }
  read : Related s t → domain i → t.get (slots i) = s.get i
  write : Related s t → domain i → ∀ value,
    Option.Rel Related (s.set? i value) (t.set? (slots i) value)

inductive Continuations (R : Locals → Locals → Prop) :
    Continuation α → Continuation α → Prop
  | next (st) (s t) : R s t → Continuations R (.Fallthrough st s) (.Fallthrough st t)
  | branch (k st) (s t) : R s t → Continuations R (.Break k st s) (.Break k st t)
  | returned (st values) : Continuations R (.Return st values) (.Return st values)
  | trap (st message) : Continuations R (.Trap st message) (.Trap st message)
  | invalid (message) : Continuations R (.Invalid message) (.Invalid message)
  | exhausted : Continuations R .OutOfFuel .OutOfFuel
  | tail (i st values) : Continuations R (.ReturnCall i st values) (.ReturnCall i st values)
  | thrown (tag values st) (s t) : R s t →
      Continuations R (.Throwing tag values st s) (.Throwing tag values st t)

end Project.LocalRegion
