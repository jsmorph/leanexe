import Project.LocalRegion.Syntax

namespace Project.LocalRegion
open Wasm

def exitBlock (results : Nat) (below : List Value) : Continuation α → Continuation α
  | .Fallthrough st s => .Fallthrough st { s with values := s.values.take results ++ below }
  | .Break 0 st s => .Fallthrough st { s with values := s.values.take results ++ below }
  | .Break (k + 1) st s => .Break k st s
  | other => other

theorem exitBlock_related (frame : Frame slots domain) (results : Nat)
    (below : List Value) (h : Continuations frame.Related a b) :
    Continuations frame.Related (exitBlock results below a) (exitBlock results below b) := by
  cases h with
  | next st s t h =>
      simpa only [exitBlock, frame.values h] using
        Continuations.next st _ _ (frame.stack h (s.values.take results ++ below))
  | branch k st s t h =>
      cases k with
      | zero =>
          simpa only [exitBlock, frame.values h] using
            Continuations.next st _ _ (frame.stack h (s.values.take results ++ below))
      | succ k => exact .branch _ _ _ _ h
  | returned => exact .returned _ _
  | trap => exact .trap _ _
  | invalid => exact .invalid _
  | exhausted => exact .exhausted
  | tail => exact .tail _ _ _
  | thrown _ _ _ _ _ h => exact .thrown _ _ _ _ _ h

end Project.LocalRegion
