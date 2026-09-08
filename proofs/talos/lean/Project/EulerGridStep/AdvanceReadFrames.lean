import Project.EulerGridStep.AdvanceOffsets

namespace Project.EulerGridStep.Execution
open Wasm

def advanceReadOffset (size index field : Nat) : Nat :=
  if field < 3 then previousOffset index else if field < 6 then 3 * index else nextOffset size index

def advanceReadIndex (size index field : Nat) : Nat :=
  advanceReadOffset size index field + field % 3

/-- Complete frame after each of the nine emitted reads. -/
def advanceReadStageFrame (ratio inputUnused pointer unused output : UInt64)
    (input : Array UInt64) (index : Nat) : Nat → Locals
  | 0 => advanceOffsetsFrame ratio inputUnused pointer unused output input.size index
  | field + 1 =>
    let base := advanceReadStageFrame ratio inputUnused pointer unused output input index field
    let wordIndex := advanceReadIndex input.size index field
    let locals := if field = 0 then base.locals.set 3 (.i64 ratio) else base.locals
    let locals := locals.set (4 + 3 * field) (.i64 pointer)
    let locals := locals.set (5 + 3 * field) (.i64 (UInt64.ofNat wordIndex))
    let locals := locals.set (6 + 3 * field) (.i64 (input.getD wordIndex 0))
    let locals := (locals.set 59 (.i64 pointer)).set 60 (.i64 (UInt64.ofNat wordIndex))
    let locals := if field % 3 = 0 then locals else locals.set 61 (.i64 (UInt64.ofNat wordIndex))
    { base with locals := locals, values := [] }

macro "advance_single_read_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [func35, advanceReadStageFrame, advanceReadIndex, advanceReadOffset,
        advanceOffsetsFrame, advanceEntryFrame, List.set, List.cons_append, List.nil_append,
        List.getElem?_cons_zero, List.getElem?_cons_succ, reduceIte,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod,
        Nat.add_zero, *]
    | simp (discharger := omega) [*, -UInt64.ofNat_mul, -UInt64.ofNat_add]
    | refine ⟨by omega, ?_⟩
    | (try rw [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add])

end Project.EulerGridStep.Execution
