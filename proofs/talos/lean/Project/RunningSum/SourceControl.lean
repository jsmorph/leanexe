import Project.RunningSum.Stream
import Init.Internal.Order.While

namespace Project.RunningSum.Source

open LeanExe.Examples.RunningSum (Decimal emitSum)

local instance : LawfulMonad BaseIO := LawfulMonad.mk' BaseIO
  (by intros; rfl) (by intros; rfl) (by intros; rfl)

abbrev LoopState := Option UInt32 × Decimal × ByteArray

def byteStep (byte : UInt8) (state : LoopState) : BaseIO (ForInStep LoopState) := do
  let total := state.2.1
  let pending := state.2.2
  if byte == 10 then
    match ← emitSum total pending with
    | .error code => pure (.done (some code, total, pending))
    | .ok next => pure (.yield (none, next, ByteArray.empty))
  else pure (.yield (none, total, pending.push byte))

def chunkLoop (bytes : ByteArray) (state : LoopState) : BaseIO LoopState :=
  forIn (List.range bytes.size) state (fun i => byteStep bytes[i]!)

def readStep (_ : Unit) (state : LoopState) : BaseIO (ForInStep LoopState) := do
  let total := state.2.1
  let pending := state.2.2
  match ← LeanExe.ByteIO.read 4096 18446744073709551615 with
  | .error code => pure (.done (some code, total, pending))
  | .ok bytes =>
    if bytes.size == 0 then
      if pending.size == 0 then pure (.done (some 0, total, pending))
      else
        match ← emitSum total pending with
        | .error code => pure (.done (some code, total, pending))
        | .ok _ => pure (.done (some 0, total, pending))
    else
      let next ← chunkLoop bytes (none, total, pending)
      match next.1 with
      | some code => pure (.done (some code, next.2))
      | none => pure (.yield (none, next.2))

def readLoop (state : LoopState) : BaseIO LoopState :=
  Lean.Loop.forIn (m := BaseIO) {} state readStep

theorem readLoop_eq (state : LoopState) : readLoop state = (do
    match ← readStep () state with
    | .done next => pure next
    | .yield next => readLoop next) := by
  unfold readLoop
  rw [Lean.Loop.forIn_eq_of_monadTail]
  congr 1
  funext step
  cases step <;> rfl

theorem main_eq : LeanExe.Examples.RunningSum.main = (do
    let next ← readLoop (none, ⟨false, ByteArray.empty⟩, ByteArray.empty)
    match next.1 with
    | some code => pure code
    | none => pure 0) := by
  unfold LeanExe.Examples.RunningSum.main readLoop readStep chunkLoop byteStep
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, List.range_eq_range']
  congr 1
  · congr 1
    funext ignored state
    congr 1
    funext result
    cases result with
    | error code => rfl
    | ok bytes =>
      simp only
      split
      · split
        · rfl
        · congr 1
      · congr 1
        funext state
        cases state.1 <;> rfl
  · funext state
    cases state.1 <;> rfl

theorem chunkLoop_eq (bytes : ByteArray) (state : LoopState) :
    chunkLoop bytes state = forIn bytes.data.toList state byteStep := by
  have hbytes : (List.range bytes.size).map (fun i => bytes[i]!) = bytes.data.toList := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, Array.length_toList]
      rfl
    · intro i hi hj
      have hi' : i < bytes.size := by simpa only [List.length_map, List.length_range] using hi
      simp only [List.getElem_map, List.getElem_range, getElem!_pos bytes i hi',
        ByteArray.getElem_eq_getElem_data, Array.getElem_toList]
  rw [← hbytes, List.forIn_map]
  rfl

#print axioms main_eq

end Project.RunningSum.Source
