import Verified.Wasi.LoopSemantics
import Verified.Wasi.LoopContext

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

structure LoopFrame {World : Type} {context : List Ty} {type : Ty}
    (host : Host World) (env : Env context) (slots : List Slot)
    (liveIn live : Nat → Bool) (base : Nat) (heap : Heap)
    (initial : Store (Observed World)) (locals : Locals) (count : UInt64)
    (initialState : type.denote) (test : UInt64 → type.denote → Bool)
    (step : UInt64 → type.denote → Action type.denote)
    (index : UInt64) (current : Store (Observed World)) (currentLocals : Locals) where
  state : type.denote
  currentHeap : Heap
  words : List Value
  trace : List Event
  progress : LoopProgress (observedHost host) count initialState test step Action.pure
    initial.host index state trace current.host
  after : After env slots liveIn live base heap initial locals (.value type) state
    currentHeap current currentLocals words
  countLocal : currentLocals.get base = some (.i64 count)
  indexLocal : currentLocals.get (base + 1) = some (.i64 index)
  held : LocalsHold currentLocals (base + 2) type.types words
  stack : currentLocals.values = locals.values

theorem loop_held_frame {type : Ty} {words : List Value} {locals finalLocals : Locals} {base : Nat}
    (held : LocalsHold locals (base + 2) type.types words) (width : words.length = type.width)
    (frame : Frame (base + 2 + type.width) locals finalLocals) :
    LocalsHold finalLocals (base + 2) type.types words := by
  intro k bound
  have below : base + 2 + k < base + 2 + type.width := by rw [width] at bound; omega
  rw [frame.positions]
  exact (frame.slot below _).trans (held k bound)

namespace LoopFrame

variable {World : Type} {context : List Ty} {type : Ty} {host : Host World}
  {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat} {heap : Heap}
  {initial : Store (Observed World)} {locals : Locals} {count index : UInt64}
  {initialState : type.denote} {test : UInt64 → type.denote → Bool}
  {step : UInt64 → type.denote → Action type.denote}
  {current final : Store (Observed World)} {currentLocals finalLocals : Locals}

def retest (frame : LoopFrame host env slots liveIn live base heap initial locals count
    initialState test step index current currentLocals) {finalHeap : Heap}
    (after : After env slots liveIn live base heap initial locals (.value type) frame.state
      finalHeap final finalLocals frame.words)
    (localFrame : Frame (base + 2 + type.width) currentLocals finalLocals)
    (sameWorld : final.host = current.host) (sameStack : finalLocals.values = currentLocals.values) :
    LoopFrame host env slots liveIn live base heap initial locals count initialState test step
      index final finalLocals := by
  refine ⟨frame.state, finalHeap, frame.words, frame.trace, ?_, after, ?_, ?_,
    loop_held_frame frame.held frame.after.rep.length localFrame, sameStack.trans frame.stack⟩
  · rw [sameWorld]
    exact frame.progress
  · exact (localFrame.below base (by omega)).1.trans frame.countLocal
  · exact (localFrame.below (base + 1) (by omega)).1.trans frame.indexLocal

def advance (frame : LoopFrame host env slots liveIn live base heap initial locals count
    initialState test step index current currentLocals)
    {finalHeap : Heap} {state : type.denote} {words : List Value} {trace : List Event}
    (bound : index < count) (runs : test index frame.state = true)
    (execution : Exec (observedHost host) (step index frame.state) current.host trace (.returned state) final.host)
    (after : After env slots liveIn live base heap initial locals (.value type) state
      finalHeap final finalLocals words)
    (localFrame : Frame (base + 2) currentLocals finalLocals)
    (held : LocalsHold finalLocals (base + 2) type.types words)
    (sameStack : finalLocals.values = currentLocals.values)
    (low : finalLocals.params.length ≤ base + 1) (high : base + 1 < finalLocals.positions)
    (room : base + 2 + type.width ≤ finalLocals.positions) :
    LoopFrame host env slots liveIn live base heap initial locals count initialState test step
      (index + 1) final (setLocal finalLocals (base + 1) (.i64 (index + 1))) := by
  let incremented := setLocal finalLocals (base + 1) (.i64 (index + 1))
  have incrementFrame : Frame (base + 1) finalLocals incremented := Frame.set low le_rfl high
  have held' : LocalsHold incremented (base + 2) type.types words :=
    held.keep (lo := base + 2) incrementFrame.positions (fun j below _ => by
      dsimp only [incremented]
      refine ⟨?_, ?_, ?_⟩ <;> rw [Locals.get_setLocal_ne (s := finalLocals) low (by omega)])
      le_rfl (by rw [after.rep.length]; exact room)
  refine ⟨state, finalHeap, words, frame.trace ++ trace,
    frame.progress.advance bound runs execution,
    after.reframe (incrementFrame.mono (by omega)), ?_, ?_, held', sameStack.trans frame.stack⟩
  · exact (incrementFrame.below base (by omega)).1.trans
      ((localFrame.below base (by omega)).1.trans frame.countLocal)
  · exact Locals.get_setLocal_same low (Locals.lt_total high)

end LoopFrame

end Verified.Wasi
