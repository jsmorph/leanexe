import Verified.Wasi.CommandBind
import Verified.Locals

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem After.lower {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn live : Nat → Bool} {base upper : Nat}
    {heap finalHeap : Heap} {initial final : Store World} {locals finalLocals : Locals}
    {result : ResultTy} {value : result.denote} {words : List Value}
    (after : After env slots liveIn live upper heap initial locals result value
      finalHeap final finalLocals words)
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (selected : ∀ i, live i = true → liveIn i = true) (below : base ≤ upper) :
    After env slots liveIn live base heap initial locals result value
      finalHeap final finalLocals words :=
  ⟨after.step, after.frame.mono below, after.holds.lower vars selected, after.rep, after.apart⟩

theorem ResultTy.fresh_scalar {result : ResultTy} {store : Store Unit}
    {words : List Value} {value : result.denote} (scalar : result.scalar = true) :
    result.fresh store words value = [] := by
  cases result with
  | unit => rfl
  | value type =>
      change Mode.owned.fresh store type words value = []
      exact Mode.fresh_scalar (mode := .owned) (store := store) scalar words value

theorem After.thenEmpty {World : Type} {context : List Ty} {env : Env context}
    {slots : List Slot} {liveIn liveMid live : Nat → Bool} {base : Nat}
    {heap middleHeap finalHeap : Heap} {initial middle final : Store World}
    {locals middleLocals finalLocals : Locals} {firstResult result : ResultTy}
    {firstValue : firstResult.denote} {value : result.denote} {firstWords words : List Value}
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (first : After env slots liveIn liveMid base heap initial locals firstResult firstValue
      middleHeap middle middleLocals firstWords)
    (empty : firstResult.fresh (PureTransport.erase middle) firstWords firstValue = [])
    (second : After env slots liveMid live base middleHeap middle middleLocals
      result value finalHeap final finalLocals words)
    (midSelected : ∀ i, liveMid i = true → liveIn i = true)
    (selected : ∀ i, live i = true → liveMid i = true) :
    After env slots liveIn live base heap initial locals result value
      finalHeap final finalLocals words := by
  have unitFirst : After env slots liveIn liveMid base heap initial locals .unit ()
      middleHeap middle middleLocals [] :=
    ⟨by
        have step := first.step
        rw [empty] at step
        exact step,
      first.frame, first.holds, rfl, trivial⟩
  exact After.thenUnit vars apart unitFirst second midSelected selected

theorem wp_sequence_value {World : Type} {host : Host World}
    {context : List Ty} {env : Env context} {slots : List Slot}
    {liveIn liveMid bodyIn live : Nat → Bool} {base h : Nat} {type : Ty} {result : ResultTy}
    {first : Action type.denote} {next : type.denote → Action result.denote}
    {heap : Heap} {initial : Store (Observed World)} {locals : Locals}
    {aborts : Bool} {target : Wasm.Module} {targetHost : HostEnv (Observed World)}
    {firstCode nextCode : Program}
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (apart : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (positions : locals.positions = h) (low : locals.params.length ≤ base)
    (room : base + type.width ≤ h)
    (bodySelected : ∀ i, bodyIn (i + 1) = true → liveMid i = true)
    (midSelected : ∀ i, liveMid i = true → liveIn i = true)
    (selected : ∀ i, live i = true → liveMid i = true)
    (firstRun : wp target firstCode
      (CommandResult host env slots liveIn liveMid base (.value type) first
        heap initial locals aborts) initial locals targetHost)
    (nextRun : ∀ middleHeap middle middleLocals words value trace,
      Exec (observedHost host) first initial.host trace (.returned value) middle.host →
      After env slots liveIn liveMid base heap initial locals (.value type) value
        middleHeap middle middleLocals words →
      ∀ boundLocals, Frame base middleLocals boundLocals →
      LocalsHold boundLocals base type.types words →
      boundLocals.values = locals.values →
      wp target nextCode
        (CommandResult host (.cons value env) (⟨base, .owned⟩ :: slots)
          bodyIn (shift 1 live) (base + type.width) result (next value)
          middleHeap middle boundLocals aborts) middle boundLocals targetHost) :
    wp target (firstCode ++ (storeCode h base type.types ++ nextCode))
      (CommandResult host env slots liveIn live base result (Action.bind first next)
        heap initial locals aborts) initial locals targetHost := by
  apply wp_append
  refine wp.conseq (fun continuation execution => ?_) firstRun
  cases execution with
  | returned value middleHeap middle middleLocals words trace execution after =>
      change wp target (storeCode h base type.types ++ nextCode) _ middle
        { middleLocals with values := words.reverse ++ locals.values } targetHost
      have rep : type.Rep .owned middleHeap (PureTransport.erase middle) words value := after.rep
      refine wp_storeCode words h base type.types middleLocals locals.values rep.typed
        (after.frame.positions.trans positions)
        (by rw [after.frame.params]; exact low)
        (by rw [Ty.types_length, after.frame.positions, positions]; exact room)
        (fun boundLocals frame held _ => ?_)
      have frame' : Frame base middleLocals { boundLocals with values := locals.values } :=
        ⟨frame.params, frame.length, frame.below, frame.below32⟩
      refine wp.conseq (fun continuation second => ?_)
        (nextRun middleHeap middle middleLocals words value trace execution after _ frame' held rfl)
      exact CommandResult.bind_value vars apart execution after frame' held rfl second
        bodySelected midSelected selected
  | terminal final trace outcome message execution terminal =>
      exact CommandResult.bind_trap (intermediate := .value type) (result := result)
        (liveMid := liveMid) (next := next)
        (CommandResult.terminal (result := .value type) final trace outcome message
          execution terminal) id
  | resource final trace residual allowed progress =>
      exact CommandResult.resource final trace (Action.bind residual next) allowed progress.bind

end Verified.Wasi
