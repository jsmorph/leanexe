import Verified.Wasi.LoopCostReady

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

namespace LoopCostReady

def advance {World : Type} {context : List Ty} {type : Ty} {host : Host World}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs} {depth : UInt64}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat} {heap : Heap}
    {initial : Store (Observed World)} {locals : Locals} {count index : UInt64}
    {initialState : type.denote} {initialCharge : Nat} {initialFits : Bool}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
    {current final : Store (Observed World)} {currentLocals finalLocals : Locals} {finalHeap : Heap}
    {state : type.denote} {words : List Value} {trace : List Event} {spent : Nat} {fits : Bool}
    (frame : LoopCostReady host pure program depth env slots liveIn live base heap initial locals
      count initialState initialCharge initialFits test step index true current currentLocals)
    (execution : Resource.ResourceExec (observedHost host) pure program depth
      (Resource.loopModes .owned (slots.map Slot.mode)) (shift 2 (Resource.loopLive test step live))
      step (Resource.loopEnv env index.toNat frame.safety.state)
      current.host trace (.returned state) final.host spent fits)
    (after : After env slots liveIn (fun i => live i || (test.uses (i + 2) || step.uses (i + 2)))
      base heap initial locals (.value type) state finalHeap final finalLocals words)
    (localFrame : Frame (base + 2) currentLocals finalLocals)
    (held : LocalsHold finalLocals (base + 2) type.types words)
    (sameStack : finalLocals.values = currentLocals.values)
    (low : finalLocals.params.length ≤ base + 1) (high : base + 1 < finalLocals.positions)
    (room : base + 2 + type.width ≤ finalLocals.positions)
    (growth : fits = true → finalHeap.top.toNat ≤ frame.safety.currentHeap.top.toNat + spent) :
    LoopCostFrame host pure program depth env slots liveIn live base heap initial locals count initialState
      initialCharge initialFits test step (index + 1) final
      (setLocal finalLocals (base + 1) (.i64 (index + 1))) := by
  have chosen : test.denote pure.funs (.cons frame.safety.state (.cons index env)) = true := by
    simpa only [Resource.loopEnv, UInt64.ofNat_toNat] using frame.choice
  have sourceExecution : Exec (observedHost host)
      (step.denote pure.funs (program.funs pure.funs) (.cons frame.safety.state (.cons index env)))
      current.host trace (.returned state) final.host := by
    simpa only [Resource.loopEnv, UInt64.ofNat_toNat] using execution.erase
  let nextSafety := frame.safety.advance frame.bound chosen sourceExecution after localFrame held sameStack low high room
  refine ⟨nextSafety,
    frame.spent + pure.loopTestCost depth (slots.map Slot.mode) live test step env index.toNat frame.safety.state + spent,
    frame.fits && pure.loopTestFits depth test env index.toNat frame.safety.state && fits, ?_, ?_⟩
  · have history := frame.history
    rw [loop_remaining_succ frame.bound] at history
    have advanced := Resource.ResourceLoopHead.next history frame.choice execution
    change Resource.ResourceLoopHead (observedHost host) pure program depth (slots.map Slot.mode) live
      test step env count.toNat 0 initialState initial.host (count.toNat - (index + 1).toNat)
      (index + 1).toNat state final.host (frame.safety.trace ++ trace)
      (frame.spent + pure.loopTestCost depth (slots.map Slot.mode) live test step env index.toNat frame.safety.state + spent)
      (frame.fits && pure.loopTestFits depth test env index.toNat frame.safety.state && fits)
    rw [loop_increment_toNat frame.bound] at advanced ⊢
    exact advanced
  · intro initialValid valid
    change finalHeap.top.toNat ≤ heap.top.toNat + initialCharge +
      (frame.spent + pure.loopTestCost depth (slots.map Slot.mode) live test step env
        index.toNat frame.safety.state + spent)
    simp only [Bool.and_eq_true] at valid
    have first := frame.top initialValid valid.1.1 valid.1.2
    have last := growth valid.2
    omega

theorem complete_stop {World : Type} {context : List Ty} {type : Ty} {host : Host World}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs} {depth : UInt64}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat} {heap : Heap}
    {initial : Store (Observed World)} {locals : Locals} {count index : UInt64}
    {initialState : type.denote} {initialCharge : Nat} {initialFits : Bool}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
    {current : Store (Observed World)} {currentLocals : Locals}
    (frame : LoopCostReady host pure program depth env slots liveIn live base heap initial locals
      count initialState initialCharge initialFits test step index false current currentLocals) :
    Resource.ResourceLoopExec (observedHost host) pure program depth (slots.map Slot.mode) live test step env
      count.toNat 0 initialState initial.host frame.safety.trace (.returned frame.safety.state) current.host
      (frame.spent + pure.loopTestCost depth (slots.map Slot.mode) live test step env index.toNat frame.safety.state)
      (frame.fits && pure.loopTestFits depth test env index.toNat frame.safety.state) := by
  have history := frame.history
  rw [loop_remaining_succ frame.bound] at history
  simpa only [List.append_nil] using
    history.complete (Resource.ResourceLoopExec.stop current.host frame.choice)

end LoopCostReady

namespace LoopCostFrame

theorem complete_done {World : Type} {context : List Ty} {type : Ty} {host : Host World}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs} {depth : UInt64}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat} {heap : Heap}
    {initial : Store (Observed World)} {locals : Locals} {count : UInt64}
    {initialState : type.denote} {initialCharge : Nat} {initialFits : Bool}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
    {current : Store (Observed World)} {currentLocals : Locals}
    (frame : LoopCostFrame host pure program depth env slots liveIn live base heap initial locals
      count initialState initialCharge initialFits test step count current currentLocals) :
    Resource.ResourceLoopExec (observedHost host) pure program depth (slots.map Slot.mode) live test step env
      count.toNat 0 initialState initial.host frame.safety.trace (.returned frame.safety.state) current.host
      frame.spent frame.fits := by
  have history := frame.history
  rw [Nat.sub_self] at history
  simpa only [List.append_nil, Nat.add_zero, Bool.and_true] using
    history.complete (Resource.ResourceLoopExec.zero current.host count.toNat frame.safety.state)

end LoopCostFrame

end Verified.Wasi
