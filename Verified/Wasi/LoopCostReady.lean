import Verified.Wasi.LoopCostInvariant

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

structure LoopCostReady {World : Type} {context : List Ty} {type : Ty}
    (host : Host World) (pure : Resource.PureContext pureSigs) (program : EffectProg pureSigs effectSigs)
    (depth : UInt64) (env : Env context) (slots : List Slot) (liveIn live : Nat → Bool)
    (base : Nat) (heap : Heap) (initial : Store (Observed World)) (locals : Locals)
    (count : UInt64) (initialState : type.denote) (initialCharge : Nat) (initialFits : Bool)
    (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type))
    (index : UInt64) (decision : Bool) (current : Store (Observed World)) (currentLocals : Locals) where
  safety : LoopFrame host env slots liveIn
    (fun i => live i || (test.uses (i + 2) || step.uses (i + 2))) base heap initial locals
    count initialState
    (fun index state => test.denote pure.funs (.cons state (.cons index env)))
    (fun index state => step.denote pure.funs (program.funs pure.funs) (.cons state (.cons index env)))
    index current currentLocals
  spent : Nat
  fits : Bool
  history : Resource.ResourceLoopHead (observedHost host) pure program depth (slots.map Slot.mode) live
    test step env count.toNat 0 initialState initial.host (count.toNat - index.toNat) index.toNat
    safety.state current.host safety.trace spent fits
  bound : index < count
  choice : test.denote pure.funs (Resource.loopEnv env index.toNat safety.state) = decision
  top : initialFits = true → fits = true →
    pure.loopTestFits depth test env index.toNat safety.state = true →
    safety.currentHeap.top.toNat ≤ heap.top.toNat + initialCharge + spent +
      pure.loopTestCost depth (slots.map Slot.mode) live test step env index.toNat safety.state

namespace LoopCostFrame

def tested {World : Type} {context : List Ty} {type : Ty} {host : Host World}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs} {depth : UInt64}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat} {heap : Heap}
    {initial : Store (Observed World)} {locals : Locals} {count index : UInt64}
    {initialState : type.denote} {initialCharge : Nat} {initialFits : Bool}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
    {current final : Store (Observed World)} {currentLocals finalLocals : Locals} {finalHeap : Heap}
    {decision : Bool}
    (frame : LoopCostFrame host pure program depth env slots liveIn live base heap initial locals
      count initialState initialCharge initialFits test step index current currentLocals)
    (bound : index < count)
    (choice : test.denote pure.funs (Resource.loopEnv env index.toNat frame.safety.state) = decision)
    (after : After env slots liveIn (fun i => live i || (test.uses (i + 2) || step.uses (i + 2)))
      base heap initial locals (.value type) frame.safety.state finalHeap final finalLocals frame.safety.words)
    (localFrame : Frame (base + 2 + type.width) currentLocals finalLocals)
    (sameWorld : final.host = current.host) (sameStack : finalLocals.values = currentLocals.values)
    (growth : pure.loopTestFits depth test env index.toNat frame.safety.state = true →
      finalHeap.top.toNat ≤ frame.safety.currentHeap.top.toNat +
        pure.loopTestCost depth (slots.map Slot.mode) live test step env index.toNat frame.safety.state) :
    LoopCostReady host pure program depth env slots liveIn live base heap initial locals count initialState
      initialCharge initialFits test step index decision final finalLocals := by
  refine ⟨frame.safety.retest after localFrame sameWorld sameStack, frame.spent, frame.fits,
    ?_, bound, choice, ?_⟩
  · rw [sameWorld]
    exact frame.history
  · intro initialValid historyValid testValid
    change finalHeap.top.toNat ≤ heap.top.toNat + initialCharge + frame.spent +
      pure.loopTestCost depth (slots.map Slot.mode) live test step env index.toNat frame.safety.state
    have first := frame.top initialValid historyValid
    have last := growth testValid
    omega

end LoopCostFrame

namespace LoopCostReady

theorem body_resources {World : Type} {context : List Ty} {type : Ty} {host : Host World}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs} {depth : UInt64}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat} {heap : Heap}
    {initial : Store (Observed World)} {locals : Locals} {count index : UInt64}
    {initialState : type.denote} {initialCharge : Nat} {initialFits : Bool}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
    {current : Store (Observed World)} {currentLocals : Locals}
    (frame : LoopCostReady host pure program depth env slots liveIn live base heap initial locals
      count initialState initialCharge initialFits test step index true current currentLocals)
    {source : Wasm.Module} {budget : Nat}
    (within : heap.Within (PureTransport.erase initial) source budget)
    (initialBound : initialCharge ≤ budget) (initialValid : initialFits = true)
    (bounded : Resource.LoopPrefixBound (observedHost host) pure program depth (slots.map Slot.mode) live
      test step env count.toNat 0 initialState initial.host (budget - initialCharge)) :
    frame.safety.currentHeap.Within (PureTransport.erase current) source
        (budget - initialCharge - frame.spent -
          pure.loopTestCost depth (slots.map Slot.mode) live test step env index.toNat frame.safety.state) ∧
      Resource.PrefixBound (observedHost host) pure program depth (Resource.loopModes .owned (slots.map Slot.mode))
        (shift 2 (Resource.loopLive test step live)) step
        (Resource.loopEnv env index.toNat frame.safety.state) current.host
        (budget - initialCharge - frame.spent -
          pure.loopTestCost depth (slots.map Slot.mode) live test step env index.toNat frame.safety.state) := by
  obtain ⟨spentBound, historyFits⟩ := frame.history.resources bounded
  have remaining := frame.history.residualBound bounded
  rw [loop_remaining_succ frame.bound] at remaining
  obtain ⟨testBound, testFits⟩ := remaining.test
  have top := frame.top initialValid historyFits testFits
  exact ⟨within.of_le (by omega) (frame.safety.after.step.cap source), remaining.step frame.choice⟩

end LoopCostReady

end Verified.Wasi
