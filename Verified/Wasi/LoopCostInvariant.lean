import Verified.Wasi.LoopInvariant
import Verified.Wasi.ResourceLoopHead
import Verified.ExprSpec

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

structure LoopCostFrame {World : Type} {context : List Ty} {type : Ty}
    (host : Host World) (pure : Resource.PureContext pureSigs) (program : EffectProg pureSigs effectSigs)
    (depth : UInt64) (env : Env context) (slots : List Slot) (liveIn live : Nat → Bool)
    (base : Nat) (heap : Heap) (initial : Store (Observed World)) (locals : Locals)
    (count : UInt64) (initialState : type.denote) (initialCharge : Nat) (initialFits : Bool)
    (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type))
    (index : UInt64) (current : Store (Observed World)) (currentLocals : Locals) where
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
  top : initialFits = true → fits = true →
    safety.currentHeap.top.toNat ≤ heap.top.toNat + initialCharge + spent

namespace LoopCostFrame

variable {World : Type} {context : List Ty} {type : Ty} {host : Host World}
  {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs} {depth : UInt64}
  {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {base : Nat} {heap : Heap}
  {initial : Store (Observed World)} {locals : Locals} {count index : UInt64}
  {initialState : type.denote} {initialCharge : Nat} {initialFits : Bool}
  {test : Expr pureSigs (type :: .word :: context) .bool}
  {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
  {current : Store (Observed World)} {currentLocals : Locals}

theorem resources (frame : LoopCostFrame host pure program depth env slots liveIn live base heap initial locals
    count initialState initialCharge initialFits test step index current currentLocals)
    {source : Wasm.Module} {budget : Nat}
    (within : heap.Within (PureTransport.erase initial) source budget)
    (initialBound : initialCharge ≤ budget) (initialValid : initialFits = true)
    (bounded : Resource.LoopPrefixBound (observedHost host) pure program depth (slots.map Slot.mode) live
      test step env count.toNat 0 initialState initial.host (budget - initialCharge)) :
    frame.safety.currentHeap.Within (PureTransport.erase current) source
        (budget - initialCharge - frame.spent) ∧
      Resource.LoopPrefixBound (observedHost host) pure program depth (slots.map Slot.mode) live
        test step env (count.toNat - index.toNat) index.toNat frame.safety.state current.host
        (budget - initialCharge - frame.spent) := by
  obtain ⟨spentBound, spentFits⟩ := frame.history.resources bounded
  have top := frame.top initialValid spentFits
  refine ⟨within.of_le (by omega) (frame.safety.after.step.cap source), frame.history.residualBound bounded⟩

theorem test_resources (frame : LoopCostFrame host pure program depth env slots liveIn live base heap initial locals
    count initialState initialCharge initialFits test step index current currentLocals)
    {source : Wasm.Module} {budget : Nat} (bound : index < count)
    (within : heap.Within (PureTransport.erase initial) source budget)
    (initialBound : initialCharge ≤ budget) (initialValid : initialFits = true)
    (bounded : Resource.LoopPrefixBound (observedHost host) pure program depth (slots.map Slot.mode) live
      test step env count.toNat 0 initialState initial.host (budget - initialCharge)) :
    frame.safety.currentHeap.Within (PureTransport.erase current) source
      (pure.loopTestCost depth (slots.map Slot.mode) live test step env index.toNat frame.safety.state) ∧
      pure.loopTestFits depth test env index.toNat frame.safety.state = true := by
  obtain ⟨currentWithin, remaining⟩ := frame.resources within initialBound initialValid bounded
  rw [loop_remaining_succ bound] at remaining
  obtain ⟨testBound, testFits⟩ := remaining.test
  exact ⟨currentWithin.mono testBound, testFits⟩

end LoopCostFrame

end Verified.Wasi
