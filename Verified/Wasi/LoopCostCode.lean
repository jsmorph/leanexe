import Verified.Wasi.ResourceCompilerCost
import Verified.Wasi.ConditionalCost

namespace Verified.Wasi.Resource

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem PureContext.loopTestReturnCost (pure : PureContext pureSigs) (depth : UInt64)
    (slots : List Slot) (live : Nat → Bool) (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type))
    (env : Env context) (index : UInt64) (state : type.denote) (base : Nat)
    (store : Store Unit) (locals : Locals) :
    returnCost pure.funs pure.flags (pure.callBounds depth) test (.cons state (.cons index env))
      (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots) []
      (fun i => i == 0 || shift 2 (fun j => live j || (test.uses (j + 2) || step.uses (j + 2))) i)
      store locals = pure.loopTestCost depth (slots.map Slot.mode) live test step env index.toNat state := by
  rw [pure.returnBoolCost_nil]
  rw [pure.loopTestCost_compiler depth slots live test step env index.toNat state (base + 2) (base + 1)]
  simp only [PureContext.exprCost, loopEnv, UInt64.ofNat_toNat]

theorem PureContext.loopPrepareCost (pure : PureContext pureSigs) (depth : UInt64)
    (slots : List Slot) (live : Nat → Bool) (count : Expr pureSigs context .word)
    (initial : Expr pureSigs context type) (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type)) (env : Env context) :
    count.allocs pure.funs pure.flags (pure.callBounds depth) (slots.map Slot.mode) []
        (fun i => (live i || (test.uses (i + 2) || step.uses (i + 2))) || initial.uses i) env +
      (initial.allocs pure.funs pure.flags (pure.callBounds depth) (slots.map Slot.mode) []
        (fun i => live i || (test.uses (i + 2) || step.uses (i + 2))) env +
        coerceCost type (initial.mode (slots.map Slot.mode)) .owned (initial.denote pure.funs env)) =
      pure.loopInitCost depth (slots.map Slot.mode) live count initial test step env := by
  simp only [PureContext.loopInitCost, PureContext.loopCountCost, PureContext.ownedCost,
    PureContext.exprCost, loopLive_code]

theorem PureContext.loopTestFits_code (pure : PureContext pureSigs) (depth : UInt64)
    (test : Expr pureSigs (type :: .word :: context) .bool) (env : Env context)
    (index : UInt64) (state : type.denote) :
    pure.loopTestFits depth test env index.toNat state =
      test.fits pure.funs (pure.callFits depth) (.cons state (.cons index env)) := by
  simp only [PureContext.loopTestFits, PureContext.exprFits, loopEnv, UInt64.ofNat_toNat]

end Verified.Wasi.Resource
