import Verified.Wasi.ResourceBudget
import Verified.Wasi.CallArguments
import Verified.Wasi.LoopAfter

namespace Verified.Wasi.Resource

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem argumentMoves_slots (signature : EffectSig) (slots : List Slot) (live : Nat → Bool)
    (args : (i : Fin signature.params.length) → Expr pureSigs context (signature.params.get i)) :
    argumentMoves signature (slots.map Slot.mode) live args = signature.callMoves slots live args := by
  funext index
  simp only [argumentMoves, EffectSig.callMoves, modeAt, Slot.modes_getD, Expr.usesFast_eq]
  rfl

theorem argumentLive_code {signature : EffectSig} (live : Nat → Bool)
    (args : (i : Fin signature.params.length) → Expr pureSigs context (signature.params.get i)) :
    argumentLive args live = (fun i => live i || argsAny fun j => (args j).usesFast i) := by
  funext index
  simp only [argumentLive, Expr.usesFast_eq]

theorem argumentKept_code (signature : EffectSig) (slots : List Slot) (live : Nat → Bool)
    (args : (i : Fin signature.params.length) → Expr pureSigs context (signature.params.get i)) :
    argumentKept signature (slots.map Slot.mode) live args =
      (fun i => (live i || argsAny fun j => (args j).usesFast i) &&
        !(argsAny fun j => signature.callMoves slots live args j && (args j).usesFast i)) := by
  funext index
  simp only [argumentKept, argumentMoves_slots, argumentLive, Expr.usesFast_eq]

theorem PureContext.argumentCost_compiler (pure : PureContext pureSigs) (depth : UInt64)
    (signature : EffectSig) (slots : List Slot) (live : Nat → Bool)
    (args : (i : Fin signature.params.length) → Expr pureSigs context (signature.params.get i))
    (env : Env context) :
    pure.argumentCost depth (slots.map Slot.mode) live signature args env =
      Verified.Wasi.argumentCost pure.funs pure.flags (pure.callBounds depth) signature.mode args env slots
        (fun i => live i || argsAny fun j => (args j).usesFast i)
        (fun i => (live i || argsAny fun j => (args j).usesFast i) &&
          !(argsAny fun j => signature.callMoves slots live args j && (args j).usesFast i)) := by
  simp only [PureContext.argumentCost, Verified.Wasi.argumentCost,
    PureContext.exprCost, argumentKept_code, argumentLive_code]
  rfl

theorem loopLive_code (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type))
    (live : Nat → Bool) :
    loopLive test step live = (fun i => live i || (test.uses (i + 2) || step.uses (i + 2))) := by
  funext index
  simp only [loopLive, Bool.or_assoc]

theorem loopCaptured_modes (slots : List Slot) :
    (Verified.Wasi.loopCaptured slots).map Slot.mode =
      (slots.map Slot.mode).map (fun _ => .borrowed) := by
  simp only [Verified.Wasi.loopCaptured, List.map_map]
  rfl

theorem loopSlots_modes (slots : List Slot) (state counter : Nat) (stateMode : Mode) :
    ((⟨state, stateMode⟩ :: ⟨counter, .borrowed⟩ :: Verified.Wasi.loopCaptured slots) : List Slot).map Slot.mode =
      loopModes stateMode (slots.map Slot.mode) := by
  simp only [List.map_cons, loopCaptured_modes, loopModes]

theorem PureContext.loopCountCost_compiler (pure : PureContext pureSigs) (depth : UInt64)
    (slots : List Slot) (live : Nat → Bool) (count : Expr pureSigs context .word)
    (initial : Expr pureSigs context type) (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type)) (env : Env context) :
    pure.loopCountCost depth (slots.map Slot.mode) live count initial test step env =
      count.allocs pure.funs pure.flags (pure.callBounds depth) (slots.map Slot.mode) []
        (fun i => (live i || (test.uses (i + 2) || step.uses (i + 2))) || initial.usesFast i) env := by
  simp only [PureContext.loopCountCost, PureContext.exprCost, loopLive_code, Expr.usesFast_eq]

theorem PureContext.loopInitCost_compiler (pure : PureContext pureSigs) (depth : UInt64)
    (slots : List Slot) (live : Nat → Bool) (count : Expr pureSigs context .word)
    (initial : Expr pureSigs context type) (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type)) (env : Env context)
    (store : Store Unit) (locals : Locals) :
    pure.loopInitCost depth (slots.map Slot.mode) live count initial test step env =
      pure.loopCountCost depth (slots.map Slot.mode) live count initial test step env +
        Verified.Wasi.returnCost pure.funs pure.flags (pure.callBounds depth) initial env slots []
          (fun i => live i || (test.uses (i + 2) || step.uses (i + 2))) store locals := by
  rw [pure.returnCost_nil]
  simp only [PureContext.loopInitCost, loopLive_code]

theorem PureContext.loopTestCost_compiler (pure : PureContext pureSigs) (depth : UInt64)
    (slots : List Slot) (live : Nat → Bool) (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type)) (env : Env context)
    (index : Nat) (value : type.denote) (state counter : Nat) :
    pure.loopTestCost depth (slots.map Slot.mode) live test step env index value =
      test.allocs pure.funs pure.flags (pure.callBounds depth)
        (((⟨state, .borrowed⟩ :: ⟨counter, .borrowed⟩ :: Verified.Wasi.loopCaptured slots) : List Slot).map Slot.mode)
        [] (fun i => i == 0 || shift 2 (fun j => live j || (test.uses (j + 2) || step.uses (j + 2))) i)
        (loopEnv env index value) := by
  simp only [PureContext.loopTestCost, PureContext.exprCost, loopSlots_modes, loopLive_code]

theorem PureContext.word_ownedCost (pure : PureContext pureSigs) (depth : UInt64)
    (modes : List Mode) (live : Nat → Bool) (value : Expr pureSigs context .word) (env : Env context) :
    pure.ownedCost depth modes live value env = pure.exprCost depth modes live value env := by
  simp [PureContext.ownedCost, coerceCost, Ty.copyCost]

theorem PureContext.returnWordCost_nil (pure : PureContext pureSigs) (depth : UInt64)
    (slots : List Slot) (live : Nat → Bool) (value : Expr pureSigs context .word) (env : Env context)
    (store : Store Unit) (locals : Locals) :
    Verified.Wasi.returnCost pure.funs pure.flags (pure.callBounds depth) value env slots [] live store locals =
      pure.exprCost depth (slots.map Slot.mode) live value env := by
  rw [pure.returnCost_nil, pure.word_ownedCost]

theorem PureContext.readCost_compiler (pure : PureContext pureSigs) (depth : UInt64)
    (slots : List Slot) (live : Nat → Bool) (capacity : Expr pureSigs context .word) (env : Env context)
    (store : Store Unit) (locals : Locals) :
    Verified.Wasi.returnCost pure.funs pure.flags (pure.callBounds depth) capacity env slots [] live store locals +
        Verified.Wasi.readCost (capacity.denote pure.funs env) =
      pure.readCost depth (slots.map Slot.mode) live capacity env := by
  rw [pure.returnWordCost_nil]
  rfl

theorem PrefixBound.exit {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {code : Expr pureSigs context .word} {env : Env context} {world : World} {budget : Nat}
    {result : ResultTy}
    (bounded : PrefixBound host pure program depth modes live (Command.exit (result := result) code)
      env world budget) :
    pure.exprCost depth modes live code env ≤ budget ∧ pure.exprFits depth code env = true :=
  bounded _ _ _ _ _ (.exit_charge code env world)

theorem PrefixBound.write {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {modes : List Mode} {live : Nat → Bool}
    {output : Output} {bytes : Var context .bytes} {env : Env context} {world : World} {budget : Nat}
    (bounded : PrefixBound host pure program depth modes live (.write output bytes) env world budget) :
    0 ≤ budget ∧ (true : Bool) = true :=
  bounded _ _ _ _ _ (.refl program depth modes live (.write output bytes) env world)

theorem PrefixBound.ret_resources {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {slots : List Slot} {live : Nat → Bool}
    {value : Expr pureSigs context type} {env : Env context} {world : World} {budget : Nat}
    {heap : Heap} {store : Store Unit} {source : Wasm.Module} (locals : Locals)
    (bounded : PrefixBound host pure program depth (slots.map Slot.mode) live (.ret value) env world budget)
    (within : heap.Within store source budget) :
    heap.Within store source
      (Verified.Wasi.returnCost pure.funs pure.flags (pure.callBounds depth) value env slots [] live store locals) ∧
      pure.exprFits depth value env = true := by
  rw [pure.returnCost_nil]
  exact ⟨within.mono bounded.ret.1, bounded.ret.2⟩

theorem PrefixBound.read_resources {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {slots : List Slot} {live : Nat → Bool}
    {capacity : Expr pureSigs context .word} {env : Env context} {world : World} {budget : Nat}
    {heap : Heap} {store : Store Unit} {source : Wasm.Module} (locals : Locals)
    (bounded : PrefixBound host pure program depth (slots.map Slot.mode) live (.read capacity) env world budget)
    (within : heap.Within store source budget) :
    heap.Within store source
      (Verified.Wasi.returnCost pure.funs pure.flags (pure.callBounds depth) capacity env slots [] live store locals +
        Verified.Wasi.readCost (capacity.denote pure.funs env)) ∧ pure.exprFits depth capacity env = true := by
  rw [pure.readCost_compiler]
  exact ⟨within.mono bounded.read.1, bounded.read.2⟩

theorem PrefixBound.exit_resources {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {slots : List Slot} {live : Nat → Bool}
    {code : Expr pureSigs context .word} {env : Env context} {world : World} {budget : Nat} {result : ResultTy}
    {heap : Heap} {store : Store Unit} {source : Wasm.Module} (locals : Locals)
    (bounded : PrefixBound host pure program depth (slots.map Slot.mode) live
      (Command.exit (result := result) code) env world budget) (within : heap.Within store source budget) :
    heap.Within store source
      (Verified.Wasi.returnCost pure.funs pure.flags (pure.callBounds depth) code env slots [] live store locals) ∧
      pure.exprFits depth code env = true := by
  rw [pure.returnWordCost_nil]
  exact ⟨within.mono bounded.exit.1, bounded.exit.2⟩

theorem PrefixBound.write_resources {World : Type} {host : Host World} {pure : PureContext pureSigs}
    {program : EffectProg pureSigs effectSigs} {depth : UInt64} {slots : List Slot} {live : Nat → Bool}
    {output : Output} {bytes : Var context .bytes} {env : Env context} {world : World} {budget : Nat}
    {heap : Heap} {store : Store Unit} {source : Wasm.Module}
    (bounded : PrefixBound host pure program depth (slots.map Slot.mode) live (.write output bytes) env world budget)
    (within : heap.Within store source budget) :
    heap.Within store source 0 ∧ (true : Bool) = true :=
  ⟨within.mono bounded.write.1, bounded.write.2⟩

end Verified.Wasi.Resource
