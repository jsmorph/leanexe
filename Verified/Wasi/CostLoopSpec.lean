import Verified.Wasi.LoopPreparedCost
import Verified.Wasi.LoopPrepareGuarded
import Verified.Wasi.CompilerFacts
import Verified.AlignedCorrect

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem cost_command_loop_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty} {type : Ty}
    {count : Expr pureSigs context .word} {initial : Expr pureSigs context type}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
    (facts : CompilerFacts source target pure (program.funs pure.funs) pool) (sourceHost : HostEnv Unit)
    (bodySpec : CostCommandCodeSpec source target pure program pool step) :
    CostCommandCodeSpec source target pure program pool (.loop count initial test step) := by
  intro World host targetHost depth env slots live h base heap store locals budget aborts
    valid below depthParam positions vars at_ safe scratch cap low room ready covered place resources
  let used := fun i => test.uses (i + 2) || step.uses (i + 2)
  let all := fun i => live i || used i
  let input := fun i => (all i || initial.uses i) || count.uses i
  have inputEq : (fun i => live i || (Command.loop count initial test step).uses i) = input := by
    funext i
    simp only [input, all, used, Command.uses, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  rw [inputEq] at vars safe scratch ⊢
  have selected : ∀ i, all i = true → input i = true := by
    intro i chosen
    simp only [input, chosen, Bool.true_or]
  obtain ⟨countCovered, initialCovered, testCovered, stepCovered⟩ :=
    (Command.covered_loop count initial test step pool).mp covered
  have places : count.placeArgs = true ∧ initial.placeArgs = true ∧
      test.placeArgs = true ∧ step.placeArgs = true := by
    simpa only [Command.placeArgs, Bool.and_eq_true, and_assoc] using place
  have countFragment := ready (count.code (pool := pool) h slots base
      (fun i => all i || initial.uses i))
    (by simp [Command.fragments, all, used, Expr.usesFast_eq])
  have initialFragment := ready (initial.code (pool := pool) h slots (base + 1) all ++
      coerceCode h type (initial.mode (slots.map Slot.mode)) .owned (base + 1))
    (by simp [Command.fragments, all, used])
  have testFragment := ready (test.code (pool := pool) h
      (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      (base + 2 + type.width) (fun i => i == 0 || shift 2 all i))
    (by simp [Command.fragments, all, used, loopCaptured])
  have releaseFragment := ready (releaseCode type (base + 2))
    (by simp [Command.fragments])
  have finishFragment := ready (releaseWhere context slots (fun i => used i && !live i))
    (by simp [Command.fragments, used])
  have stepReady : step.Ready source h
      (⟨base + 2, .owned⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      (base + 2 + type.width) (shift 2 all) pool := by
    intro fragment member
    apply ready
    simp only [Command.fragments, List.mem_append]
    exact Or.inr member
  have countWidth : base + count.width ≤ h := by
    have outer := Nat.le_max_left count.width
      (max (1 + max initial.width (copyWidth type)) (2 + type.width + max test.width step.width))
    change base + max count.width
      (max (1 + max initial.width (copyWidth type)) (2 + type.width + max test.width step.width)) ≤ h at room
    omega
  have initialWidth : base + 1 + max initial.width (copyWidth type) ≤ h := by
    have outer := Nat.le_max_right count.width
      (max (1 + max initial.width (copyWidth type)) (2 + type.width + max test.width step.width))
    have middle := Nat.le_max_left (1 + max initial.width (copyWidth type))
      (2 + type.width + max test.width step.width)
    change base + max count.width
      (max (1 + max initial.width (copyWidth type)) (2 + type.width + max test.width step.width)) ≤ h at room
    omega
  have callbacksWidth : base + 2 + type.width + max test.width step.width ≤ h := by
    have outer := Nat.le_max_right count.width
      (max (1 + max initial.width (copyWidth type)) (2 + type.width + max test.width step.width))
    have middle := Nat.le_max_right (1 + max initial.width (copyWidth type))
      (2 + type.width + max test.width step.width)
    change base + max count.width
      (max (1 + max initial.width (copyWidth type)) (2 + type.width + max test.width step.width)) ≤ h at room
    omega
  have testWidth : base + 2 + type.width + max test.width (copyWidth .bool) ≤ h := by
    have bound := Nat.le_max_left test.width step.width
    simpa only [copyWidth, Ty.scalar, ite_true, Nat.max_zero] using
      (show base + 2 + type.width + test.width ≤ h from by omega)
  have bodyWidth : base + 2 + type.width + step.width ≤ h := by
    have bound := Nat.le_max_right test.width step.width
    omega
  have countSpec := count.code_spec source pure.funs pure.flags (pure.callBounds depth)
    (pure.callFits depth) sourceHost facts.runtime (Calls.at facts.calls depth) countCovered
    (fun _ => depthParam) env slots [] (fun i => all i || initial.uses i)
  have initialSpec := initial.code_spec source pure.funs pure.flags (pure.callBounds depth)
    (pure.callFits depth) sourceHost facts.runtime (Calls.at facts.calls depth) initialCovered
    (fun _ => depthParam) env slots [] all
  have testSpec := fun index state => test.code_spec source pure.funs pure.flags (pure.callBounds depth)
    (pure.callFits depth) sourceHost facts.runtime (Calls.at facts.calls depth) testCovered
    (fun _ => depthParam) (.cons state (.cons index env))
    (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots) []
    (fun i => i == 0 || shift 2 all i)
  let Q := CostCommandResult host pure program (.loop count initial test step) depth env slots
    input live base heap store locals aborts
  have execution := wp_loopPrepareGuarded (targetHost := targetHost)
    facts.runtime facts.layout facts.profile countSpec initialSpec
    countFragment.1 countFragment.2 initialFragment.1 initialFragment.2
    positions rfl vars at_ safe scratch facts.poolApart cap low
    (by simpa only [copyWidth, Ty.scalar, ite_true, Nat.max_zero] using countWidth)
    initialWidth (by omega) places.1 places.2.1
    (rest := loopPreparedCode source h base slots pool test step live) (Q := Q)
    (fun failure final same => by
      have allowed : aborts = true := by
        cases permitted : aborts with
        | true => rfl
        | false =>
            obtain ⟨within, bounded⟩ := resources permitted
            obtain ⟨chargeBound, valid⟩ := bounded.loop_init
            have withinInit := within.mono chargeBound
            have failureSource : (!(pure.loopInitFits depth count initial env) || !decide
                (heap.Within (PureTransport.erase store) source
                  (pure.loopInitCost depth (slots.map Slot.mode) live count initial test step env))) = true := by
              simpa only [Resource.PureContext.loopInitFits, Resource.PureContext.exprFits,
                all, used, pure.loopPrepareCost] using failure
            simp only [valid, withinInit, decide_true, Bool.not_true, Bool.false_or] at failureSource
            exact nomatch failureSource
      exact CostCommandResult.trapped final "unreachable" (CommandResult.resource_refl allowed same))
    (fun finalHeap final finalLocals words after sameWorld countLocal indexLocal held stack top => by
      let safety : LoopFrame host env slots input all base heap store locals
          (count.denote pure.funs env) (initial.denote pure.funs env)
          (fun index state => test.denote pure.funs (.cons state (.cons index env)))
          (fun index state => step.denote pure.funs (program.funs pure.funs) (.cons state (.cons index env)))
          0 final finalLocals :=
        ⟨initial.denote pure.funs env, finalHeap, words, [],
          by
            rw [sameWorld]
            exact LoopProgress.initial _ _ _ _ _ store.host,
          after, countLocal, indexLocal, held, stack⟩
      have start : LoopCostFrame host pure program depth env slots input live base heap store locals
          (count.denote pure.funs env) (initial.denote pure.funs env)
          (pure.loopInitCost depth (slots.map Slot.mode) live count initial test step env)
          (pure.loopInitFits depth count initial env) test step 0 final finalLocals :=
        ⟨safety, 0, true,
          by
            dsimp only [safety]
            rw [sameWorld, UInt64.toNat_zero, Nat.sub_zero]
            exact .refl,
          by
            intro initialValid _
            have valid : count.fits pure.funs (pure.callFits depth) env = true ∧
                initial.fits pure.funs (pure.callFits depth) env = true := by
              simpa only [Resource.PureContext.loopInitFits, Resource.PureContext.exprFits,
                Bool.and_eq_true] using initialValid
            have bound := top valid.1 valid.2
            dsimp only [all, used] at bound
            rw [pure.loopPrepareCost] at bound
            dsimp only [safety]
            simpa only [Nat.add_zero] using bound⟩
      exact wp_loopPreparedCost facts.runtime facts.layout facts.profile bodySpec testSpec valid below depthParam
        positions vars scratch safe facts.poolApart selected cap low testWidth bodyWidth
        testFragment.1 testFragment.2 releaseFragment.1 releaseFragment.2
        finishFragment.1 finishFragment.2 stepReady stepCovered places.2.2.1 places.2.2.2
        (fun permitted => by
          obtain ⟨within, bounded⟩ := resources permitted
          obtain ⟨initialBound, initialValid⟩ := bounded.loop_init
          exact ⟨within, initialBound, initialValid, bounded.loop_body⟩) start)
  have codeEq : (Command.loop count initial test step).code (pool := pool) source h slots base live =
      loopPrepareCode h base slots pool count initial all ++
        loopPreparedCode source h base slots pool test step live := by
    simp only [Command.code, loopPrepareCode, loopPreparedCode, loopControlCode, Expr.usesFast_eq,
      List.append_assoc, List.cons_append, List.nil_append, loopCaptured, all, used]
  rw [codeEq]
  exact execution

end Verified.Wasi
