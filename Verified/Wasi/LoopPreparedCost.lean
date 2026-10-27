import Verified.Wasi.LoopPrepared
import Verified.Wasi.LoopCostAdvance
import Verified.Wasi.LoopTestGuarded
import Verified.Wasi.LoopBodyCost
import Verified.Wasi.LoopFinishCost
import Verified.Wasi.LoopCostCode

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem wp_loopPreparedCost {World : Type} {source target : Wasm.Module} {host : Host World}
    {pureSigs : List Sig} {effectSigs : List EffectSig} {context : List Ty} {type : Ty}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {count : Expr pureSigs context .word} {initialExpr : Expr pureSigs context type}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)} {pool : Bytes.LiteralPool}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {depth : UInt64}
    {heap : Heap} {initial current : Store (Observed World)} {locals currentLocals : Locals}
    {h base budget : Nat} {aborts : Bool}
    (runtime : Runtime source) (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    (bodySpec : CostCommandCodeSpec source target pure program pool step)
    (testSpec : ∀ index state,
      CodeSpec source pure.funs pure.flags (pure.callBounds depth) (pure.callFits depth) sourceHost
        locals.params test (.cons state (.cons (t := .word) index env))
        (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots) []
        (fun i => i == 0 || shift 2 (fun j => live j || (test.uses (j + 2) || step.uses (j + 2))) i) pool)
    (hostValid : targetHost.Satisfies target (hostSpec host))
    (below : depth < depthLimit) (head : locals.params.head? = some (.i64 depth))
    (positions : locals.positions = h)
    (vars : Holds env slots liveIn base heap (PureTransport.erase initial) locals)
    (scratch : Holds.ApartFrom env slots liveIn (PureTransport.erase initial) locals ABI.scratch)
    (safe : pool.Safe env slots liveIn heap (PureTransport.erase initial) locals)
    (poolApart : ∀ region ∈ pool.regions, regionsDisjoint region ABI.scratch)
    (selected : ∀ i, (live i || (test.uses (i + 2) || step.uses (i + 2))) = true → liveIn i = true)
    (cap : (PureTransport.erase initial).memoryCap source 0 ≤ 65535)
    (low : locals.params.length ≤ base)
    (testRoom : base + 2 + type.width + max test.width (copyWidth .bool) ≤ h)
    (bodyRoom : base + 2 + type.width + step.width ≤ h)
    (testForm : Encoding.ProgramForm (test.code (pool := pool) h
      (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      (base + 2 + type.width)
      (fun i => i == 0 || shift 2 (fun j => live j || (test.uses (j + 2) || step.uses (j + 2))) i)))
    (testClosed : Relocation.programClosed source.funcs.length (test.code (pool := pool) h
      (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      (base + 2 + type.width)
      (fun i => i == 0 || shift 2 (fun j => live j || (test.uses (j + 2) || step.uses (j + 2))) i)) = true)
    (releaseForm : Encoding.ProgramForm (releaseCode type (base + 2)))
    (releaseClosed : Relocation.programClosed source.funcs.length (releaseCode type (base + 2)) = true)
    (finishForm : Encoding.ProgramForm (releaseWhere context slots
      (fun i => (test.uses (i + 2) || step.uses (i + 2)) && !live i)))
    (finishClosed : Relocation.programClosed source.funcs.length (releaseWhere context slots
      (fun i => (test.uses (i + 2) || step.uses (i + 2)) && !live i)) = true)
    (ready : step.Ready source h
      (⟨base + 2, .owned⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      (base + 2 + type.width) (shift 2 (fun j => live j || (test.uses (j + 2) || step.uses (j + 2)))) pool)
    (covered : step.Covered pool) (testPlace : test.placeArgs = true) (bodyPlace : step.placeArgs = true)
    (resources : aborts = false → heap.Within (PureTransport.erase initial) source budget ∧
      pure.loopInitCost depth (slots.map Slot.mode) live count initialExpr test step env ≤ budget ∧
      pure.loopInitFits depth count initialExpr env = true ∧
      Resource.LoopPrefixBound (observedHost host) pure program depth (slots.map Slot.mode) live test step env
        (count.denote pure.funs env).toNat 0 (initialExpr.denote pure.funs env) initial.host
        (budget - pure.loopInitCost depth (slots.map Slot.mode) live count initialExpr test step env))
    (start : LoopCostFrame host pure program depth env slots liveIn live base heap initial locals
      (count.denote pure.funs env) (initialExpr.denote pure.funs env)
      (pure.loopInitCost depth (slots.map Slot.mode) live count initialExpr test step env)
      (pure.loopInitFits depth count initialExpr env) test step 0 current currentLocals) :
    wp target (loopPreparedCode source h base slots pool test step live)
      (CostCommandResult host pure program (.loop count initialExpr test step) depth env slots
        liveIn live base heap initial locals aborts) current currentLocals targetHost := by
  let countValue := count.denote pure.funs env
  let initialCharge := pure.loopInitCost depth (slots.map Slot.mode) live count initialExpr test step env
  let initialFits := pure.loopInitFits depth count initialExpr env
  let used := fun i => test.uses (i + 2) || step.uses (i + 2)
  let all := fun i => live i || used i
  let testLive := fun i => i == 0 || shift 2 all i
  let FrameAt := fun index current currentLocals =>
    LoopCostFrame host pure program depth env slots liveIn live base heap initial locals countValue
      (initialExpr.denote pure.funs env) initialCharge initialFits test step index current currentLocals
  let ReadyAt := fun index decision current currentLocals =>
    LoopCostReady host pure program depth env slots liveIn live base heap initial locals countValue
      (initialExpr.denote pure.funs env) initialCharge initialFits test step index decision current currentLocals
  let invariant := fun index current currentLocals => Nonempty (FrameAt index current currentLocals)
  let tested := fun index decision current currentLocals => Nonempty (ReadyAt index decision current currentLocals)
  let Q := CostCommandResult host pure program (.loop count initialExpr test step) depth env slots
    liveIn live base heap initial locals aborts
  have testSelected : ∀ i, (testLive (i + 2) || test.uses (i + 2)) = true → all i = true := by
    intro i chosen
    simp only [testLive, show (i + 2 == 0) = false by simp, Bool.false_or, shift_add,
      Bool.or_eq_true] at chosen
    rcases chosen with chosen | chosen
    · exact chosen
    · simp only [all, used, chosen, Bool.true_or, Bool.or_true]
  have bodySelected : ∀ i, step.uses (i + 2) = true → all i = true := by
    intro i chosen
    simp only [all, used, chosen, Bool.or_true]
  have main : wp target
      (loopControlCode base (base + 1)
        (Relocation.program (test.code (pool := pool) h
          (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
          (base + 2 + type.width) testLive))
        ((if step.uses 0 = false then Relocation.program (releaseCode type (base + 2)) else []) ++
          step.code (pool := pool) source h
            (⟨base + 2, .owned⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
            (base + 2 + type.width) (shift 2 all) ++ storeCode h (base + 2) type.types) ++
        (Relocation.program (releaseWhere context slots (fun i => used i && !live i)) ++
          loadCode h (base + 2) type.types)) Q current currentLocals targetHost := by
    refine wp_loopControl (count := countValue) (values := locals.values)
      invariant tested ⟨start⟩ ?_ ?_ ?_ ?_ ?_
    · intro index current currentLocals inv
      obtain ⟨frame⟩ := inv
      exact ⟨frame.safety.progress.bound, frame.safety.countLocal, frame.safety.indexLocal, frame.safety.stack⟩
    · intro index current currentLocals inv bound
      obtain ⟨frame⟩ := inv
      obtain ⟨currentSafe, _⟩ := frame.safety.after.pool_safe safe vars scratch selected poolApart
      have currentScratch := frame.safety.after.scratch vars scratch selected
      have testRun := wp_loopTestGuarded (targetHost := targetHost) runtime layout profile
        (testSpec index frame.safety.state) testForm testClosed
        (frame.safety.after.frame.positions.trans positions) frame.safety.after.frame.params
        frame.safety.after currentScratch currentSafe.static frame.safety.held frame.safety.indexLocal testSelected
        (by rw [frame.safety.after.step.cap source]; exact cap)
        (by rw [frame.safety.after.frame.params]; omega) testRoom testPlace
        (rest := []) (Q := LoopTestPost Q tested locals.values index)
        (fun failure final same => by
          have allowed : aborts = true := by
            cases permitted : aborts with
            | true => rfl
            | false =>
                obtain ⟨within, initialBound, initialValid, bounded⟩ := resources permitted
                obtain ⟨withinTest, testValid⟩ := frame.test_resources bound within initialBound initialValid bounded
                rw [pure.loopTestFits_code] at testValid
                have withinReturn : frame.safety.currentHeap.Within (PureTransport.erase current) source
                    (returnCost pure.funs pure.flags (pure.callBounds depth) test
                      (.cons frame.safety.state (.cons index env))
                      (⟨base + 2, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots) [] testLive
                      (PureTransport.erase current) currentLocals) := by
                  rw [pure.loopTestReturnCost]
                  exact withinTest
                dsimp only [testLive, all, used] at withinReturn
                simp only [testValid, withinReturn, decide_true, Bool.not_true, Bool.false_or] at failure
                exact nomatch failure
          exact CostCommandResult.trapped final "unreachable"
            (CommandResult.resource final frame.safety.trace
              (loopResidual countValue index
                (fun index state => test.denote pure.funs (.cons state (.cons index env)))
                (fun index state => step.denote pure.funs (program.funs pure.funs) (.cons state (.cons index env)))
                Action.pure frame.safety.state) allowed
              (by rw [same]; exact frame.safety.progress.progress)))
        (fun finalHeap final finalLocals after localFrame sameWorld growth => by
          rw [wp_nil]
          let decision := test.denote pure.funs (.cons frame.safety.state (.cons index env))
          refine ⟨decision, ?_, ?_⟩
          · rw [frame.safety.stack]
            cases truth : decision <;> simp only [decision] at truth <;> simp [truth, boolWord]
          · refine ⟨frame.tested bound ?_ (after.reframe Frame.ofValues)
              (localFrame.trans Frame.ofValues) sameWorld frame.safety.stack.symm ?_⟩
            · simp only [Resource.loopEnv, UInt64.ofNat_toNat]
              rfl
            · intro testValid
              rw [pure.loopTestFits_code] at testValid
              have bound := growth testValid
              simpa only [pure.loopTestCost_compiler depth slots live test step env index.toNat
                frame.safety.state (base + 2) (base + 1), Resource.loopEnv, UInt64.ofNat_toNat] using bound)
      simpa only [List.append_nil] using testRun
    · intro index current currentLocals decision bound
      obtain ⟨frame⟩ := decision
      obtain ⟨currentSafe, fresh⟩ := frame.safety.after.pool_safe safe vars scratch selected poolApart
      have currentScratch := frame.safety.after.scratch vars scratch selected
      let bodyBudget := budget - initialCharge - frame.spent -
        pure.loopTestCost depth (slots.map Slot.mode) live test step env index.toNat frame.safety.state
      refine wp_loopBodyCost (sourceHost := sourceHost) (budget := bodyBudget) (aborts := aborts)
        runtime layout profile bodySpec hostValid below
        (by rw [frame.safety.after.frame.params]; exact head)
        (frame.safety.after.frame.positions.trans positions) frame.safety.after currentScratch currentSafe.static fresh
        poolApart frame.safety.held frame.safety.indexLocal bodySelected
        (by rw [frame.safety.after.step.cap source]; exact cap)
        (by rw [frame.safety.after.frame.params]; exact low) bodyRoom releaseForm releaseClosed ready covered bodyPlace
        (fun permitted => by
          obtain ⟨within, initialBound, initialValid, bounded⟩ := resources permitted
          obtain ⟨withinBody, bodyBound⟩ := frame.body_resources within initialBound initialValid bounded
          refine ⟨withinBody, ?_⟩
          simpa only [Resource.loopSlots_modes, Resource.loopLive_code, Resource.loopEnv, UInt64.ofNat_toNat]
            using bodyBound)
        (Q := LoopStepPost Q invariant locals.values (base + 1) index) ?_ ?_ ?_
      · intro finalHeap final stored words value trace spent fits execution after localFrame held sameStack growth
        have sourceExecution : Resource.ResourceExec (observedHost host) pure program depth
            (Resource.loopModes .owned (slots.map Slot.mode)) (shift 2 (Resource.loopLive test step live))
            step (Resource.loopEnv env index.toNat frame.safety.state)
            current.host trace (.returned value) final.host spent fits := by
          simpa only [Resource.loopSlots_modes, Resource.loopLive_code, Resource.loopEnv, UInt64.ofNat_toNat]
            using execution
        have indexLocal := (localFrame.below (base + 1) (by omega)).1.trans frame.safety.indexLocal
        have lower : stored.params.length ≤ base + 1 := by rw [after.frame.params]; omega
        have high : base + 1 < stored.positions := by rw [after.frame.positions, positions]; omega
        have room : base + 2 + type.width ≤ stored.positions := by rw [after.frame.positions, positions]; omega
        exact ⟨sameStack.trans frame.safety.stack, indexLocal, lower, Locals.lt_total high,
          ⟨frame.advance sourceExecution after localFrame held sameStack lower high room growth⟩⟩
      · intro final trace outcome message execution terminal
        apply CostCommandResult.trapped
        cases outcome with
        | returned value => exact terminal.elim
        | exited code =>
            exact CommandResult.terminal final (frame.safety.trace ++ trace) (.exited code) message
              (frame.safety.progress.exited bound
                (by simpa only [Resource.loopEnv, UInt64.ofNat_toNat] using frame.choice) execution) terminal
        | trapped cause =>
            exact CommandResult.terminal final (frame.safety.trace ++ trace) (.trapped cause) message
              (frame.safety.progress.trapped bound
                (by simpa only [Resource.loopEnv, UInt64.ofNat_toNat] using frame.choice) execution) terminal
      · intro final trace residual allowed progress
        exact CostCommandResult.trapped final "unreachable"
          (CommandResult.resource final (frame.safety.trace ++ trace)
            (Action.bind residual (loopResidual countValue (index + 1)
              (fun index state => test.denote pure.funs (.cons state (.cons index env)))
              (fun index state => step.denote pure.funs (program.funs pure.funs) (.cons state (.cons index env)))
              Action.pure)) allowed
            (frame.safety.progress.resource bound
              (by simpa only [Resource.loopEnv, UInt64.ofNat_toNat] using frame.choice) progress))
    · intro current currentLocals inv
      obtain ⟨frame⟩ := inv
      refine wp_loopFinishCost (sourceHost := sourceHost) runtime layout profile finishForm finishClosed vars scratch
        frame.safety.after selected (frame.safety.after.frame.positions.trans positions) frame.safety.held frame.safety.stack
        (Resource.ResourceExec.loop frame.complete_done) ?_
      intro valid
      simp only [Bool.and_eq_true] at valid
      simpa only [Nat.add_assoc, initialCharge] using frame.top valid.1 valid.2
    · intro index current currentLocals stopped
      obtain ⟨frame⟩ := stopped
      refine wp_loopFinishCost (sourceHost := sourceHost) runtime layout profile finishForm finishClosed vars scratch
        frame.safety.after selected (frame.safety.after.frame.positions.trans positions) frame.safety.held frame.safety.stack
        (Resource.ResourceExec.loop frame.complete_stop) ?_
      intro valid
      simp only [Bool.and_eq_true] at valid
      have bound := frame.top valid.1 valid.2.1 valid.2.2
      omega
  have completed : wp target (loopPreparedCode source h base slots pool test step live)
      Q current currentLocals targetHost := main
  exact completed

end Verified.Wasi
