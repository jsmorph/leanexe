import Verified.Wasi.LoopInvariant
import Verified.Wasi.LoopTest
import Verified.Wasi.LoopBody
import Verified.Wasi.LoopFinish

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

def loopPreparedCode (source : Wasm.Module) (h base : Nat) (slots : List Slot)
    (pool : Bytes.LiteralPool) (test : Expr pureSigs (type :: .word :: context) .bool)
    (step : Command pureSigs effectSigs (type :: .word :: context) (.value type))
    (live : Nat → Bool) : Program :=
  let used := fun i => test.uses (i + 2) || step.uses (i + 2)
  let all := fun i => live i || used i
  let state := base + 2
  let scratch := state + type.width
  loopControlCode base (base + 1)
    (Relocation.program (test.code (pool := pool) h
      (⟨state, .borrowed⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots)
      scratch (fun i => i == 0 || shift 2 all i)))
    ((if step.uses 0 = false then Relocation.program (releaseCode type state) else []) ++
      step.code (pool := pool) source h
        (⟨state, .owned⟩ :: ⟨base + 1, .borrowed⟩ :: loopCaptured slots) scratch (shift 2 all) ++
      storeCode h state type.types) ++
    Relocation.program (releaseWhere context slots (fun i => used i && !live i)) ++
    loadCode h state type.types

theorem wp_loopPrepared {World : Type} {source target : Wasm.Module} {host : Host World}
    {pureSigs : List Sig} {effectSigs : List EffectSig} {context : List Ty} {type : Ty}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {test : Expr pureSigs (type :: .word :: context) .bool}
    {step : Command pureSigs effectSigs (type :: .word :: context) (.value type)}
    {sourceHost : HostEnv Unit} {targetHost : HostEnv (Observed World)} {pool : Bytes.LiteralPool}
    {env : Env context} {slots : List Slot} {liveIn live : Nat → Bool} {count depth : UInt64}
    {initialState : type.denote} {heap : Heap} {initial current : Store (Observed World)}
    {locals currentLocals : Locals} {h base : Nat}
    (runtime : Runtime source) (layout : Relocation.Layout source target) (profile : Relocation.Profile source)
    (bodySpec : CommandCodeSpec source target pure effects pool step)
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
    (start : LoopFrame host env slots liveIn
      (fun j => live j || (test.uses (j + 2) || step.uses (j + 2))) base heap initial locals
      count initialState
      (fun index state => test.denote pure.funs (.cons state (.cons index env)))
      (fun index state => step.denote pure.funs effects (.cons state (.cons index env)))
      0 current currentLocals) :
    wp target (loopPreparedCode source h base slots pool test step live)
      (CommandResult host env slots liveIn live base (.value type)
        (.loop count initialState
          (fun index state => test.denote pure.funs (.cons state (.cons index env)))
          (fun index state => step.denote pure.funs effects (.cons state (.cons index env))) Action.pure)
        heap initial locals true) current currentLocals targetHost := by
  let used := fun i => test.uses (i + 2) || step.uses (i + 2)
  let all := fun i => live i || used i
  let testLive := fun i => i == 0 || shift 2 all i
  let testFn := fun index state => test.denote pure.funs (.cons state (.cons index env))
  let stepFn := fun index state => step.denote pure.funs effects (.cons state (.cons index env))
  let action : Action type.denote := .loop count initialState testFn stepFn Action.pure
  let FrameAt := fun index current currentLocals =>
    LoopFrame host env slots liveIn all base heap initial locals count initialState testFn stepFn
      index current currentLocals
  let invariant := fun index current currentLocals => Nonempty (FrameAt index current currentLocals)
  let tested := fun index decision current currentLocals =>
    ∃ frame : FrameAt index current currentLocals, index < count ∧ testFn index frame.state = decision
  let Q := CommandResult host env slots liveIn live base (.value type) action heap initial locals true
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
    refine wp_loopControl (count := count) (values := locals.values)
      invariant tested ⟨start⟩ ?_ ?_ ?_ ?_ ?_
    · intro index current currentLocals inv
      obtain ⟨frame⟩ := inv
      exact ⟨frame.progress.bound, frame.countLocal, frame.indexLocal, frame.stack⟩
    · intro index current currentLocals inv bound
      obtain ⟨frame⟩ := inv
      obtain ⟨currentSafe, _⟩ := frame.after.pool_safe safe vars scratch selected poolApart
      have currentScratch := frame.after.scratch vars scratch selected
      have testRun := wp_loopTest (targetHost := targetHost) runtime layout profile
        (testSpec index frame.state) testForm testClosed
        (frame.after.frame.positions.trans positions) frame.after.frame.params frame.after currentScratch
        currentSafe.static frame.held frame.indexLocal testSelected
        (by rw [frame.after.step.cap source]; exact cap)
        (by rw [frame.after.frame.params]; omega) testRoom testPlace
        (rest := []) (Q := LoopTestPost Q tested locals.values index)
        (fun final same => by
          exact CommandResult.resource final frame.trace
            (loopResidual count index testFn stepFn Action.pure frame.state) rfl
            (by rw [same]; exact frame.progress.progress))
        (fun finalHeap final finalLocals after localFrame sameWorld _ => by
          rw [wp_nil]
          refine ⟨testFn index frame.state, ?_, ?_⟩
          · rw [frame.stack]
            cases truth : testFn index frame.state <;>
              simp only [testFn] at truth <;> simp [truth, boolWord]
          · refine ⟨frame.retest (after.reframe Frame.ofValues)
              (localFrame.trans Frame.ofValues) sameWorld frame.stack.symm, bound, rfl⟩)
      simpa only [List.append_nil] using testRun
    · intro index current currentLocals decision bound
      obtain ⟨frame, _, runs⟩ := decision
      obtain ⟨currentSafe, fresh⟩ := frame.after.pool_safe safe vars scratch selected poolApart
      have currentScratch := frame.after.scratch vars scratch selected
      refine wp_loopBody (sourceHost := sourceHost) runtime layout profile bodySpec hostValid below
        (by rw [frame.after.frame.params]; exact head)
        (frame.after.frame.positions.trans positions) frame.after currentScratch currentSafe.static fresh
        poolApart frame.held frame.indexLocal bodySelected
        (by rw [frame.after.step.cap source]; exact cap)
        (by rw [frame.after.frame.params]; exact low) bodyRoom releaseForm releaseClosed ready covered bodyPlace
        (Q := LoopStepPost Q invariant locals.values (base + 1) index) ?_ ?_ ?_
      · intro finalHeap final stored words value trace execution after localFrame held sameStack
        have indexLocal := (localFrame.below (base + 1) (by omega)).1.trans frame.indexLocal
        have lower : stored.params.length ≤ base + 1 := by rw [after.frame.params]; omega
        have high : base + 1 < stored.positions := by rw [after.frame.positions, positions]; omega
        have room : base + 2 + type.width ≤ stored.positions := by
          rw [after.frame.positions, positions]
          omega
        exact ⟨sameStack.trans frame.stack, indexLocal, lower, Locals.lt_total high,
          ⟨frame.advance bound runs execution after localFrame held sameStack lower high room⟩⟩
      · intro final trace outcome message execution terminal
        cases outcome with
        | returned value => exact terminal.elim
        | exited code =>
            exact CommandResult.terminal final (frame.trace ++ trace) (.exited code) message
              (frame.progress.exited bound runs execution) terminal
        | trapped cause =>
            exact CommandResult.terminal final (frame.trace ++ trace) (.trapped cause) message
              (frame.progress.trapped bound runs execution) terminal
      · intro final trace residual progress
        exact CommandResult.resource final (frame.trace ++ trace)
          (Action.bind residual (loopResidual count (index + 1) testFn stepFn Action.pure)) rfl
          (frame.progress.resource bound runs progress)
    · intro current currentLocals inv
      obtain ⟨frame⟩ := inv
      exact wp_loopFinish (sourceHost := sourceHost) runtime layout profile
        finishForm finishClosed vars scratch frame.after selected
        (frame.after.frame.positions.trans positions) frame.held frame.stack
        (by simpa only [List.append_nil] using frame.progress.done (Exec.pure current.host frame.state))
    · intro index current currentLocals stopped
      obtain ⟨frame, bound, stops⟩ := stopped
      exact wp_loopFinish (sourceHost := sourceHost) runtime layout profile
        finishForm finishClosed vars scratch frame.after selected
        (frame.after.frame.positions.trans positions) frame.held frame.stack
        (by simpa only [List.append_nil] using
          frame.progress.stopped bound stops (Exec.pure current.host frame.state))
  have completed : wp target (loopPreparedCode source h base slots pool test step live)
      Q current currentLocals targetHost := main
  exact completed

end Verified.Wasi
