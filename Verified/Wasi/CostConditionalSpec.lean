import Verified.Wasi.CommandConditionalSpec
import Verified.Wasi.CommandResultStore
import Verified.Wasi.ConditionalCost
import Verified.Wasi.CostCodeSpec

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem cost_command_ite_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty} {result : ResultTy}
    {condition : Expr pureSigs context .bool}
    {yes no : Command pureSigs effectSigs context result}
    (facts : CompilerFacts source target pure (program.funs pure.funs) pool)
    (sourceHost : HostEnv Unit)
    (yesSpec : CostCommandCodeSpec source target pure program pool yes)
    (noSpec : CostCommandCodeSpec source target pure program pool no) :
    CostCommandCodeSpec source target pure program pool (.ite condition yes no) := by
  intro World host targetHost depth env slots live h base heap initial locals budget aborts
    valid below depthParam positions vars at_ safe scratch cap low room ready covered place resources
  let mid := fun i => live i || yes.uses i || no.uses i
  let picked := bif condition.denote pure.funs env then yes else no
  let branchLive := fun i => live i || picked.uses i
  let charge := pure.exprCost depth (slots.map Slot.mode) mid condition env
  let Q := CostCommandResult host pure program (.ite condition yes no) depth env slots
    (fun i => mid i || condition.uses i) live base heap initial locals aborts
  let yesCode := Relocation.program (releaseWhere context slots
      (fun i => mid i && !(live i || yes.uses i))) ++
    yes.code (pool := pool) source h slots (base + result.width) live ++
    storeCode h base result.types
  let noCode := Relocation.program (releaseWhere context slots
      (fun i => mid i && !(live i || no.uses i))) ++
    no.code (pool := pool) source h slots (base + result.width) live ++
    storeCode h base result.types
  have allEq : (fun i => live i || (Command.ite condition yes no).uses i) =
      (fun i => mid i || condition.uses i) := by
    funext i
    simp only [Command.uses, mid, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  rw [allEq] at vars safe scratch ⊢
  have conditionFragment := ready
    (condition.code (pool := pool) h slots base mid) (by simp [Command.fragments, mid])
  have cleanupFragment := ready (releaseWhere context slots (fun i => mid i && !branchLive i))
    (by
      cases chosen : condition.denote pure.funs env <;>
        simp [Command.fragments, mid, branchLive, picked, chosen])
  have conditionCovered : condition.literals ⊆ pool.values := by
    intro literal member
    apply covered
    simp only [Command.literals, List.mem_append]
    tauto
  have yesCovered : yes.Covered pool := by
    intro literal member
    apply covered
    simp only [Command.literals, List.mem_append]
    tauto
  have noCovered : no.Covered pool := by
    intro literal member
    apply covered
    simp only [Command.literals, List.mem_append]
    tauto
  have yesReady : yes.Ready source h slots (base + result.width) live pool := by
    intro fragment member
    apply ready
    simp only [Command.fragments, List.mem_append]
    tauto
  have noReady : no.Ready source h slots (base + result.width) live pool := by
    intro fragment member
    apply ready
    simp only [Command.fragments, List.mem_append]
    tauto
  have places : condition.placeArgs = true ∧ yes.placeArgs = true ∧ no.placeArgs = true := by
    simpa only [Command.placeArgs, Bool.and_eq_true, and_assoc] using place
  have pickedSpec : CostCommandCodeSpec source target pure program pool picked := by
    dsimp only [picked]
    cases condition.denote pure.funs env <;> assumption
  have pickedReady : picked.Ready source h slots (base + result.width) live pool := by
    dsimp only [picked]
    cases condition.denote pure.funs env <;> assumption
  have pickedCovered : picked.Covered pool := by
    dsimp only [picked]
    cases condition.denote pure.funs env <;> assumption
  have pickedPlace : picked.placeArgs = true := by
    dsimp only [picked]
    cases condition.denote pure.funs env with
    | false => exact places.2.2
    | true => exact places.2.1
  have pickedWidth : picked.width ≤ max yes.width no.width := by
    dsimp only [picked]
    cases condition.denote pure.funs env with
    | false => exact Nat.le_max_right _ _
    | true => exact Nat.le_max_left _ _
  have conditionBound : base + condition.width ≤ h := by
    have := Nat.le_max_left condition.width (result.width + max yes.width no.width)
    change base + max condition.width (result.width + max yes.width no.width) ≤ h at room
    omega
  have resultBound : base + result.width + max yes.width no.width ≤ h := by
    have := Nat.le_max_right condition.width (result.width + max yes.width no.width)
    change base + max condition.width (result.width + max yes.width no.width) ≤ h at room
    omega
  have midSelected : ∀ i, mid i = true → (mid i || condition.uses i) = true := by
    intro i selected
    simp only [selected, Bool.true_or]
  have branchSelected : ∀ i, branchLive i = true → mid i = true := by
    intro i selected
    cases chosen : condition.denote pure.funs env <;>
      simp [branchLive, picked, chosen, Bool.or_eq_true] at selected <;>
      simp only [mid, Bool.or_eq_true] <;> tauto
  have liveSelected : ∀ i, live i = true → branchLive i = true := by
    intro i selected
    simp only [branchLive, selected, Bool.true_or]
  have liveMid : ∀ i, live i = true → mid i = true :=
    fun i selected => branchSelected i (liveSelected i selected)
  have actionEq : (Command.ite condition yes no).denote pure.funs (program.funs pure.funs) env =
      picked.denote pure.funs (program.funs pure.funs) env := by
    cases chosen : condition.denote pure.funs env <;> simp [Command.denote, picked, chosen]
  have codeEq : (if condition.denote pure.funs env then yesCode else noCode) =
      Relocation.program (releaseWhere context slots (fun i => mid i && !branchLive i)) ++
        picked.code (pool := pool) source h slots (base + result.width) live ++
        storeCode h base result.types := by
    cases chosen : condition.denote pure.funs env <;>
      simp [yesCode, noCode, picked, branchLive, chosen]
  have liveEq : (fun i => mid i && !(mid i && !branchLive i)) = branchLive := by
    funext i
    exact live_released (mid i) (branchLive i) (branchSelected i)
  have spec := condition.code_spec source pure.funs pure.flags (pure.callBounds depth)
    (pure.callFits depth) sourceHost facts.runtime (Calls.at facts.calls depth) conditionCovered
    (fun _ => depthParam) env slots [] mid
  have noCoerce : coerceCode h .bool (condition.mode (slots.map Slot.mode)) .owned base = [] := by
    simp [coerceCode, Ty.scalar]
  have execution := wp_return (targetHost := targetHost) facts.runtime facts.layout facts.profile
    spec (by simpa only [noCoerce, List.append_nil] using conditionFragment.1)
    (by simpa only [noCoerce, List.append_nil] using conditionFragment.2)
    positions rfl vars at_ safe cap low
    (by simpa only [copyWidth, Ty.scalar, ite_true, Nat.max_zero] using conditionBound) places.1
    (rest := [.eqzI64, .iff 0 0 noCode yesCode [] []] ++ loadCode h base result.types)
    (Q := Q)
    (fun failure final sameWorld => by
      apply CostCommandResult.trapped final "unreachable"
      apply CommandResult.resource_refl ?_ sameWorld
      cases state : aborts with
      | true => rfl
      | false =>
          obtain ⟨within, bounded⟩ := resources state
          obtain ⟨withinCondition, fit⟩ := bounded.ite_resources locals within
          change condition.fits pure.funs (pure.callFits depth) env = true at fit
          change heap.Within (PureTransport.erase initial) source
            (returnCost pure.funs pure.flags (pure.callBounds depth) condition env slots [] mid
              (PureTransport.erase initial) locals) at withinCondition
          simp only [fit, withinCondition, decide_true, Bool.not_true, Bool.false_or] at failure
          exact failure)
    (fun prefixHeap conditionStore prefixLocals words first sameWorld prefixTop => by
      have wordsEq : words = [.i64 (boolWord (condition.denote pure.funs env))] := first.rep
      subst words
      have first' := first.reframe (show Frame base prefixLocals
        { prefixLocals with values := locals.values } from Frame.ofValues)
      have prefixVars := first'.holds
      have prefixApart := first'.scratch vars scratch midSelected
      have prefixSafe := (first'.pool_safe safe vars scratch midSelected facts.poolApart).1
      have upperVars := prefixVars.mono (Nat.le_add_right base result.width)
      have selectedBranch : wp target
          (if condition.denote pure.funs env then yesCode else noCode)
          (ItePost targetHost target (loadCode h base result.types) Q locals.values)
          conditionStore { prefixLocals with values := locals.values } targetHost := by
        rw [codeEq]
        rw [List.append_assoc]
        refine wp_release_context (sourceHost := sourceHost) (targetHost := targetHost)
          facts.runtime facts.layout facts.profile
          cleanupFragment.1 cleanupFragment.2 upperVars first'.step.at_
          (fun _ selected => by simp only [Bool.and_eq_true] at selected; exact selected.1) ?_
        intro middleHeap middle evolution top world
        have evolution' : Evolves env slots mid branchLive (base + result.width) prefixHeap
            (PureTransport.erase conditionStore) { prefixLocals with values := locals.values }
            middleHeap (PureTransport.erase middle) { prefixLocals with values := locals.values } := by
          simpa only [liveEq] using evolution
        have cleanup := cleanup_after evolution'
        have child := pickedSpec World host targetHost depth env slots live h (base + result.width)
          middleHeap middle { prefixLocals with values := locals.values } (budget - charge) aborts
          valid below (by rw [first.frame.params]; exact depthParam)
          (first.frame.positions.trans positions) cleanup.holds cleanup.step.at_
          (cleanup.pool_safe prefixSafe upperVars prefixApart branchSelected facts.poolApart).1
          (cleanup.scratch upperVars prefixApart branchSelected)
          (by rw [cleanup.step.cap source, first'.step.cap source]; exact cap)
          (by rw [first.frame.params]; omega) (by omega) pickedReady pickedCovered pickedPlace
          (fun noAbort => by
            obtain ⟨within, bounded⟩ := resources noAbort
            obtain ⟨conditionCharge, conditionFits⟩ := bounded.ite_condition
            change charge ≤ budget at conditionCharge
            have prefixBound := prefixTop conditionFits
            rw [pure.returnBoolCost_nil] at prefixBound
            have middleTop : middleHeap.top.toNat ≤ heap.top.toNat + charge := by
              rw [top]
              exact prefixBound
            refine ⟨within.shift middleTop (by omega) ?_, ?_⟩
            · rw [cleanup.step.cap source, first'.step.cap source]
            · rw [world, sameWorld]
              exact bounded.ite_selected)
        apply wp_append
        refine wp.conseq (fun continuation classification => ?_) child
        cases classification with
        | returned value finalHeap final finalLocals words trace spent fits resourceExecution after costTop =>
            change wp target (storeCode h base result.types)
              (ItePost targetHost target (loadCode h base result.types) Q locals.values) final
              { finalLocals with values := words.reverse ++ locals.values } targetHost
            have branchAfter := After.thenUnit upperVars prefixApart cleanup after
              branchSelected liveSelected
            refine wp_store_owned_result (initial := conditionStore) (heap := prefixHeap)
              (locals := { prefixLocals with values := locals.values })
              (base := base) (h := h) (result := result) prefixVars liveMid
              (first'.frame.positions.trans positions)
              (by rw [first'.frame.params]; exact low) (by omega) branchAfter ?_
            intro stored storedAfter held
            change wp target (loadCode h base result.types) Q final
              { stored with values := locals.values } targetHost
            have combined := After.thenEmpty vars scratch first'
              (ResultTy.fresh_scalar (result := .value .bool) rfl) storedAfter midSelected liveMid
            have resourceExecution' : Resource.ResourceExec (observedHost host) pure program depth
                (slots.map Slot.mode) live (.ite condition yes no) env initial.host trace
                (.returned value) final.host (charge + spent) (pure.exprFits depth condition env && fits) := by
              rw [← sameWorld, ← world]
              exact resourceExecution.ite_selected
            have totalTop : (pure.exprFits depth condition env && fits) = true →
                finalHeap.top.toNat ≤ heap.top.toNat + (charge + spent) := by
              intro fit
              simp only [Bool.and_eq_true] at fit
              have prefixBound := prefixTop fit.1
              rw [pure.returnBoolCost_nil] at prefixBound
              have finalBound := costTop fit.2
              rw [top] at finalBound
              dsimp only [charge]
              omega
            have loaded : wp target (loadCode h base result.types ++ []) Q final
                { stored with values := locals.values } targetHost := by
              refine wp_loadCode words after.rep.typed (combined.frame.positions.trans positions) held ?_
              rw [wp_nil]
              exact CostCommandResult.returned value finalHeap final stored words trace (charge + spent)
                (pure.exprFits depth condition env && fits) resourceExecution' combined totalTop
            simpa only [List.append_nil] using loaded
        | trapped final message classification =>
            change Q (.Trap final message)
            apply CostCommandResult.trapped final message
            cases classification with
            | terminal final trace outcome message sourceExecution terminal =>
                apply CommandResult.terminal final trace outcome message ?_ terminal
                rw [actionEq, ← sameWorld, ← world]
                exact sourceExecution
            | resource final trace residual allowed progress =>
                apply CommandResult.resource final trace residual allowed
                rw [actionEq, ← sameWorld, ← world]
                exact progress
      have branchExecution := wp_ite_bool (condition := condition.denote pure.funs env)
        (yes := yesCode) (no := noCode) (rest := loadCode h base result.types) (Q := Q) selectedBranch
      simpa only [List.cons_append, List.nil_append, List.reverse_cons, List.reverse_nil]
        using branchExecution)
  simpa only [Command.code, noCoerce, List.append_nil, List.cons_append, List.nil_append,
    List.append_assoc, mid, yesCode, noCode, Q] using execution

end Verified.Wasi
