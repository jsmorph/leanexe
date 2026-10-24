import Verified.Wasi.BindContext
import Verified.Wasi.CompilerFacts
import Verified.Wasi.CostCodeSpec
import Verified.Wasi.LoopRelease
import Verified.Wasi.Cleanup
import Verified.Wasi.ResourceBudget

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem cost_command_bind_value_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty} {type : Ty} {result : ResultTy}
    (facts : CompilerFacts source target pure (program.funs pure.funs) pool) (sourceHost : HostEnv Unit)
    (first : Command pureSigs effectSigs context (.value type))
    (next : Command pureSigs effectSigs (type :: context) result)
    (firstSpec : CostCommandCodeSpec source target pure program pool first)
    (nextSpec : CostCommandCodeSpec source target pure program pool next) :
    CostCommandCodeSpec source target pure program pool (.bind first next) := by
  intro World host targetHost depth env slots live h base heap initial locals budget aborts
    valid below depthParam positions vars at_ safe scratch cap low room ready covered place resource
  let mid := fun i => live i || next.uses (i + 1)
  let all := fun i => mid i || first.uses i
  let bodyIn := fun i => shift 1 live i || next.uses i
  let releaseIn := fun i => i == 0 || bodyIn i
  have allEq : (fun i => live i || (Command.bind first next).uses i) = all := by
    funext i
    change (live i || (first.uses i || next.uses (i + 1))) =
      ((live i || next.uses (i + 1)) || first.uses i)
    simp only [Bool.or_assoc, Bool.or_comm]
  rw [allEq] at vars safe scratch ⊢
  have midSelected : ∀ i, mid i = true → all i = true := by
    intro i selected
    simp only [all, selected, Bool.true_or]
  have selected : ∀ i, live i = true → mid i = true := by
    intro i retained
    simp only [mid, retained, Bool.true_or]
  have tail : (fun i => releaseIn (i + 1)) = mid := by
    funext i
    simp [releaseIn, bodyIn, mid, shift_add]
  have tailSelected : ∀ i, releaseIn (i + 1) = true → mid i = true := by
    intro i used
    simpa only [congrFun tail i] using used
  have bodySelected : ∀ i, bodyIn i = true → releaseIn i = true := by
    intro i used
    simp only [releaseIn, used, Bool.or_true]
  have outputSelected : ∀ i, shift 1 live i = true → bodyIn i = true := by
    intro i retained
    simp only [bodyIn, retained, Bool.true_or]
  change base + (type.width + max first.width next.width) ≤ h at room
  have firstRoom : base + type.width + first.width ≤ h := by
    have := Nat.le_max_left first.width next.width
    omega
  have nextRoom : base + type.width + next.width ≤ h := by
    have := Nat.le_max_right first.width next.width
    omega
  have resultRoom : base + type.width ≤ h := by omega
  have firstReady : first.Ready source h slots (base + type.width) mid pool := by
    intro fragment member
    exact ready fragment (List.mem_append_left _ (List.mem_append_left _ member))
  have releaseReady := ready (releaseCode type base)
    (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)))
  have nextReady : next.Ready source h (⟨base, .owned⟩ :: slots)
      (base + type.width) (shift 1 live) pool := by
    intro fragment member
    exact ready fragment (List.mem_append_right _ member)
  obtain ⟨firstCovered, nextCovered⟩ := (Command.covered_bind first next pool).mp covered
  have placement : first.placeArgs = true ∧ next.placeArgs = true := by
    change (first.placeArgs && next.placeArgs) = true at place
    simpa only [Bool.and_eq_true] using place
  have firstUpper := firstSpec World host targetHost depth env slots mid h (base + type.width)
    heap initial locals budget aborts valid below depthParam positions
    (vars.mono (Nat.le_add_right _ _)) at_ safe scratch cap (by omega) firstRoom firstReady
    firstCovered placement.1 (fun noAbort => by
      obtain ⟨within, bounded⟩ := resource noAbort
      exact ⟨within, bounded.bind_first⟩)
  have firstRun := wp.conseq (fun _ classification =>
    classification.lower vars midSelected (Nat.le_add_right _ _)) firstUpper
  let Q := CostCommandResult host pure program (.bind first next) depth env slots all live base
    heap initial locals aborts
  let restCode := (if next.uses 0 = false then Relocation.program (releaseCode type base) else []) ++
    next.code (pool := pool) source h (⟨base, .owned⟩ :: slots) (base + type.width) (shift 1 live)
  simp only [Command.code, List.append_assoc]
  change wp target (first.code (pool := pool) source h slots (base + type.width) mid ++
    (storeCode h base type.types ++ restCode)) Q initial locals targetHost
  apply wp_append
  refine wp.conseq (fun continuation firstResult => ?_) firstRun
  cases firstResult with
  | returned value middleHeap middle middleLocals words firstTrace firstSpent firstFits
      firstExecution firstAfter firstTop =>
    change wp target (storeCode h base type.types ++ restCode) Q middle
      { middleLocals with values := words.reverse ++ locals.values } targetHost
    have rep : type.Rep .owned middleHeap (PureTransport.erase middle) words value := firstAfter.rep
    refine wp_storeCode words h base type.types middleLocals locals.values rep.typed
      (firstAfter.frame.positions.trans positions)
      (by rw [firstAfter.frame.params]; exact low)
      (by rw [Ty.types_length, firstAfter.frame.positions, positions]; exact resultRoom) ?_
    intro boundLocals frame held _
    have frame' : Frame base middleLocals { boundLocals with values := locals.values } :=
      ⟨frame.params, frame.length, frame.below, frame.below32⟩
    have boundVars := bind_context_holds firstAfter frame' held tailSelected
    have boundScratch := bind_context_scratch firstAfter vars scratch frame' held midSelected tailSelected
    have boundSafe := bind_context_safe firstAfter vars scratch safe facts.poolApart
      frame' held midSelected tailSelected
    refine wp_loopRelease (sourceHost := sourceHost) (targetHost := targetHost)
      (used := next.uses 0) (rest := next.code (pool := pool) source h
        (⟨base, .owned⟩ :: slots) (base + type.width) (shift 1 live))
      facts.runtime facts.layout facts.profile releaseReady.1 releaseReady.2 boundVars firstAfter.step.at_
      (by simp only [releaseIn, beq_self_eq_true, Bool.true_or])
      (by simp [bodyIn, shift]) bodySelected ?_
    intro cleanupHeap cleanupStore cleanup cleanupTop sameWorld
    have cleanupAfter := cleanup_after cleanup
    have bodyRun := nextSpec World host targetHost depth (.cons value env)
      (⟨base, .owned⟩ :: slots) (shift 1 live) h (base + type.width) cleanupHeap cleanupStore
      { boundLocals with values := locals.values } (budget - firstSpent) aborts
      valid below (by rw [frame'.params, firstAfter.frame.params]; exact depthParam)
      (frame'.positions.trans (firstAfter.frame.positions.trans positions)) cleanup.holds cleanup.step.at_
      (cleanupAfter.pool_safe boundSafe boundVars boundScratch bodySelected facts.poolApart).1
      (cleanupAfter.scratch boundVars boundScratch bodySelected)
      (by rw [cleanup.step.cap source, firstAfter.step.cap source]; exact cap)
      (by rw [frame'.params, firstAfter.frame.params]; omega) nextRoom nextReady nextCovered placement.2
      (fun noAbort => by
        obtain ⟨within, bounded⟩ := resource noAbort
        obtain ⟨spentBound, fitFirst⟩ := bounded.bind_first.returned firstExecution
        have cleanupGrowth : cleanupHeap.top.toNat ≤ heap.top.toNat + firstSpent := by
          rw [cleanupTop]
          exact firstTop fitFirst
        refine ⟨within.shift cleanupGrowth (by omega) ?_, ?_⟩
        · rw [cleanup.step.cap source, firstAfter.step.cap source]
        · rw [sameWorld]
          simpa only [Resource.bindModes, ResultTy.bindCount, ResultTy.bindEnv, ResultTy.extend,
            List.map_cons] using bounded.bind_next firstExecution)
    refine wp.conseq (fun continuation nextResult => ?_) bodyRun
    cases nextResult with
    | returned finalValue finalHeap final finalLocals resultWords trace nextSpent nextFits
        nextExecution nextAfter nextTop =>
      have bodyAfter := After.thenUnit boundVars boundScratch cleanupAfter nextAfter bodySelected outputSelected
      have combined := After.bind_value vars scratch firstAfter frame' held bodyAfter
        tailSelected midSelected selected
      have execution : Resource.ResourceExec (observedHost host) pure program depth
          (slots.map Slot.mode) live (.bind first next) env initial.host (firstTrace ++ trace)
          (.returned finalValue) final.host (firstSpent + nextSpent) (firstFits && nextFits) := by
        apply Resource.ResourceExec.bind_return firstExecution
        rw [← sameWorld]
        simpa only [Resource.bindModes, ResultTy.bindCount, ResultTy.bindEnv, ResultTy.extend,
          List.map_cons] using nextExecution
      refine CostCommandResult.returned (result := result) finalValue finalHeap final finalLocals resultWords
        (firstTrace ++ trace) (firstSpent + nextSpent) (firstFits && nextFits) execution combined ?_
      intro fits
      simp only [Bool.and_eq_true] at fits
      have firstGrowth := firstTop fits.1
      have nextGrowth := nextTop fits.2
      rw [cleanupTop] at nextGrowth
      omega
    | trapped final message classification =>
      apply CostCommandResult.trapped final message
      cases classification with
      | terminal final trace outcome message execution terminal =>
        refine CommandResult.terminal final (firstTrace ++ trace) outcome message ?_ terminal
        apply firstExecution.erase.bind
        rw [← sameWorld]
        exact execution
      | resource final trace residual allowed progress =>
        refine CommandResult.resource final (firstTrace ++ trace) residual allowed ?_
        apply Prefix.bind_after firstExecution.erase
        rw [← sameWorld]
        exact progress
  | trapped final message classification =>
    apply CostCommandResult.trapped final message
    exact CommandResult.bind_trap (intermediate := .value type) (result := result)
      (liveMid := mid) (next := fun value => next.denote pure.funs (program.funs pure.funs) (.cons value env))
      classification id

end Verified.Wasi
