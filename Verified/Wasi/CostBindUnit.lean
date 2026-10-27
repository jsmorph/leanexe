import Verified.Wasi.CostCodeSpec
import Verified.Wasi.CompilerFacts
import Verified.Wasi.CommandBind
import Verified.Wasi.LoopAfter
import Verified.Wasi.ResourceBudget

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem cost_command_bind_unit_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {program : EffectProg pureSigs effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty} {result : ResultTy}
    (facts : CompilerFacts source target pure (program.funs pure.funs) pool)
    (first : Command pureSigs effectSigs context .unit)
    (next : Command pureSigs effectSigs context result)
    (firstSpec : CostCommandCodeSpec source target pure program pool first)
    (nextSpec : CostCommandCodeSpec source target pure program pool next) :
    CostCommandCodeSpec source target pure program pool
      (.bind (intermediate := .unit) (result := result) first next) := by
  intro World host targetHost depth env slots live h base heap initial locals budget aborts
    valid below depthParam positions vars at_ safe scratch cap low room ready covered place resource
  let mid := fun i => live i || next.uses i
  let all := fun i => mid i || first.uses i
  have shiftZero : shift 0 live = live := by
    funext index
    simp only [shift, Nat.not_lt_zero, ite_false, Nat.sub_zero]
  have allEq : (fun i => live i || (Command.bind first next).uses i) = all := by
    funext i
    change (live i || (first.uses i || next.uses i)) = ((live i || next.uses i) || first.uses i)
    simp only [Bool.or_assoc, Bool.or_comm]
  rw [allEq] at vars safe scratch ⊢
  have midSelected : ∀ i, mid i = true → all i = true := by
    intro i selected
    simp only [all, selected, Bool.true_or]
  have selected : ∀ i, live i = true → mid i = true := by
    intro i retained
    simp only [mid, retained, Bool.true_or]
  change base + (0 + max first.width next.width) ≤ h at room
  simp only [Nat.zero_add] at room
  have firstRoom : base + first.width ≤ h :=
    (Nat.add_le_add_left (Nat.le_max_left first.width next.width) base).trans room
  have nextRoom : base + next.width ≤ h :=
    (Nat.add_le_add_left (Nat.le_max_right first.width next.width) base).trans room
  have firstReady : first.Ready source h slots base mid pool := by
    intro fragment member
    exact ready fragment (List.mem_append_left _ member)
  have nextReady : next.Ready source h slots base live pool := by
    intro fragment member
    exact ready fragment (List.mem_append_right _ member)
  obtain ⟨firstCovered, nextCovered⟩ := (Command.covered_bind first next pool).mp covered
  have placement : first.placeArgs = true ∧ next.placeArgs = true := by
    change (first.placeArgs && next.placeArgs) = true at place
    simpa only [Bool.and_eq_true] using place
  have firstRun := firstSpec World host targetHost depth env slots mid h base heap initial locals budget aborts
    valid below depthParam positions vars at_ safe scratch cap low firstRoom firstReady
    firstCovered placement.1 (fun noAbort => by
      obtain ⟨within, bounded⟩ := resource noAbort
      exact ⟨within, bounded.bind_first⟩)
  let Q := CostCommandResult host pure program (.bind first next) depth env slots all live base
    heap initial locals aborts
  change wp target
    (first.code (pool := pool) source h slots base mid ++ next.code (pool := pool) source h slots base live)
    Q initial locals targetHost
  apply wp_append
  refine wp.conseq (fun continuation firstResult => ?_) firstRun
  cases firstResult with
  | returned value middleHeap middle middleLocals words firstTrace firstSpent firstFits
      firstExecution firstAfter firstTop =>
    cases value
    have empty : words = [] := firstAfter.rep
    subst words
    simp only [List.reverse_nil, List.nil_append, Then]
    have adjusted := firstAfter.reframe (show Frame base middleLocals
      { middleLocals with values := locals.values } from Frame.ofValues)
    have secondRun := nextSpec World host targetHost depth env slots live h base middleHeap middle
      { middleLocals with values := locals.values } (budget - firstSpent) aborts
      valid below (by rw [adjusted.frame.params]; exact depthParam)
      (adjusted.frame.positions.trans positions) adjusted.holds adjusted.step.at_
      (adjusted.pool_safe safe vars scratch midSelected facts.poolApart).1
      (adjusted.scratch vars scratch midSelected)
      (by rw [adjusted.step.cap source]; exact cap)
      (by rw [adjusted.frame.params]; exact low) nextRoom nextReady nextCovered placement.2
      (fun noAbort => by
        obtain ⟨within, bounded⟩ := resource noAbort
        obtain ⟨spentBound, fitFirst⟩ := bounded.bind_first.returned firstExecution
        refine ⟨within.shift (firstTop fitFirst) (by omega) (adjusted.step.cap source), ?_⟩
        simpa only [Resource.bindModes, ResultTy.bindCount, ResultTy.bindEnv, ResultTy.extend,
          shiftZero] using bounded.bind_next firstExecution)
    refine wp.conseq (fun continuation nextResult => ?_) secondRun
    cases nextResult with
    | returned value finalHeap final finalLocals words trace nextSpent nextFits
        nextExecution nextAfter nextTop =>
      have combined := After.thenUnit vars scratch adjusted nextAfter midSelected selected
      have execution : Resource.ResourceExec (observedHost host) pure program depth
          (slots.map Slot.mode) live (.bind first next) env initial.host (firstTrace ++ trace)
          (.returned value) final.host (firstSpent + nextSpent) (firstFits && nextFits) := by
        apply Resource.ResourceExec.bind_return firstExecution
        simpa only [Resource.bindModes, ResultTy.bindCount, ResultTy.bindEnv, ResultTy.extend,
          shiftZero] using nextExecution
      refine CostCommandResult.returned (result := result) value finalHeap final finalLocals words
        (firstTrace ++ trace) (firstSpent + nextSpent) (firstFits && nextFits) execution combined ?_
      intro fits
      simp only [Bool.and_eq_true] at fits
      have firstGrowth := firstTop fits.1
      have nextGrowth := nextTop fits.2
      omega
    | trapped final message classification =>
      apply CostCommandResult.trapped final message
      exact CommandResult.bind_after_trap (intermediate := .unit) (result := result)
        (liveMid := mid) (next := fun _ : Unit => next.denote pure.funs (program.funs pure.funs) env)
        firstExecution.erase classification
  | trapped final message classification =>
    apply CostCommandResult.trapped final message
    exact CommandResult.bind_trap (intermediate := .unit) (result := result)
      (liveMid := mid) (next := fun _ : Unit => next.denote pure.funs (program.funs pure.funs) env)
      classification id

end Verified.Wasi
