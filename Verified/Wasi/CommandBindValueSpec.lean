import Verified.Wasi.BindContext
import Verified.Wasi.CompilerFacts
import Verified.Wasi.CommandCodeSpec
import Verified.Wasi.LoopRelease
import Verified.Wasi.Cleanup

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem command_bind_value_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty} {type : Ty} {result : ResultTy}
    (facts : CompilerFacts source target pure effects pool) (sourceHost : HostEnv Unit)
    (first : Command pureSigs effectSigs context (.value type))
    (next : Command pureSigs effectSigs (type :: context) result)
    (firstSpec : CommandCodeSpec source target pure effects pool first)
    (nextSpec : CommandCodeSpec source target pure effects pool next) :
    CommandCodeSpec source target pure effects pool (.bind first next) := by
  intro World host targetHost depth env slots live h base heap initial locals
    valid below depthParam positions vars at_ safe scratch cap low room ready covered place
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
    heap initial locals valid below depthParam positions (vars.mono (Nat.le_add_right _ _))
    at_ safe scratch cap (by omega) firstRoom firstReady firstCovered placement.1
  have firstRun := wp.conseq (fun _ classification =>
    classification.lower vars midSelected (Nat.le_add_right _ _)) firstUpper
  simp only [Command.code, List.append_assoc]
  refine wp_sequence_value (type := type) (result := result)
    (first := first.denote pure.funs effects env)
    (next := fun value => next.denote pure.funs effects (.cons value env))
    (bodyIn := releaseIn)
    (nextCode := (if next.uses 0 = false then Relocation.program (releaseCode type base) else []) ++
      next.code (pool := pool) source h (⟨base, .owned⟩ :: slots) (base + type.width) (shift 1 live))
    vars scratch positions low resultRoom
    (fun i used => by simpa only [congrFun tail i] using used)
    midSelected selected firstRun ?_
  · intro middleHeap middle middleLocals words value trace execution after
      boundLocals frame held stack
    have tailSelected : ∀ i, releaseIn (i + 1) = true → mid i = true := by
      intro i used
      simpa only [congrFun tail i] using used
    have boundVars := bind_context_holds after frame held tailSelected
    have boundScratch := bind_context_scratch after vars scratch frame held midSelected tailSelected
    have boundSafe := bind_context_safe after vars scratch safe facts.poolApart
      frame held midSelected tailSelected
    refine wp_loopRelease (sourceHost := sourceHost) (targetHost := targetHost)
      (used := next.uses 0) (rest := next.code (pool := pool) source h
        (⟨base, .owned⟩ :: slots) (base + type.width) (shift 1 live))
      facts.runtime facts.layout facts.profile releaseReady.1 releaseReady.2 boundVars after.step.at_
      (by simp only [releaseIn, beq_self_eq_true, Bool.true_or])
      (by simp [bodyIn, shift]) bodySelected ?_
    intro finalHeap final cleanup _ sameWorld
    have cleanupAfter := cleanup_after cleanup
    have bodyRun := nextSpec World host targetHost depth (.cons value env)
      (⟨base, .owned⟩ :: slots) (shift 1 live) h (base + type.width) finalHeap final boundLocals
      valid below (by rw [frame.params, after.frame.params]; exact depthParam)
      (frame.positions.trans (after.frame.positions.trans positions)) cleanup.holds cleanup.step.at_
      (cleanupAfter.pool_safe boundSafe boundVars boundScratch bodySelected facts.poolApart).1
      (cleanupAfter.scratch boundVars boundScratch bodySelected)
      (by rw [cleanup.step.cap source, after.step.cap source]; exact cap)
      (by rw [frame.params, after.frame.params]; omega) nextRoom nextReady nextCovered placement.2
    refine wp.conseq (fun continuation classification => ?_) bodyRun
    have firstExecution : Exec (observedHost host) (.pure ()) middle.host []
        (.returned ()) final.host := by
      rw [sameWorld]
      exact Exec.pure (α := Unit) middle.host ()
    have joined := CommandResult.bind_unit (result := result) (aborts := true)
      (next := fun _ : Unit => next.denote pure.funs effects (.cons value env))
      boundVars boundScratch firstExecution cleanupAfter rfl
      classification bodySelected outputSelected
    simpa only [Action.bind, List.nil_append] using joined

end Verified.Wasi
