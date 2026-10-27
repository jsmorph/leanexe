import Verified.Wasi.CommandCodeSpec
import Verified.Wasi.CompilerFacts
import Verified.Wasi.CommandBind

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem command_bind_unit_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty} {result : ResultTy}
    (facts : CompilerFacts source target pure effects pool)
    (first : Command pureSigs effectSigs context .unit)
    (next : Command pureSigs effectSigs context result)
    (firstSpec : CommandCodeSpec source target pure effects pool first)
    (nextSpec : CommandCodeSpec source target pure effects pool next) :
    CommandCodeSpec source target pure effects pool
      (.bind (intermediate := .unit) (result := result) first next) := by
  intro World host targetHost depth env slots live h base heap initial locals
    valid below depthParam positions vars at_ safe scratch cap low room ready covered place
  let mid := fun i => live i || next.uses i
  let all := fun i => mid i || first.uses i
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
  have firstRun := firstSpec World host targetHost depth env slots mid h base heap initial locals
    valid below depthParam positions vars at_ safe scratch cap low firstRoom firstReady
    firstCovered placement.1
  have sequence := wp_sequence_unit (result := result)
    (first := first.denote pure.funs effects env)
    (next := fun _ : Unit => next.denote pure.funs effects env)
    (nextCode := next.code (pool := pool) source h slots base live)
    vars scratch midSelected selected firstRun
    (fun middleHeap middle middleLocals _ _ after _ =>
      nextSpec World host targetHost depth env slots live h base middleHeap middle middleLocals
        valid below (by rw [after.frame.params]; exact depthParam)
        (after.frame.positions.trans positions) after.holds after.step.at_
        (after.pool_safe safe vars scratch midSelected facts.poolApart).1
        (after.scratch vars scratch midSelected)
        (by rw [after.step.cap source]; exact cap)
        (by rw [after.frame.params]; exact low) nextRoom nextReady nextCovered placement.2)
  exact sequence

end Verified.Wasi
