import Verified.Wasi.CommandConditional
import Verified.Wasi.CommandCodeSpec
import Verified.Wasi.CompilerFacts
import Verified.AlignedCorrect

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime

theorem command_ite_spec {source target : Wasm.Module}
    {pure : Resource.PureContext pureSigs} {effects : EffectFuns effectSigs}
    {pool : Bytes.LiteralPool} {context : List Ty} {result : ResultTy}
    {condition : Expr pureSigs context .bool}
    {yes no : Command pureSigs effectSigs context result}
    (facts : CompilerFacts source target pure effects pool) (sourceHost : HostEnv Unit)
    (yesSpec : CommandCodeSpec source target pure effects pool yes)
    (noSpec : CommandCodeSpec source target pure effects pool no) :
    CommandCodeSpec source target pure effects pool (.ite condition yes no) := by
  intro World host targetHost depth env slots live h base heap initial locals
    valid below depthParam positions vars at_ safe scratch cap low room ready covered place
  let mid := fun i => live i || yes.uses i || no.uses i
  let picked := bif condition.denote pure.funs env then yes else no
  have allEq : (fun i => live i || (Command.ite condition yes no).uses i) =
      (fun i => mid i || condition.uses i) := by
    funext i
    simp only [Command.uses, mid, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  rw [allEq] at vars safe scratch ⊢
  have conditionFragment := ready
    (condition.code (pool := pool) h slots base mid) (by simp [Command.fragments, mid])
  have cleanupForm : ∀ choice : Bool, Encoding.ProgramForm (releaseWhere context slots
      (fun i => mid i && !(live i || (bif choice then yes else no).uses i))) := by
    intro choice
    cases choice <;> exact
      (ready _ (by simp [Command.fragments, mid])).1
  have cleanupClosed : ∀ choice : Bool, Relocation.programClosed source.funcs.length
      (releaseWhere context slots
        (fun i => mid i && !(live i || (bif choice then yes else no).uses i))) = true := by
    intro choice
    cases choice <;> exact
      (ready _ (by simp [Command.fragments, mid])).2
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
  have pickedSpec : CommandCodeSpec source target pure effects pool picked := by
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
  have spec := condition.code_spec source pure.funs pure.flags (pure.callBounds depth)
    (pure.callFits depth) sourceHost facts.runtime (Calls.at facts.calls depth) conditionCovered
    (fun _ => depthParam) env slots [] mid
  have noCoerce : coerceCode h .bool (condition.mode (slots.map Slot.mode)) .owned base = [] := by
    simp [coerceCode, Ty.scalar]
  refine wp_command_ite (sourceHost := sourceHost) facts.runtime facts.layout facts.profile spec
    (by simpa only [noCoerce, List.append_nil] using conditionFragment.1)
    (by simpa only [noCoerce, List.append_nil] using conditionFragment.2)
    cleanupForm cleanupClosed positions rfl vars scratch at_ safe facts.poolApart cap low
    (by simpa only [copyWidth, Ty.scalar, ite_true, Nat.max_zero] using conditionBound)
    (by omega) places.1 (fun _ => rfl) ?_
  dsimp only
  intro prefixHeap conditionStore prefixLocals first sameWorld prefixTop middleHeap middle
    evolution top world at_ held safe apart cap
  exact pickedSpec World host targetHost depth env slots live h (base + result.width)
    middleHeap middle { prefixLocals with values := locals.values }
    valid below (by rw [first.frame.params]; exact depthParam)
    (first.frame.positions.trans positions) held at_ safe apart cap
    (by rw [first.frame.params]; omega) (by omega) pickedReady pickedCovered pickedPlace

end Verified.Wasi
