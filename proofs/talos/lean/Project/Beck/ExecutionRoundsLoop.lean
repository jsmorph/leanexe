import Project.Beck.ExecutionRoundsGuard
import Project.Beck.ExecutionRoundsStep
import Project.ProofKit.BlockLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def roundsMeasure (_store : Store Unit) (frame : Locals) : Nat :=
  match (frame.params[0]? : Option Value), (frame.locals[5]? : Option Value) with
  | some (.i64 fuel), some (.i64 flag) => if flag = 0 then fuel.toNat + 1 else 0
  | _, _ => 0

theorem roundsMeasure_eq {locals : List Value} {stopped : Bool} {point : Point} {pointOwner root internal : UInt64}
    (state : RoundsLocals locals stopped point pointOwner root internal) (store : Store Unit) (fuel : Nat)
    (input : Input) (inputRoot : UInt64) (bound : fuel ≤ 6) :
    roundsMeasure store { params := roundsParams fuel input point inputRoot pointOwner root, locals := locals } =
      if stopped then 0 else fuel + 1 := by
  have fit : fuel < UInt64.size := by change fuel < 18446744073709551616; omega
  cases stopped <;> simp [roundsMeasure, roundsParams, state.flag, UInt64.toNat_ofNat_of_lt' fit]

def roundsInv (initial : Store Unit) (heap : Heap) (input : Input) (inputRoot : UInt64)
    (initialNode : FreeNode) (target : Point) (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ current fuel point roundNumber node pointOwner internal stopped locals,
    current.At store ∧ heap.Frame initial current store ∧
    Project.Beck.State.Valid input.jobs point roundNumber ∧ roundNumber + fuel ≤ 6 ∧
    (Project.Beck.Counting.live input point).card ≤ fuel ∧
    current.OwnsWords store node point.numerators ∧
    (node = initialNode ∨ FreshFor heap node) ∧
    (internal = 0 ∨ internal = node.root ∧ FreshFor heap node) ∧ node.root ≠ inputRoot ∧
    (stopped = true → allFrozen point = true) ∧
    target = (if stopped then point else rounds fuel input point) ∧
    OutputBudget store current (roundMaxBytes * (if stopped then 0 else fuel) + remaining) pageLimit Project.Beck.«module» ∧
    RoundsLocals locals stopped point pointOwner node.root internal ∧
    frame = { params := roundsParams fuel input point inputRoot pointOwner node.root, locals := locals }

def roundsDone (initial : Store Unit) (heap : Heap) (input : Input) (inputRoot : UInt64)
    (initialNode : FreeNode) (target : Point) (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ current fuel node pointOwner internal stopped locals,
    current.At store ∧ heap.Frame initial current store ∧ current.OwnsWords store node target.numerators ∧
    (node = initialNode ∨ FreshFor heap node) ∧ node.root ≠ inputRoot ∧ allFrozen target = true ∧
    OutputBudget store current remaining pageLimit Project.Beck.«module» ∧
    RoundsLocals locals stopped target pointOwner node.root internal ∧
    frame = { params := roundsParams fuel input target inputRoot pointOwner node.root, locals := locals }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem roundsLoop_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (locals : List Value) (fuel : Nat) (input : Input) (point : Point) (inputNode initialNode : FreeNode) (pointOwner : UInt64)
    (roundNumber remaining pageLimit : Nat)
    (state : RoundsLocals locals false point pointOwner initialNode.root 0)
    (valid : heap.At initial) (supported : Project.Beck.State.Supported input)
    (pointValid : Project.Beck.State.Valid input.jobs point roundNumber) (roundBudget : roundNumber + fuel ≤ 6)
    (enough : (Project.Beck.Counting.live input point).card ≤ fuel)
    (owned : heap.OwnsWords initial initialNode point.numerators)
    (inputOwned : heap.OwnsWords initial inputNode input.incidence) (different : initialNode.root ≠ inputNode.root)
    (inputSize : input.incidence.size = input.jobs * input.categories)
    (categories : input.categories ≤ 8) (overlap : input.overlap ≤ 8)
    (budget : OutputBudget initial heap (roundMaxBytes * fuel + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap finalFuel resultNode resultOwner internal stopped nextLocals,
      finalHeap.At final → finalHeap.OwnsWords final resultNode (rounds fuel input point).numerators →
      heap.Frame initial finalHeap final → (resultNode = initialNode ∨ FreshFor heap resultNode) →
      resultNode.root ≠ inputNode.root → allFrozen (rounds fuel input point) = true →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      RoundsLocals nextLocals stopped (rounds fuel input point) resultOwner resultNode.root internal →
      wp Project.Beck.«module» rest Q final
        { params := roundsParams finalFuel input (rounds fuel input point) inputNode.root resultOwner resultNode.root, locals := nextLocals } env) :
    wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 roundsBody]] ++ rest) Q initial
      { params := roundsParams fuel input point inputNode.root pointOwner initialNode.root, locals := locals } env := by
  let target := rounds fuel input point
  have inputNonzero : inputNode.root ≠ 0 := by
    intro zero
    have := inputOwned.buffer.rootBound
    rw [zero] at this
    contradiction
  apply BlockLoop.program_spec Project.Beck.«module» env initial _ roundsBody
    (roundsInv initial heap input inputNode.root initialNode target remaining pageLimit)
    (roundsDone initial heap input inputNode.root initialNode target remaining pageLimit) roundsMeasure
  · rintro store frame ⟨current, f, p, r, node, owner, internal, stopped, ls, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
    rfl
  · rintro store frame ⟨current, f, node, owner, internal, stopped, ls, _, _, _, _, _, _, _, _, rfl⟩
    rfl
  · exact ⟨heap, fuel, point, roundNumber, initialNode, pointOwner, 0, false, locals, valid, Heap.Frame.refl heap initial,
      pointValid, roundBudget, enough, owned, Or.inl rfl, Or.inl rfl, different, by simp, rfl, budget, state, rfl⟩
  · rintro store frame ⟨current, f, p, r, node, owner, internal, stopped, ls, currentValid, preserved,
      currentPoint, currentRoundBudget, currentEnough, currentOwned, output, active, currentDifferent,
      stoppedFrozen, correct, currentBudget, currentState, rfl⟩
    have fuelBound : f ≤ 6 := by omega
    apply roundsGuard_exact env store ls f input p inputNode.root owner node.root internal stopped fuelBound currentState
    · intro nonzero running
      subst stopped
      cases f with
      | zero => exact False.elim (nonzero rfl)
      | succ f =>
        have stepBudget : OutputBudget store current (roundMaxBytes + (roundMaxBytes * f + remaining)) pageLimit Project.Beck.«module» :=
          currentBudget.mono (by simp only [Bool.false_eq_true, reduceIte, Nat.mul_add, Nat.mul_one]; omega)
        apply roundsStep_exact env initial store heap current ls f input p node inputNode.root owner internal r
          (roundMaxBytes * f + remaining) pageLimit currentState currentValid currentOwned preserved active
          currentDifferent inputNonzero supported currentPoint (by omega)
          (preserved.words (ownedWords_protects inputOwned) inputOwned.buffer.values)
          (preserved.protects _ _ (ownedWords_protects inputOwned)) inputSize categories overlap stepBudget
        · intro frozen nextLocals nextState
          constructor
          · refine ⟨current, f + 1, p, r, node, owner, internal, true, nextLocals, currentValid, preserved,
              currentPoint, currentRoundBudget, currentEnough, currentOwned, output, active, currentDifferent,
              fun _ => frozen, ?_, currentBudget.mono (by simp), nextState, rfl⟩
            simpa [rounds, frozen] using correct
          · rw [roundsMeasure_eq nextState store (f + 1) input inputNode.root fuelBound,
              roundsMeasure_eq currentState store (f + 1) input inputNode.root fuelBound]
            simp
        · intro running final finalHeap nextNode finalValid finalOwned finalFrame fresh finalBudget nextLocals nextState
          have live := (Project.Beck.Loop.live_nonempty input p currentPoint.size).mpr running
          have nextPoint := (Project.Beck.SourceRound.round_valid_progress input p r supported currentPoint (by omega) live).1
          have decreases := Project.Beck.Loop.live_decreases input p r supported currentPoint (by omega) live
          have nonzero : (LeanExe.Examples.Beck.round input p).denominator ≠ 0 := by
            intro zero
            have positive := nextPoint.positive
            simp [zero] at positive
          have nextDifferent : nextNode.root ≠ inputNode.root := Ne.symm
            (ownedRoots_ne (finalFrame.ownsWords finalValid inputOwned) finalOwned
              (fresh.separated inputOwned finalOwned.buffer.rootBound))
          constructor
          · refine ⟨finalHeap, f, LeanExe.Examples.Beck.round input p, r + 1, nextNode, nextNode.root, nextNode.root, false, nextLocals,
              finalValid, finalFrame, nextPoint, by omega, by omega, finalOwned, Or.inr fresh,
              Or.inr ⟨rfl, fresh⟩, nextDifferent, by simp, ?_, finalBudget, nextState, rfl⟩
            simpa [rounds, running, nonzero] using correct
          · rw [roundsMeasure_eq nextState final f input inputNode.root (by omega),
              roundsMeasure_eq currentState store (f + 1) input inputNode.root fuelBound]
            simp
    · intro finished
      have frozen : allFrozen p = true := by
        rcases finished with exhausted | halted
        · subst f
          cases h : allFrozen p
          · have positive := ((Project.Beck.Loop.live_nonempty input p currentPoint.size).mpr h).card_pos
            omega
          · rfl
        · exact stoppedFrozen halted
      have result : target = p := by
        rcases finished with exhausted | halted
        · subst f
          cases stopped <;> simpa [rounds, frozen] using correct
        · simpa only [halted, reduceIte] using correct
      change roundsDone initial heap input inputNode.root initialNode target remaining pageLimit store _
      rw [result]
      exact ⟨current, f, node, owner, internal, stopped, ls, currentValid, preserved, currentOwned, output, currentDifferent,
        frozen, currentBudget.mono (Nat.le_add_left _ _), currentState, rfl⟩
  · rintro final frame ⟨finalHeap, finalFuel, resultNode, resultOwner, internal, stopped, nextLocals, finalValid, finalFrame,
      finalOwned, output, finalDifferent, frozen, finalBudget, finalState, rfl⟩
    exact next final finalHeap finalFuel resultNode resultOwner internal stopped nextLocals finalValid finalOwned finalFrame output
      finalDifferent frozen finalBudget finalState

#print axioms roundsLoop_exact

end Project.Beck.Execution
