import Project.Beck.ExecutionFindBasisGuard

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def findBasisMeasure (_store : Store Unit) (frame : Locals) : Nat :=
  match (frame.params[0]? : Option Value), (frame.locals[8]? : Option Value) with
  | some (.i64 fuel), some (.i64 flag) => if flag = 0 then fuel.toNat + 1 else 0
  | _, _ => 0

theorem findBasisMeasure_eq {locals : List Value} {stopped : Bool} {basis : Basis}
    {rowOwner rowPointer columnOwner columnPointer : UInt64}
    (state : FindBasisLocals locals stopped basis rowOwner rowPointer columnOwner columnPointer)
    (store : Store Unit) (fuel width : Nat) (matrixOwner matrixPointer : UInt64) (bound : fuel ≤ 6) :
    findBasisMeasure store
      { params := findBasisParams fuel width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := locals } =
      if stopped then 0 else fuel + 1 := by
  have fit : fuel < UInt64.size := by change fuel < 18446744073709551616; omega
  cases stopped <;> simp [findBasisMeasure, findBasisParams, state.flag, UInt64.toNat_ofNat_of_lt' fit]

def findBasisInv (initial : Store Unit) (heap : Heap) (width : Nat) (matrix : Array UInt64)
    (matrixOwner matrixPointer : UInt64) (initialBasis target : Basis) (initialValues : List Value)
    (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ current fuel basis rowOwner rowPointer columnOwner columnPointer stopped locals,
    current.At store ∧ heap.Frame initial current store ∧ fuel ≤ 6 ∧
    Project.Beck.Basis.WellFormed width matrix basis ∧
    BasisReferences current store basis rowPointer columnPointer ∧
    BasisOutput heap current store initialBasis initialValues basis
      (basisValues basis rowOwner rowPointer columnOwner columnPointer) ∧
    target = (if stopped then basis else findBasis fuel width matrix basis) ∧
    OutputBudget store current (findBasisRoundBytes width matrix * (if stopped then 0 else fuel) + remaining) pageLimit Project.Beck.«module» ∧
    FindBasisLocals locals stopped basis rowOwner rowPointer columnOwner columnPointer ∧
    frame = { params := findBasisParams fuel width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := locals }

def findBasisDone (initial : Store Unit) (heap : Heap) (width : Nat)
    (matrixOwner matrixPointer : UInt64) (initialBasis target : Basis) (initialValues : List Value)
    (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ current fuel rowOwner rowPointer columnOwner columnPointer stopped locals,
    current.At store ∧ heap.Frame initial current store ∧
    BasisReferences current store target rowPointer columnPointer ∧
    BasisOutput heap current store initialBasis initialValues target
      (basisValues target rowOwner rowPointer columnOwner columnPointer) ∧
    OutputBudget store current remaining pageLimit Project.Beck.«module» ∧
    FindBasisLocals locals stopped target rowOwner rowPointer columnOwner columnPointer ∧
    frame = { params := findBasisParams fuel width matrixOwner matrixPointer target rowOwner rowPointer columnOwner columnPointer, locals := locals }

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem findBasisLoop_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (fuel width : Nat) (matrix : Array UInt64) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) (locals : List Value)
    (remaining pageLimit : Nat) (valid : heap.At initial)
    (wellFormed : Project.Beck.Basis.WellFormed width matrix basis)
    (fuelBound : fuel ≤ 6) (widthBound : width ≤ 6) (matrixBound : matrix.size ≤ 56) (rowsBound : matrix.size / width < 6)
    (state : FindBasisLocals locals false basis rowOwner rowPointer columnOwner columnPointer)
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (refs : BasisReferences heap initial basis rowPointer columnPointer)
    (budget : OutputBudget initial heap (findBasisRoundBytes width matrix * fuel + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final finalHeap, finalHeap.At final → heap.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      ∀ finalFuel ro rp co cp stopped nextLocals,
        BasisReferences finalHeap final (findBasis fuel width matrix basis) rp cp →
        BasisOutput heap finalHeap final basis (basisValues basis rowOwner rowPointer columnOwner columnPointer)
          (findBasis fuel width matrix basis) (basisValues (findBasis fuel width matrix basis) ro rp co cp) →
        FindBasisLocals nextLocals stopped (findBasis fuel width matrix basis) ro rp co cp →
        wp Project.Beck.«module» rest Q final
          { params := findBasisParams finalFuel width matrixOwner matrixPointer (findBasis fuel width matrix basis) ro rp co cp, locals := nextLocals } env) :
    wp Project.Beck.«module» ([.block 0 0 [.loop 0 0 findBasisBody]] ++ rest) Q initial
      { params := findBasisParams fuel width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := locals } env := by
  let initialValues := basisValues basis rowOwner rowPointer columnOwner columnPointer
  let target := findBasis fuel width matrix basis
  apply BlockLoop.program_spec Project.Beck.«module» env initial _ findBasisBody
    (findBasisInv initial heap width matrix matrixOwner matrixPointer basis target initialValues remaining pageLimit)
    (findBasisDone initial heap width matrixOwner matrixPointer basis target initialValues remaining pageLimit) findBasisMeasure
  · rintro store frame ⟨current, f, b, ro, rp, co, cp, stopped, ls, _, _, _, _, _, _, _, _, _, rfl⟩
    rfl
  · rintro store frame ⟨current, f, ro, rp, co, cp, stopped, ls, _, _, _, _, _, _, rfl⟩
    rfl
  · exact ⟨heap, fuel, basis, rowOwner, rowPointer, columnOwner, columnPointer, false, locals,
      valid, Heap.Frame.refl heap initial, fuelBound, wellFormed, refs, Or.inl ⟨rfl, rfl⟩, rfl, budget, state, rfl⟩
  · rintro store frame ⟨current, f, b, ro, rp, co, cp, stopped, ls, currentValid, preserved, fBound,
      currentWF, currentRefs, output, correct, currentBudget, currentState, rfl⟩
    apply findBasisGuard_exact env store ls f width matrixOwner matrixPointer b ro rp co cp stopped fBound currentState
    · intro nonzero active
      subst stopped
      cases f with
      | zero => exact False.elim (nonzero rfl)
      | succ f =>
        have stepBudget : OutputBudget store current
            (findBasisRoundBytes width matrix + (findBasisRoundBytes width matrix * f + remaining)) pageLimit Project.Beck.«module» := by
          simpa only [Bool.false_eq_true, reduceIte, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm] using currentBudget
        apply findBasisStep_exact env store current f width matrix matrixOwner matrixPointer b ro rp co cp ls
          (findBasisRoundBytes width matrix * f + remaining) pageLimit currentValid currentWF widthBound matrixBound rowsBound
          currentState (preserved.words matrixProtected matrixAt) (preserved.protects _ _ matrixProtected) currentRefs stepBudget
        · intro stable final finalHeap finalValid finalFrame finalBudget nextLocals nextState
          constructor
          · refine ⟨finalHeap, f + 1, b, ro, rp, co, cp, true, nextLocals, finalValid, preserved.trans finalFrame,
              fBound, currentWF, currentRefs.preserved finalFrame, output.preserved finalFrame finalValid, ?_, ?_, nextState, rfl⟩
            · exact correct.trans (findBasis_stable (f + 1) width matrix b stable)
            · exact finalBudget.mono (by simp)
          · rw [findBasisMeasure_eq nextState final (f + 1) width matrixOwner matrixPointer fBound,
              findBasisMeasure_eq currentState store (f + 1) width matrixOwner matrixPointer fBound]
            simp
        · intro nextBasis growing final finalHeap rowsNode columnsNode finalValid finalFrame finalBudget owned nextLocals nextState
          have nextWF : Project.Beck.Basis.WellFormed width matrix nextBasis := by
            simpa only [Project.Beck.Basis.extend_eq, growing, Option.getD_some] using Project.Beck.Basis.extend_wellFormed width matrix b currentWF
          constructor
          · refine ⟨finalHeap, f, nextBasis, rowsNode.root, rowsNode.root, columnsNode.root, columnsNode.root,
              false, nextLocals, finalValid, preserved.trans finalFrame, by omega, nextWF, owned.references,
              Or.inr ⟨rowsNode, columnsNode, owned.original preserved, rfl⟩, ?_, finalBudget, nextState, rfl⟩
            exact correct.trans (findBasis_growing f width matrix b nextBasis growing)
          · rw [findBasisMeasure_eq nextState final f width matrixOwner matrixPointer (by omega),
              findBasisMeasure_eq currentState store (f + 1) width matrixOwner matrixPointer fBound]
            simp
    · intro finished
      have result : target = b := by
        rcases finished with exhausted | halted
        · subst f
          simpa [findBasis] using correct
        · simpa only [halted, reduceIte] using correct
      change findBasisDone initial heap width matrixOwner matrixPointer basis target initialValues remaining pageLimit store _
      rw [result]
      exact ⟨current, f, ro, rp, co, cp, stopped, ls, currentValid, preserved, currentRefs, output,
        currentBudget.mono (Nat.le_add_left _ _), currentState, rfl⟩
  · rintro final frame ⟨finalHeap, finalFuel, ro, rp, co, cp, stopped, nextLocals, finalValid, finalFrame,
      finalRefs, output, finalBudget, finalState, rfl⟩
    exact next final finalHeap finalValid finalFrame finalBudget finalFuel ro rp co cp stopped nextLocals finalRefs output finalState

#print axioms findBasisLoop_exact

end Project.Beck.Execution
