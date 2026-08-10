import Project.ProofKit.FixedArrayTraversalInput
import Project.ProofKit.GuardedBackEdge

namespace Project.ProofKit.FixedArrayFoldBody

open Wasm

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem continuingGuardedProgram_spec
    (arrayLocal indexLocal stopLocal itemLocal scratch : Nat)
    (body : ScalarTransition.Stmt)
    (condition : ScalarTransition.Expr .bool)
    (continuing : ScalarTransition.Stmt)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr indexValue stopValue : UInt64)
    (input : Array UInt64) (index : Nat) (stepProgram : Wasm.Program)
    (initial afterBody afterCondition : ScalarTransition.State)
    (result : Bool)
    (hValues : frame.values = [])
    (hArrayLocal : frame.get arrayLocal = some (.i64 inputPtr))
    (hIndexLocal : frame.get indexLocal = some (.i64 indexValue))
    (hStopLocal : frame.get stopLocal = some (.i64 stopValue))
    (hIndexValue : indexValue = UInt64.ofNat index)
    (hContinueGuard : indexValue < stopValue)
    (hItem : frame.validIndex itemLocal)
    (hInput : UInt64Array.At st inputPtr input)
    (hIndex : index < input.size)
    (hLoaded :
      FixedArrayTraversalInput.dynamicResultFrame frame itemLocal input[index]
        hItem = initial.toLocals [])
    (hStepProgram : stepProgram =
      ScalarTransition.guardedBackEdgeProgram scratch body condition continuing)
    (hBody : body.eval scratch initial = some afterBody)
    (hCondition : condition.eval scratch afterBody =
      some (result, afterCondition))
    (Q : Assertion Unit)
    (hExit : result = true →
      Q (.Break 1 st (afterCondition.toLocals [])))
    (hContinue : result = false →
      ∃ afterContinue,
        continuing.eval scratch afterCondition = some afterContinue ∧
        Q (.Break 0 st (afterContinue.toLocals []))) :
    wp module_
      (FixedArrayTraversalInput.continuingProgram arrayLocal indexLocal
        stopLocal itemLocal ++ stepProgram)
      Q st frame env := by
  apply FixedArrayTraversalInput.continuingProgram_spec
    (arrayLocal := arrayLocal) (indexLocal := indexLocal)
    (stopLocal := stopLocal) (itemLocal := itemLocal)
    (module_ := module_) (env := env) (st := st) (frame := frame)
    (inputPtr := inputPtr) (indexValue := indexValue)
    (stopValue := stopValue) (input := input) (index := index)
    (hValues := hValues) (hArrayLocal := hArrayLocal)
    (hIndexLocal := hIndexLocal) (hStopLocal := hStopLocal)
    (hIndexValue := hIndexValue) (hContinue := hContinueGuard)
    (hItem := hItem) (hInput := hInput) (hIndex := hIndex)
    (Q := Q) (rest := stepProgram)
  rw [hLoaded, hStepProgram]
  simpa using ScalarTransition.guardedBackEdgeProgram_spec
    (scratch := scratch) (body := body) (condition := condition)
    (continuing := continuing) (initial := initial)
    (afterBody := afterBody) (afterCondition := afterCondition)
    (result := result) (values := []) (module_ := module_)
    (env := env) (store := st) (rest := []) (Q := Q)
    hBody hCondition hExit hContinue

end Project.ProofKit.FixedArrayFoldBody
