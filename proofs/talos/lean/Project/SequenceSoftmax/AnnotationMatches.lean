import Project.SequenceSoftmax.Program
import Project.ProofKit.Annotation

import Project.ProofKit.FuelGuard




import Project.ProofKit.ScalarTransition
import Project.ProofKit.ScalarTransitionU64




import Project.ProofKit.FixedArrayLengthDispatch

import Project.ProofKit.FixedArrayCapacity

import Project.ProofKit.FixedArrayTraversalInput

import Project.ProofKit.FixedArrayFold




set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

namespace Project.SequenceSoftmax.AnnotationMatches

def function_0_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 5

theorem function_0_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.SequenceSoftmax.func0
      [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_0_while_loop_0_guard_program := by
  rfl

theorem function_0_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.SequenceSoftmax.func0 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_0_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.SequenceSoftmax.func0 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_1_while_loop_0_guard_program : Wasm.Program :=
  Project.ProofKit.FuelGuard.program 0 3

theorem function_1_while_loop_0_guard_eq :
    Project.ProofKit.Annotation.region Project.SequenceSoftmax.func1
      [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }] 0 7 = some function_1_while_loop_0_guard_program := by
  rfl

theorem function_1_while_loop_0_guard_tail_eq :
    (Project.ProofKit.Annotation.resolve Project.SequenceSoftmax.func1 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD [] = function_1_while_loop_0_guard_program ++ ((Project.ProofKit.Annotation.resolve Project.SequenceSoftmax.func1 [{ instructionIndex := 2, field := .block }, { instructionIndex := 0, field := .loop }]).getD []).drop 7 := by
  rfl

def function_8_array_fold_0_program : Wasm.Program :=
  (Project.ProofKit.Annotation.region Project.SequenceSoftmax.func8 [] 0 35).getD []

theorem function_8_array_fold_0_eq :
    Project.ProofKit.Annotation.region Project.SequenceSoftmax.func8 [] 0 35 = some function_8_array_fold_0_program := by
  rfl

theorem function_8_array_fold_0_tail_eq :
    ((Project.ProofKit.Annotation.resolve Project.SequenceSoftmax.func8 []).getD []).drop 0 =
      Project.SequenceSoftmax.AnnotationMatches.function_8_array_fold_0_program ++ ((Project.ProofKit.Annotation.resolve Project.SequenceSoftmax.func8 []).getD []).drop 35 := by
  rfl

def function_8_array_fold_0_continuing_program : Wasm.Program :=
  Project.ProofKit.FixedArrayTraversalInput.continuingProgram
    9 11
    13 3

theorem function_8_array_fold_0_continuing_eq :
    Project.ProofKit.Annotation.region Project.SequenceSoftmax.func8
      [{ instructionIndex := 32, field := .block }, { instructionIndex := 0, field := .loop }] 0 16 =
        some function_8_array_fold_0_continuing_program := by
  rfl

def function_8_array_fold_0_result_program : Wasm.Program :=
  Project.ProofKit.FixedArrayFold.resultProgram
    2 8

theorem function_8_array_fold_0_result_eq :
    Project.ProofKit.Annotation.region Project.SequenceSoftmax.func8
      [] 33
      35 = some function_8_array_fold_0_result_program := by
  rfl





def function_8_array_fold_0_state (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    Project.ProofKit.ScalarTransition.U64State :=
  { params := [v0, v1],
    locals := [v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19] }

def function_8_array_fold_0_continuing_frame (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) : Wasm.Locals :=
  (function_8_array_fold_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).toState.toLocals []

@[simp] theorem function_8_array_fold_0_continuing_frame_params (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).params = [.i64 v0, .i64 v1] := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_locals_length (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).locals.length = 18 := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_values (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).values = [] := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_0 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 0 = some (.i64 v0) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_1 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 1 = some (.i64 v1) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_2 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 2 = some (.i64 v2) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_3 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 3 = some (.i64 v3) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_4 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 4 = some (.i64 v4) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_5 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 5 = some (.i64 v5) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_6 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 6 = some (.i64 v6) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_7 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 7 = some (.i64 v7) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_8 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 8 = some (.i64 v8) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_9 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 9 = some (.i64 v9) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_10 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 10 = some (.i64 v10) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_11 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 11 = some (.i64 v11) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_12 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 12 = some (.i64 v12) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_13 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 13 = some (.i64 v13) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_14 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 14 = some (.i64 v14) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_15 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 15 = some (.i64 v15) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_16 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 16 = some (.i64 v16) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_17 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 17 = some (.i64 v17) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_18 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 18 = some (.i64 v18) := by
  rfl

@[simp] theorem function_8_array_fold_0_continuing_frame_get_19 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).get 19 = some (.i64 v19) := by
  rfl


theorem function_8_array_fold_0_continuing_item_valid (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) :
    (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19).validIndex 3 := by
  norm_num [Wasm.Locals.validIndex, function_8_array_fold_0_continuing_frame, function_8_array_fold_0_state,
    Project.ProofKit.ScalarTransition.U64State.toState]

theorem function_8_array_fold_0_continuing_loaded_frame_eq (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64) (value : UInt64) :
    Project.ProofKit.FixedArrayTraversalInput.dynamicResultFrame
      (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19) 3 value
      (function_8_array_fold_0_continuing_item_valid v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19) =
        function_8_array_fold_0_continuing_frame v0 v1 v2 value v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 := by
  simp [Project.ProofKit.FixedArrayTraversalInput.dynamicResultFrame,
    function_8_array_fold_0_continuing_frame, function_8_array_fold_0_state,
    Project.ProofKit.ScalarTransition.U64State.toState, Wasm.Locals.set]

theorem function_8_array_fold_0_continuing_spec (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 : UInt64)
    (module_ : Wasm.Module) (env : Wasm.HostEnv Unit) (st : Wasm.Store Unit)
    (input : Array UInt64) (index : Nat)
    (hIndexValue : v11 = UInt64.ofNat index)
    (hContinue : v11 < v13)
    (hInput : Project.ProofKit.UInt64Array.At st v9 input)
    (hIndex : index < input.size)
    (Q : Wasm.Assertion Unit) (rest : Wasm.Program)
    (hNext : Wasm.wp module_ rest Q st
      (Project.ProofKit.FixedArrayTraversalInput.dynamicResultFrame
        (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19) 3 input[index]
        (function_8_array_fold_0_continuing_item_valid v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19)) env) :
    Wasm.wp module_ (function_8_array_fold_0_continuing_program ++ rest) Q st
      (function_8_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19) env := by
  apply Project.ProofKit.FixedArrayTraversalInput.continuingProgram_spec
    (inputPtr := v9) (indexValue := v11)
    (stopValue := v13) (input := input) (index := index)
    (hValues := rfl) (hArrayLocal := rfl) (hIndexLocal := rfl)
    (hStopLocal := rfl) (hIndexValue := hIndexValue)
    (hContinue := hContinue) (hItem := function_8_array_fold_0_continuing_item_valid v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19)
    (hInput := hInput) (hIndex := hIndex)
  exact hNext



def function_10_array_fold_0_program : Wasm.Program :=
  (Project.ProofKit.Annotation.region Project.SequenceSoftmax.func10 [] 0 26).getD []

theorem function_10_array_fold_0_eq :
    Project.ProofKit.Annotation.region Project.SequenceSoftmax.func10 [] 0 26 = some function_10_array_fold_0_program := by
  rfl

theorem function_10_array_fold_0_tail_eq :
    ((Project.ProofKit.Annotation.resolve Project.SequenceSoftmax.func10 []).getD []).drop 0 =
      Project.SequenceSoftmax.AnnotationMatches.function_10_array_fold_0_program ++ ((Project.ProofKit.Annotation.resolve Project.SequenceSoftmax.func10 []).getD []).drop 26 := by
  rfl

def function_10_array_fold_0_continuing_program : Wasm.Program :=
  Project.ProofKit.FixedArrayTraversalInput.continuingProgram
    6 8
    10 3

theorem function_10_array_fold_0_continuing_eq :
    Project.ProofKit.Annotation.region Project.SequenceSoftmax.func10
      [{ instructionIndex := 23, field := .block }, { instructionIndex := 0, field := .loop }] 0 16 =
        some function_10_array_fold_0_continuing_program := by
  rfl

def function_10_array_fold_0_result_program : Wasm.Program :=
  Project.ProofKit.FixedArrayFold.resultProgram
    2 5

theorem function_10_array_fold_0_result_eq :
    Project.ProofKit.Annotation.region Project.SequenceSoftmax.func10
      [] 24
      26 = some function_10_array_fold_0_result_program := by
  rfl





def function_10_array_fold_0_state (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    Project.ProofKit.ScalarTransition.U64State :=
  { params := [v0, v1],
    locals := [v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] }

def function_10_array_fold_0_continuing_frame (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) : Wasm.Locals :=
  (function_10_array_fold_0_state v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).toState.toLocals []

@[simp] theorem function_10_array_fold_0_continuing_frame_params (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).params = [.i64 v0, .i64 v1] := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_locals_length (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).locals.length = 14 := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_values (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).values = [] := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_get_0 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).get 0 = some (.i64 v0) := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_get_1 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).get 1 = some (.i64 v1) := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_get_2 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).get 2 = some (.i64 v2) := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_get_3 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).get 3 = some (.i64 v3) := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_get_4 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).get 4 = some (.i64 v4) := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_get_5 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).get 5 = some (.i64 v5) := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_get_6 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).get 6 = some (.i64 v6) := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_get_7 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).get 7 = some (.i64 v7) := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_get_8 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).get 8 = some (.i64 v8) := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_get_9 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).get 9 = some (.i64 v9) := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_get_10 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).get 10 = some (.i64 v10) := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_get_11 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).get 11 = some (.i64 v11) := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_get_12 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).get 12 = some (.i64 v12) := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_get_13 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).get 13 = some (.i64 v13) := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_get_14 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).get 14 = some (.i64 v14) := by
  rfl

@[simp] theorem function_10_array_fold_0_continuing_frame_get_15 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).get 15 = some (.i64 v15) := by
  rfl


theorem function_10_array_fold_0_continuing_item_valid (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) :
    (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).validIndex 3 := by
  norm_num [Wasm.Locals.validIndex, function_10_array_fold_0_continuing_frame, function_10_array_fold_0_state,
    Project.ProofKit.ScalarTransition.U64State.toState]

theorem function_10_array_fold_0_continuing_loaded_frame_eq (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64) (value : UInt64) :
    Project.ProofKit.FixedArrayTraversalInput.dynamicResultFrame
      (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) 3 value
      (function_10_array_fold_0_continuing_item_valid v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) =
        function_10_array_fold_0_continuing_frame v0 v1 v2 value v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 := by
  simp [Project.ProofKit.FixedArrayTraversalInput.dynamicResultFrame,
    function_10_array_fold_0_continuing_frame, function_10_array_fold_0_state,
    Project.ProofKit.ScalarTransition.U64State.toState, Wasm.Locals.set]

theorem function_10_array_fold_0_continuing_spec (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : UInt64)
    (module_ : Wasm.Module) (env : Wasm.HostEnv Unit) (st : Wasm.Store Unit)
    (input : Array UInt64) (index : Nat)
    (hIndexValue : v8 = UInt64.ofNat index)
    (hContinue : v8 < v10)
    (hInput : Project.ProofKit.UInt64Array.At st v6 input)
    (hIndex : index < input.size)
    (Q : Wasm.Assertion Unit) (rest : Wasm.Program)
    (hNext : Wasm.wp module_ rest Q st
      (Project.ProofKit.FixedArrayTraversalInput.dynamicResultFrame
        (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) 3 input[index]
        (function_10_array_fold_0_continuing_item_valid v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)) env) :
    Wasm.wp module_ (function_10_array_fold_0_continuing_program ++ rest) Q st
      (function_10_array_fold_0_continuing_frame v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15) env := by
  apply Project.ProofKit.FixedArrayTraversalInput.continuingProgram_spec
    (inputPtr := v6) (indexValue := v8)
    (stopValue := v10) (input := input) (index := index)
    (hValues := rfl) (hArrayLocal := rfl) (hIndexLocal := rfl)
    (hStopLocal := rfl) (hIndexValue := hIndexValue)
    (hContinue := hContinue) (hItem := function_10_array_fold_0_continuing_item_valid v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15)
    (hInput := hInput) (hIndex := hIndex)
  exact hNext



def function_11_length_dispatch_0_valid_branch_program : Wasm.Program :=
  [
  .constI64 8,
  .constI64 0,
  .constI64 1,
  .mulI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .constI64 7,
  .addI64,
  .constI64 8,
  .divUI64,
  .constI64 8,
  .mulI64,
  .localSet 25,
  .localGet 25,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [
   .constI64 8,
   .localSet 25
  ] [],
  .constI64 0,
  .localSet 30,
  .constI64 0,
  .localSet 26,
  .globalGet 1,
  .localSet 27,
  .block 0 0 [
   .loop 0 0 [
    .localGet 27,
    .constI64 0,
    .eqI64,
    .br_if 1,
    .localGet 30,
    .constI64 0,
    .neI64,
    .br_if 1,
    .localGet 27,
    .constI64 32,
    .subI64,
    .wrapI64,
    .load64 0,
    .localSet 28,
    .localGet 27,
    .constI64 8,
    .subI64,
    .wrapI64,
    .load64 0,
    .localSet 29,
    .localGet 28,
    .localGet 25,
    .geUI64,
    .iff 0 0 [
     .localGet 26,
     .constI64 0,
     .eqI64,
     .iff 0 0 [
      .localGet 29,
      .globalSet 1
     ] [
      .localGet 26,
      .constI64 8,
      .subI64,
      .wrapI64,
      .localGet 29,
      .store64 0
     ],
     .localGet 27,
     .constI64 48,
     .subI64,
     .wrapI64,
     .constI64 5501223100278326855,
     .store64 0,
     .localGet 27,
     .constI64 40,
     .subI64,
     .wrapI64,
     .constI64 1,
     .store64 0,
     .localGet 27,
     .constI64 32,
     .subI64,
     .wrapI64,
     .localGet 28,
     .store64 0,
     .localGet 27,
     .constI64 24,
     .subI64,
     .wrapI64,
     .constI64 2,
     .store64 0,
     .localGet 27,
     .constI64 16,
     .subI64,
     .wrapI64,
     .constI64 1,
     .store64 0,
     .localGet 27,
     .constI64 8,
     .subI64,
     .wrapI64,
     .constI64 0,
     .store64 0,
     .localGet 27,
     .localSet 30
    ] [
     .localGet 27,
     .localSet 26,
     .localGet 29,
     .localSet 27
    ],
    .br 0
   ]
  ],
  .localGet 30,
  .constI64 0,
  .eqI64,
  .iff 0 0 [
   .globalGet 0,
   .constI64 48,
   .addI64,
   .localGet 25,
   .addI64,
   .localTee 28,
   .globalGet 0,
   .ltUI64,
   .iff 0 0 [
    .unreachable
   ] [],
   .localGet 28,
   .constI64 1,
   .subI64,
   .constI64 65536,
   .divUI64,
   .constI64 1,
   .addI64,
   .localSet 29,
   .memorySize,
   .extendUI32,
   .localGet 29,
   .ltUI64,
   .iff 0 0 [
    .localGet 29,
    .memorySize,
    .extendUI32,
    .subI64,
    .wrapI64,
    .memoryGrow,
    .const (-1),
    .eq,
    .iff 0 0 [
     .unreachable
    ] []
   ] [],
   .globalGet 0,
   .constI64 48,
   .addI64,
   .localSet 30,
   .localGet 28,
   .globalSet 0,
   .localGet 30,
   .constI64 48,
   .subI64,
   .wrapI64,
   .constI64 5501223100278326855,
   .store64 0,
   .localGet 30,
   .constI64 40,
   .subI64,
   .wrapI64,
   .constI64 1,
   .store64 0,
   .localGet 30,
   .constI64 32,
   .subI64,
   .wrapI64,
   .localGet 25,
   .store64 0,
   .localGet 30,
   .constI64 24,
   .subI64,
   .wrapI64,
   .constI64 2,
   .store64 0,
   .localGet 30,
   .constI64 16,
   .subI64,
   .wrapI64,
   .constI64 1,
   .store64 0,
   .localGet 30,
   .constI64 8,
   .subI64,
   .wrapI64,
   .constI64 0,
   .store64 0
  ] [],
  .globalGet 2,
  .constI64 1,
  .addI64,
  .globalSet 2,
  .localGet 30,
  .localSet 21,
  .localGet 21,
  .wrapI64,
  .constI64 0,
  .store64 0,
  .localGet 21,
  .localSet 1,
  .localGet 1,
  .localSet 20
]

def function_11_length_dispatch_0_invalid_branch_program : Wasm.Program :=
  [
  .constI64 0,
  .localSet 2,
  .localGet 0,
  .localSet 3,
  .constI64 0,
  .localSet 4,
  .localGet 0,
  .localSet 5,
  .localGet 4,
  .localGet 5,
  .call 8,
  .localSet 6,
  .localGet 6,
  .localSet 7,
  .localGet 2,
  .localGet 3,
  .localGet 7,
  .call 6,
  .localSet 9,
  .localSet 8,
  .localGet 8,
  .localSet 10,
  .localGet 9,
  .localSet 11,
  .localGet 10,
  .localSet 12,
  .localGet 11,
  .localSet 13,
  .localGet 10,
  .localSet 14,
  .localGet 11,
  .localSet 15,
  .localGet 14,
  .localGet 15,
  .call 10,
  .localSet 16,
  .localGet 16,
  .localSet 17,
  .localGet 12,
  .localGet 13,
  .localGet 17,
  .call 9,
  .localSet 19,
  .localSet 18,
  .localGet 19,
  .localSet 20,
  .localGet 8,
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 0 [
   .localGet 8,
   .call 15
  ] []
]

def function_11_length_dispatch_0_dispatch_program : Wasm.Program :=
  Project.ProofKit.FixedArrayLengthDispatch.eqProgram
    21 0
    function_11_length_dispatch_0_invalid_branch_program function_11_length_dispatch_0_valid_branch_program [.i64]

def function_11_length_dispatch_0_suffix_program : Wasm.Program :=
  [
  .localGet 20
]

theorem function_11_length_dispatch_0_dispatch_eq :
    Project.ProofKit.Annotation.region Project.SequenceSoftmax.func11
      [] 0
      15 = some function_11_length_dispatch_0_dispatch_program := by
  rfl

theorem function_11_length_dispatch_0_function_eq :
    Project.SequenceSoftmax.func11 =
      function_11_length_dispatch_0_dispatch_program ++ function_11_length_dispatch_0_suffix_program := by
  rfl

def function_11_length_dispatch_0_valid_capacity_program : Wasm.Program :=
  Project.ProofKit.FixedArrayCapacity.constantProgram
    0 1 25

theorem function_11_length_dispatch_0_valid_capacity_eq :
    Project.ProofKit.Annotation.region Project.SequenceSoftmax.func11
      [{ instructionIndex := 14, field := .thenBranch }] 0
      18 = some function_11_length_dispatch_0_valid_capacity_program := by
  rfl

end Project.SequenceSoftmax.AnnotationMatches
