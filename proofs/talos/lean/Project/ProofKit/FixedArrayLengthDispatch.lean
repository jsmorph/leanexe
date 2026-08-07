import Project.ProofKit.FixedArrayEqNode

namespace Project.ProofKit.FixedArrayLengthDispatch

open Wasm

macro "wp_length_dispatch" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 10000000 }) (discharger := omega) [
      wp_simp, Wasm.Locals.get, Wasm.Locals.set?,
      Wasm.Locals.validIndex, List.length_set, List.getElem?_set,
      List.getElem?_cons_zero,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
      Nat.add_left_cancel_iff, Nat.add_lt_add_iff_left, $ts,*])

def program (inputLocal expectedSize : Nat)
    (invalidBranch validBranch : Wasm.Program) : Wasm.Program :=
  [
  .localGet 0,
  .localSet inputLocal,
  .localGet inputLocal,
  .wrapI64,
  .load64 0,
  .constI64 (UInt64.ofNat expectedSize),
  .eqI64,
  .iff 0 1 [
    .constI64 1
  ] [
    .constI64 0
  ],
  .constI64 0,
  .eqI64,
  .eqz,
  .eqz,
  .iff 0 1 [
    .constI64 1
  ] [
    .constI64 0
  ],
  .constI64 1,
  .eqI64,
  .iff 0 1 [
    .constI64 1
  ] [
    .constI64 0
  ],
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 0 invalidBranch validBranch
  ]

def eqProgram (inputLocal expectedSize : Nat)
    (invalidBranch validBranch : Wasm.Program) : Wasm.Program :=
  [
  .localGet 0,
  .localSet inputLocal,
  .localGet inputLocal,
  .wrapI64,
  .load64 0,
  .constI64 (UInt64.ofNat expectedSize),
  .eqI64,
  .iff 0 1 [
    .constI64 1
  ] [
    .constI64 0
  ],
  .constI64 1,
  .eqI64,
  .iff 0 1 [
    .constI64 1
  ] [
    .constI64 0
  ],
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 0 validBranch invalidBranch
  ]

def leProgram (inputLocal maximumSize : Nat)
    (validBranch invalidBranch : Wasm.Program) : Wasm.Program :=
  [
  .localGet 0,
  .localSet inputLocal,
  .localGet inputLocal,
  .wrapI64,
  .load64 0,
  .constI64 (UInt64.ofNat maximumSize),
  .leUI64,
  .iff 0 0 validBranch invalidBranch
  ]

def branchFrame (inputLocal : Nat) (frame : Locals)
    (inputPtr : UInt64) : Locals :=
  { frame with
    locals := frame.locals.set (inputLocal - 1) (.i64 inputPtr),
    values := [] }

theorem branchFrame_params (inputLocal : Nat) (frame : Locals)
    (inputPtr : UInt64) :
    (branchFrame inputLocal frame inputPtr).params = frame.params := rfl

theorem branchFrame_locals_length (inputLocal : Nat) (frame : Locals)
    (inputPtr : UInt64) :
    (branchFrame inputLocal frame inputPtr).locals.length =
      frame.locals.length := by
  simp [branchFrame]

theorem branchFrame_values (inputLocal : Nat) (frame : Locals)
    (inputPtr : UInt64) :
    (branchFrame inputLocal frame inputPtr).values = [] := rfl

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem program_spec
    (inputLocal expectedSize : Nat)
    (invalidBranch validBranch rest : Wasm.Program)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr : UInt64) (input : Array UInt64)
    (hParams : frame.params = [.i64 inputPtr])
    (hValues : frame.values = [])
    (hInputLocalPositive : 0 < inputLocal)
    (hInputLocal : inputLocal < 1 + frame.locals.length)
    (hExpectedSize : expectedSize < UInt64.size)
    (hInput : UInt64Array.At st inputPtr input)
    (Q : Assertion Unit)
    (hInvalid : input.size ≠ expectedSize ->
      wp module_ invalidBranch
        (FixedArrayEqNode.branchPost module_ env rest Q) st
        (branchFrame inputLocal frame inputPtr) env)
    (hValid : input.size = expectedSize ->
      wp module_ validBranch
        (FixedArrayEqNode.branchPost module_ env rest Q) st
        (branchFrame inputLocal frame inputPtr) env) :
    wp module_
      (program inputLocal expectedSize invalidBranch validBranch ++ rest)
      Q st frame env := by
  have hNotParam : ¬inputLocal < frame.params.length := by
    rw [hParams]
    simp
    omega
  have hLocalValid : inputLocal < frame.params.length + frame.locals.length := by
    rw [hParams]
    simp
    exact hInputLocal
  have hLengthRead := hInput.lengthRead
  have hLengthBound := hInput.generatedLengthBound
  have hInputAddress := hInput.pointerAddress_eq
  have hEncoded := hInput.encodedSize_eq (size := expectedSize) hExpectedSize
  unfold program
  simp only [List.cons_append, List.nil_append]
  wp_length_dispatch [hParams, hValues, hNotParam, hLocalValid,
    hInputLocalPositive.ne', hInputLocal]
  rw [if_neg (Nat.not_lt.mpr hLengthBound)]
  rw [hInputAddress, hLengthRead]
  by_cases hSize : input.size = expectedSize
  · refine wp_iff_cons rfl ?_
    rw [if_pos (by simp [hEncoded.mpr hSize])]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    apply Wasm.wp.conseq
      (Q := FixedArrayEqNode.branchPost module_ env rest Q)
    · intro continuation hBranch
      cases continuation
      case Break depth final branchFrame' =>
        cases depth <;> simpa [FixedArrayEqNode.branchPost] using hBranch
      all_goals simpa [FixedArrayEqNode.branchPost] using hBranch
    · simpa [branchFrame, hParams, hValues] using hValid hSize
  · refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hEncoded, hSize])]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    apply Wasm.wp.conseq
      (Q := FixedArrayEqNode.branchPost module_ env rest Q)
    · intro continuation hBranch
      cases continuation
      case Break depth final branchFrame' =>
        cases depth <;> simpa [FixedArrayEqNode.branchPost] using hBranch
      all_goals simpa [FixedArrayEqNode.branchPost] using hBranch
    · simpa [branchFrame, hParams, hValues] using hInvalid hSize

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem eqProgram_spec
    (inputLocal expectedSize : Nat)
    (invalidBranch validBranch rest : Wasm.Program)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr : UInt64) (input : Array UInt64)
    (hParams : frame.params = [.i64 inputPtr])
    (hValues : frame.values = [])
    (hInputLocalPositive : 0 < inputLocal)
    (hInputLocal : inputLocal < 1 + frame.locals.length)
    (hExpectedSize : expectedSize < UInt64.size)
    (hInput : UInt64Array.At st inputPtr input)
    (Q : Assertion Unit)
    (hInvalid : input.size ≠ expectedSize ->
      wp module_ invalidBranch
        (FixedArrayEqNode.branchPost module_ env rest Q) st
        (branchFrame inputLocal frame inputPtr) env)
    (hValid : input.size = expectedSize ->
      wp module_ validBranch
        (FixedArrayEqNode.branchPost module_ env rest Q) st
        (branchFrame inputLocal frame inputPtr) env) :
    wp module_
      (eqProgram inputLocal expectedSize invalidBranch validBranch ++ rest)
      Q st frame env := by
  have hNotParam : ¬inputLocal < frame.params.length := by
    rw [hParams]
    simp
    omega
  have hLocalValid : inputLocal < frame.params.length + frame.locals.length := by
    rw [hParams]
    simp
    exact hInputLocal
  have hLengthRead := hInput.lengthRead
  have hLengthBound := hInput.generatedLengthBound
  have hInputAddress := hInput.pointerAddress_eq
  have hEncoded := hInput.encodedSize_eq (size := expectedSize) hExpectedSize
  unfold eqProgram
  simp only [List.cons_append, List.nil_append]
  wp_length_dispatch [hParams, hValues, hNotParam, hLocalValid,
    hInputLocalPositive.ne', hInputLocal]
  rw [if_neg (Nat.not_lt.mpr hLengthBound)]
  rw [hInputAddress, hLengthRead]
  by_cases hSize : input.size = expectedSize
  · refine wp_iff_cons rfl ?_
    rw [if_pos (by simp [hEncoded.mpr hSize])]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    apply Wasm.wp.conseq
      (Q := FixedArrayEqNode.branchPost module_ env rest Q)
    · intro continuation hBranch
      cases continuation
      case Break depth final branchFrame' =>
        cases depth <;> simpa [FixedArrayEqNode.branchPost] using hBranch
      all_goals simpa [FixedArrayEqNode.branchPost] using hBranch
    · simpa [branchFrame, hParams, hValues] using hValid hSize
  · refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hEncoded, hSize])]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    apply Wasm.wp.conseq
      (Q := FixedArrayEqNode.branchPost module_ env rest Q)
    · intro continuation hBranch
      cases continuation
      case Break depth final branchFrame' =>
        cases depth <;> simpa [FixedArrayEqNode.branchPost] using hBranch
      all_goals simpa [FixedArrayEqNode.branchPost] using hBranch
    · simpa [branchFrame, hParams, hValues] using hInvalid hSize

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem leProgram_spec
    (inputLocal maximumSize : Nat)
    (validBranch invalidBranch rest : Wasm.Program)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr : UInt64) (input : Array UInt64)
    (hParams : frame.params = [.i64 inputPtr])
    (hValues : frame.values = [])
    (hInputLocalPositive : 0 < inputLocal)
    (hInputLocal : inputLocal < 1 + frame.locals.length)
    (hMaximumSize : maximumSize < UInt64.size)
    (hInput : UInt64Array.At st inputPtr input)
    (Q : Assertion Unit)
    (hValid : input.size ≤ maximumSize ->
      wp module_ validBranch
        (FixedArrayEqNode.branchPost module_ env rest Q) st
        (branchFrame inputLocal frame inputPtr) env)
    (hInvalid : ¬input.size ≤ maximumSize ->
      wp module_ invalidBranch
        (FixedArrayEqNode.branchPost module_ env rest Q) st
        (branchFrame inputLocal frame inputPtr) env) :
    wp module_
      (leProgram inputLocal maximumSize validBranch invalidBranch ++ rest)
      Q st frame env := by
  have hNotParam : ¬inputLocal < frame.params.length := by
    rw [hParams]
    simp
    omega
  have hLocalValid : inputLocal < frame.params.length + frame.locals.length := by
    rw [hParams]
    simp
    exact hInputLocal
  have hLengthRead := hInput.lengthRead
  have hLengthBound := hInput.generatedLengthBound
  have hInputAddress := hInput.pointerAddress_eq
  have hEncoded :
      UInt64.ofNat input.size ≤ UInt64.ofNat maximumSize ↔
        input.size ≤ maximumSize := by
    rw [UInt64.le_iff_toNat_le,
      UInt64.toNat_ofNat_of_lt' hInput.size_lt,
      UInt64.toNat_ofNat_of_lt' hMaximumSize]
  unfold leProgram
  simp only [List.cons_append, List.nil_append]
  wp_length_dispatch [hParams, hValues, hNotParam, hLocalValid,
    hInputLocalPositive.ne', hInputLocal]
  rw [if_neg (Nat.not_lt.mpr hLengthBound)]
  rw [hInputAddress, hLengthRead]
  refine wp_iff_cons rfl ?_
  by_cases hSize : input.size ≤ maximumSize
  · rw [if_pos (by simpa [hEncoded] using hSize)]
    apply Wasm.wp.conseq
      (Q := FixedArrayEqNode.branchPost module_ env rest Q)
    · intro continuation hBranch
      cases continuation
      case Break depth final branchFrame' =>
        cases depth <;> simpa [FixedArrayEqNode.branchPost] using hBranch
      all_goals simpa [FixedArrayEqNode.branchPost] using hBranch
    · simpa [branchFrame, hParams, hValues] using hValid hSize
  · rw [if_neg (by simpa [hEncoded] using hSize)]
    apply Wasm.wp.conseq
      (Q := FixedArrayEqNode.branchPost module_ env rest Q)
    · intro continuation hBranch
      cases continuation
      case Break depth final branchFrame' =>
        cases depth <;> simpa [FixedArrayEqNode.branchPost] using hBranch
      all_goals simpa [FixedArrayEqNode.branchPost] using hBranch
    · simpa [branchFrame, hParams, hValues] using hInvalid hSize

macro "wp_fixed_array_length_dispatch " inputLocal:term ", " expectedSize:term : tactic =>
  `(tactic|
    (change wp _
      (program $inputLocal $expectedSize _ _ ++ _) _ _ _ _
     apply program_spec))

macro "wp_fixed_array_length_eq_dispatch " inputLocal:term ", " expectedSize:term : tactic =>
  `(tactic|
    (change wp _
      (eqProgram $inputLocal $expectedSize _ _ ++ _) _ _ _ _
     apply eqProgram_spec))

macro "wp_fixed_array_length_le_dispatch " inputLocal:term ", " maximumSize:term : tactic =>
  `(tactic|
    (change wp _
      (leProgram $inputLocal $maximumSize _ _ ++ _) _ _ _ _
     apply leProgram_spec))

end Project.ProofKit.FixedArrayLengthDispatch
