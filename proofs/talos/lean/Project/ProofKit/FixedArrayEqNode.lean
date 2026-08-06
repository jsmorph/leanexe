import Project.ProofKit.FixedArrayTraversalInput

namespace Project.ProofKit.FixedArrayEqNode

open Wasm

def compareProgram (keyLocal : Nat) (equalBranch unequalBranch : Wasm.Program) :
    Wasm.Program :=
  [
  .localGet keyLocal,
  .eqI64,
  .iff 0 1 [
    .constI64 1
  ] [
    .constI64 0
  ],
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 0 equalBranch unequalBranch
  ]

def stackCompareProgram (equalBranch unequalBranch : Wasm.Program) :
    Wasm.Program :=
  [
  .eqI64,
  .iff 0 1 [
    .constI64 1
  ] [
    .constI64 0
  ],
  .constI64 0,
  .eqI64,
  .eqz,
  .iff 0 0 equalBranch unequalBranch
  ]

def program (offset index keyLocal : Nat)
    (equalBranch unequalBranch : Wasm.Program) : Wasm.Program :=
  FixedArrayTraversalInput.program offset index ++
    compareProgram keyLocal equalBranch unequalBranch

def keyFirstProgram (offset index keyLocal : Nat)
    (equalBranch unequalBranch : Wasm.Program) : Wasm.Program :=
  [.localGet keyLocal] ++ (FixedArrayTraversalInput.program offset index ++
    stackCompareProgram equalBranch unequalBranch)

def loadKeyProgram (offset index keyLocal : Nat) : Wasm.Program :=
  FixedArrayTraversalInput.program offset index ++ [.localSet keyLocal]

def keyFrame (offset keyLocal : Nat) (frame : Locals) (inputPtr : UInt64)
    (index : Nat) (value : UInt64) : Locals :=
  { frame with
    locals := ((frame.locals.set (offset + 4) (.i64 inputPtr)).set
      (offset + 5) (.i64 (UInt64.ofNat index))).set
      (keyLocal - 1) (.i64 value),
    values := [] }

theorem keyFrame_params (offset keyLocal : Nat) (frame : Locals)
    (inputPtr : UInt64) (index : Nat) (value : UInt64) :
    (keyFrame offset keyLocal frame inputPtr index value).params =
      frame.params := rfl

theorem keyFrame_locals_length (offset keyLocal : Nat) (frame : Locals)
    (inputPtr : UInt64) (index : Nat) (value : UInt64) :
    (keyFrame offset keyLocal frame inputPtr index value).locals.length =
      frame.locals.length := by
  simp [keyFrame]

theorem keyFrame_values (offset keyLocal : Nat) (frame : Locals)
    (inputPtr : UInt64) (index : Nat) (value : UInt64) :
    (keyFrame offset keyLocal frame inputPtr index value).values = [] := rfl

theorem keyFrame_get_key
    (offset keyLocal : Nat) (frame : Locals) (inputPtr : UInt64)
    (index : Nat) (value : UInt64)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = offset + 14)
    (hKeyPositive : 0 < keyLocal)
    (hKey : keyLocal < offset + 15) :
    (keyFrame offset keyLocal frame inputPtr index value).get keyLocal =
      some (.i64 value) := by
  have hNotParam : ¬keyLocal < frame.params.length := by
    rw [hParams]
    omega
  have hValid : keyLocal < frame.params.length + frame.locals.length := by
    rw [hParams, hLocals]
    omega
  have hLocal : keyLocal - frame.params.length = keyLocal - 1 := by
    rw [hParams]
  have hLocalBound : keyLocal - 1 < frame.locals.length := by
    rw [hLocals]
    omega
  simp [keyFrame, Wasm.Locals.get, hNotParam, hValid, hLocal,
    hLocalBound]

def branchFrame (offset : Nat) (frame : Locals) (inputPtr : UInt64)
    (index : Nat) (value : UInt64) : Locals :=
  { FixedArrayTraversalInput.resultFrame offset frame inputPtr index value with
    values := [] }

theorem branchFrame_params (offset : Nat) (frame : Locals)
    (inputPtr : UInt64) (index : Nat) (value : UInt64) :
    (branchFrame offset frame inputPtr index value).params = frame.params := rfl

theorem branchFrame_locals_length (offset : Nat) (frame : Locals)
    (inputPtr : UInt64) (index : Nat) (value : UInt64) :
    (branchFrame offset frame inputPtr index value).locals.length =
      frame.locals.length := by
  simp [branchFrame, FixedArrayTraversalInput.resultFrame]

theorem branchFrame_values (offset : Nat) (frame : Locals)
    (inputPtr : UInt64) (index : Nat) (value : UInt64) :
    (branchFrame offset frame inputPtr index value).values = [] := rfl

def branchPost (module_ : Wasm.Module) (env : HostEnv Unit)
    (rest : Wasm.Program) (Q : Assertion Unit) : Assertion Unit :=
  fun continuation => match continuation with
    | .Fallthrough final frame =>
        wp module_ rest Q final { frame with values := [] } env
    | .Break 0 final frame =>
        wp module_ rest Q final { frame with values := [] } env
    | .Break (index + 1) final frame => Q (.Break index final frame)
    | other => Q other

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem loadKeyProgram_spec
    (offset index keyLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr : UInt64) (input : Array UInt64)
    (hParams : frame.params = [.i64 inputPtr])
    (hLocals : frame.locals.length = offset + 14)
    (hValues : frame.values = [])
    (hInput : UInt64Array.At st inputPtr input)
    (hIndex : index < input.size)
    (hKeyPositive : 0 < keyLocal)
    (hKey : keyLocal < offset + 15)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st
      (keyFrame offset keyLocal frame inputPtr index input[index]) env) :
    wp module_ (loadKeyProgram offset index keyLocal ++ rest)
      Q st frame env := by
  unfold loadKeyProgram
  rw [List.append_assoc]
  apply FixedArrayTraversalInput.program_spec offset module_ env st frame
    inputPtr input index hParams hLocals hValues hInput hIndex
  have hNotZero : keyLocal ≠ 0 := hKeyPositive.ne'
  have hBound : keyLocal < 1 + (offset + 14) := by omega
  simpa [wp_simp, Wasm.Locals.set?, hParams, hLocals, hValues,
    hNotZero, hBound, keyFrame,
    FixedArrayTraversalInput.resultFrame] using hNext

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem program_spec
    (offset index keyLocal : Nat)
    (equalBranch unequalBranch rest : Wasm.Program)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr key : UInt64) (input : Array UInt64)
    (hParams : frame.params = [.i64 inputPtr])
    (hLocals : frame.locals.length = offset + 14)
    (hValues : frame.values = [])
    (hInput : UInt64Array.At st inputPtr input)
    (hIndex : index < input.size)
    (hKey :
      (FixedArrayTraversalInput.resultFrame offset frame inputPtr index
        input[index]).get keyLocal = some (.i64 key))
    (Q : Assertion Unit)
    (hEqual : input[index] = key ->
      wp module_ equalBranch (branchPost module_ env rest Q) st
        (branchFrame offset frame inputPtr index input[index]) env)
    (hUnequal : input[index] ≠ key ->
      wp module_ unequalBranch (branchPost module_ env rest Q) st
        (branchFrame offset frame inputPtr index input[index]) env) :
    wp module_
      (program offset index keyLocal equalBranch unequalBranch ++ rest)
      Q st frame env := by
  unfold program
  rw [List.append_assoc]
  apply FixedArrayTraversalInput.program_spec offset module_ env st frame
    inputPtr input index hParams hLocals hValues hInput hIndex
  unfold compareProgram
  simp only [List.cons_append, List.nil_append, wp_simp, hKey]
  refine wp_iff_cons rfl ?_
  by_cases hEq : input[index] = key
  · rw [if_pos (by simp [hEq])]
    wp_run
    refine wp_iff_cons (c := 1) (vs := []) (by rfl) ?_
    rw [if_pos (by simp)]
    apply Wasm.wp.conseq (Q := branchPost module_ env rest Q)
    · intro continuation hBranch
      cases continuation
      case Break depth final branchFrame' =>
        cases depth <;> simpa [branchPost] using hBranch
      all_goals simpa [branchPost] using hBranch
    · simpa [branchFrame] using hEqual hEq
  · rw [if_neg (by simp [hEq])]
    wp_run
    refine wp_iff_cons (c := 0) (vs := []) (by rfl) ?_
    rw [if_neg (by simp)]
    apply Wasm.wp.conseq (Q := branchPost module_ env rest Q)
    · intro continuation hBranch
      cases continuation
      case Break depth final branchFrame' =>
        cases depth <;> simpa [branchPost] using hBranch
      all_goals simpa [branchPost] using hBranch
    · simpa [branchFrame] using hUnequal hEq

set_option maxHeartbeats 1000000 in
set_option Elab.async false in
theorem keyFirstProgram_spec
    (offset index keyLocal : Nat)
    (equalBranch unequalBranch rest : Wasm.Program)
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (frame : Locals) (inputPtr key : UInt64) (input : Array UInt64)
    (hParams : frame.params = [.i64 inputPtr])
    (hLocals : frame.locals.length = offset + 14)
    (hValues : frame.values = [])
    (hInput : UInt64Array.At st inputPtr input)
    (hIndex : index < input.size)
    (hKey : frame.get keyLocal = some (.i64 key))
    (Q : Assertion Unit)
    (hEqual : input[index] = key ->
      wp module_ equalBranch (branchPost module_ env rest Q) st
        (branchFrame offset frame inputPtr index input[index]) env)
    (hUnequal : input[index] ≠ key ->
      wp module_ unequalBranch (branchPost module_ env rest Q) st
        (branchFrame offset frame inputPtr index input[index]) env) :
    wp module_
      (keyFirstProgram offset index keyLocal equalBranch unequalBranch ++ rest)
      Q st frame env := by
  unfold keyFirstProgram
  simp only [List.cons_append, wp_localGet_cons, hKey, hValues]
  rw [List.append_assoc]
  apply FixedArrayTraversalInput.program_stacked_spec offset module_ env st
    { frame with values := [.i64 key] } inputPtr input index [.i64 key]
    hParams hLocals rfl hInput hIndex
  simp only [wp_simp]
  refine wp_iff_cons rfl ?_
  by_cases hEq : input[index] = key
  · rw [if_pos (by simpa [eq_comm] using hEq)]
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    apply Wasm.wp.conseq (Q := branchPost module_ env rest Q)
    · intro continuation hBranch
      cases continuation
      case Break depth final branchFrame' =>
        cases depth <;> simpa [branchPost] using hBranch
      all_goals simpa [branchPost] using hBranch
    · simpa [branchFrame, FixedArrayTraversalInput.resultFrame,
        FixedArrayTraversalInput.stackedResultFrame] using hEqual hEq
  · rw [if_neg (by simpa [eq_comm] using hEq)]
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    apply Wasm.wp.conseq (Q := branchPost module_ env rest Q)
    · intro continuation hBranch
      cases continuation
      case Break depth final branchFrame' =>
        cases depth <;> simpa [branchPost] using hBranch
      all_goals simpa [branchPost] using hBranch
    · simpa [branchFrame, FixedArrayTraversalInput.resultFrame,
        FixedArrayTraversalInput.stackedResultFrame] using hUnequal hEq

macro "wp_fixed_array_eq_node " offset:term ", " index:term ", " keyLocal:term : tactic =>
  `(tactic|
    (change wp _
      (program $offset $index $keyLocal _ _ ++ _) _ _ _ _
     apply program_spec))

macro "wp_fixed_array_key_eq_node " offset:term ", " index:term ", " keyLocal:term : tactic =>
  `(tactic|
    (change wp _
      (keyFirstProgram $offset $index $keyLocal _ _ ++ _) _ _ _ _
     apply keyFirstProgram_spec))

macro "wp_fixed_array_search_key " offset:term ", " index:term ", " keyLocal:term : tactic =>
  `(tactic|
    (change wp _
      (loadKeyProgram $offset $index $keyLocal ++ _) _ _ _ _
     apply loadKeyProgram_spec))

end Project.ProofKit.FixedArrayEqNode
