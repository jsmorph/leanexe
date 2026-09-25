import Project.ProofKit.PackedWordAccess

namespace Project.ProofKit.PackedHeaderField
open Wasm PackedMemory PackedFloatFrame

def program (offset : Nat) (expected : UInt32) : Wasm.Program :=
  [.iff 0 1
    ([.localGet 1, .localSet 5, .localGet 2, .localSet 6,
      .constI64 (UInt64.ofNat offset), .localSet 7,
      .localGet 7, .localGet 6, .leUI64] ++
    [.iff 0 1
      [.localGet 6, .localGet 7, .subI64, .constI64 4, .geUI64,
        .iff 0 1
          [.localGet 5, .localGet 7, .addI64, .wrapI64, .load32 0, .extendUI32]
          [.unreachable] [] [.i64]]
      [.unreachable] [] [.i64]] ++
    [.constI64 expected.toUInt64, .eqI64,
      .iff 0 1 [.constI64 1] [.constI64 0] [] [.i64],
      .constI64 0, .eqI64, .eqz])
    [.const 0] [] [.i32]]

theorem program_spec (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (owner ptr : UInt64) (bytes : ByteArray) (offset : Nat)
    (expected : UInt32) (accepted : Bool) (tail : List Value)
    (hBytes : ByteArrayAt initial.mem ptr.toNat bytes)
    (hOffset : accepted = true → offset + 4 ≤ bytes.size)
    (hParams : frame.params = [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat bytes.size)])
    (hLength : frame.locals.length = 5)
    (hValues : frame.values = .i32 (if accepted then 1 else 0) :: tail)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, result.params = frame.params → result.locals.length = 5 →
      result.values = .i32 (if accepted && (LeanExe.Packed.getUInt32LE! bytes offset == expected)
        then 1 else 0) :: tail → wp module_ rest Q initial result env) :
    wp module_ (program offset expected ++ rest) Q initial frame env := by
  cases accepted
  · simp only [program, List.cons_append, List.nil_append, wp_iff_control_types]
    refine wp_iff_cons hValues ?_
    rw [ite_eq_right (by decide)]
    wp_packed_frame [hParams, hLength]
    exact hNext _ hParams.symm hLength rfl
  · simp only [program, List.cons_append, List.nil_append, wp_iff_control_types]
    refine wp_iff_cons hValues ?_
    rw [ite_eq_left (by decide)]
    wp_packed_frame [hParams, hLength]
    apply PackedWordAccess.guard_spec module_ env initial _ ptr bytes offset 5 6 7 tail
      hBytes (hOffset rfl)
    · simp [Locals.get, hLength]
    · simp [Locals.get, hLength]
    · simp [Locals.get, hLength]
    · rfl
    wp_packed_frame [hParams, hLength]
    have hEq : (LeanExe.Packed.getUInt32LE! bytes offset).toUInt64 = expected.toUInt64 ↔
        LeanExe.Packed.getUInt32LE! bytes offset = expected := UInt32.toUInt64_inj
    by_cases he : LeanExe.Packed.getUInt32LE! bytes offset = expected
    all_goals
      refine wp_iff_cons rfl ?_
      first
        | rw [ite_eq_left (by simpa [hEq, he])]
        | rw [ite_eq_right (by simpa [hEq, he])]
      wp_packed_frame [hParams, hLength]
      apply hNext
      · exact hParams.symm
      · simp [hLength]
      · simp [he]

#print axioms program_spec

theorem fields_spec (fields : List (Nat × UInt32))
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (owner ptr : UInt64) (bytes : ByteArray) (accepted : Bool)
    (tail : List Value) (hBytes : ByteArrayAt initial.mem ptr.toNat bytes)
    (hOffsets : accepted = true → ∀ field ∈ fields, field.1 + 4 ≤ bytes.size)
    (hParams : frame.params = [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat bytes.size)])
    (hLength : frame.locals.length = 5)
    (hValues : frame.values = .i32 (if accepted then 1 else 0) :: tail)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, result.params = frame.params → result.locals.length = 5 →
      result.values = .i32 (if fields.foldl
        (fun valid field => valid && (LeanExe.Packed.getUInt32LE! bytes field.1 == field.2)) accepted
        then 1 else 0) :: tail → wp module_ rest Q initial result env) :
    wp module_ (fields.flatMap (fun field => program field.1 field.2) ++ rest) Q initial frame env := by
  induction fields generalizing frame accepted with
  | nil => exact hNext frame rfl hLength hValues
  | cons field fields ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    apply program_spec module_ env initial frame owner ptr bytes field.1 field.2 accepted tail
      hBytes (fun h => hOffsets h field (by simp)) hParams hLength hValues
    intro next hNextParams hNextLength hNextValues
    apply ih next (accepted && (LeanExe.Packed.getUInt32LE! bytes field.1 == field.2))
      (fun h f hf => hOffsets (by cases accepted <;> simp_all) f (List.mem_cons_of_mem field hf))
      (hNextParams.trans hParams) hNextLength hNextValues
    intro result hResultParams hResultLength hResultValues
    exact hNext result (hResultParams.trans hNextParams) hResultLength hResultValues

#print axioms fields_spec

end Project.ProofKit.PackedHeaderField
