import Project.F64Clip.Execution
import Project.ProofKit.FixedArrayTraversalInput
import Project.ProofKit.BlockLoop

namespace Project.F64Clip.Spec
open Wasm Project.ProofKit Project.ProofKit.F64Order

def scanSuffix : Wasm.Program :=
  [.localGet 5, .localSet 6, .localGet 6, .call 1,
   .constI64 0, .neI64, .eqz,
   .iff 0 0 [.constI64 0, .localSet 13, .br 2] [],
   .localGet 10, .constI64 1, .addI64, .localSet 10, .br 0]

def scanBody : Wasm.Program :=
  FixedArrayTraversalInput.continuingProgram 8 10 12 5 ++ scanSuffix

def scanFrame (count bound unused ptr : UInt64) (size index : Nat) (last ok : UInt64) : Locals :=
  { params := [.i64 count, .i64 bound, .i64 unused, .i64 ptr]
    locals := [.i64 bound, .i64 last, .i64 last, .i64 0, .i64 ptr,
      .i64 (UInt64.ofNat size), .i64 (UInt64.ofNat index), .i64 (UInt64.ofNat size),
      .i64 (UInt64.ofNat size), .i64 ok, .i64 ptr, .i64 0]
    values := [] }

def scanInv (initial : Store Unit) (count bound unused ptr : UInt64) (w : Array UInt64) :
    AssertionF Unit := fun st frame =>
  st = initial ∧ ∃ index last, index ≤ w.size ∧
    frame = scanFrame count bound unused ptr w.size index last 1 ∧
    ∀ i, i < index → finiteBits w[i]! = true

def scanDone (initial : Store Unit) (count bound unused ptr : UInt64) (w : Array UInt64) :
    AssertionF Unit := fun st frame =>
  st = initial ∧ ∃ index last, frame = scanFrame count bound unused ptr w.size index last
    (if w.all (fun x => finiteBits x) then 1 else 0)

def scanMeasure (w : Array UInt64) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get 10 with
  | some (.i64 index) => w.size-index.toNat
  | _ => 0

theorem scan_step (env : HostEnv Unit) (initial : Store Unit) (count bound unused ptr : UInt64)
    (w : Array UInt64) (hInput : UInt64Array.At initial ptr w)
    (st : Store Unit) (frame : Locals) (hInv : scanInv initial count bound unused ptr w st frame) :
    wp Project.F64Clip.module scanBody
      (BlockLoop.stepPost (scanInv initial count bound unused ptr w)
        (scanDone initial count bound unused ptr w) (scanMeasure w) (scanMeasure w st frame)) st frame env := by
  rcases hInv with ⟨hStore, index, last, hIndex, rfl, hPrefix⟩
  subst st
  have hIndexNat : (UInt64.ofNat index).toNat = index :=
    UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt hIndex hInput.size_lt)
  have hSizeNat : (UInt64.ofNat w.size).toNat = w.size :=
    UInt64.toNat_ofNat_of_lt' hInput.size_lt
  by_cases hEnd : index = w.size
  · subst index
    have hAll : w.all (fun x => finiteBits x) = true := by
      apply Array.all_eq_true.mpr
      intro i hi
      simpa [hi] using hPrefix i hi
    unfold scanBody
    apply FixedArrayTraversalInput.continuingProgram_exit_spec 8 10 12 5
      Project.F64Clip.module env initial _ (UInt64.ofNat w.size) rfl rfl rfl
    exact ⟨rfl, w.size, last, by simp only [hAll, reduceIte]; rfl⟩
  · have hi : index < w.size := by omega
    have hlt : UInt64.ofNat index < UInt64.ofNat w.size := by
      rw [UInt64.lt_iff_toNat_lt, hIndexNat, hSizeNat]
      exact hi
    unfold scanBody
    refine FixedArrayTraversalInput.continuingProgram_spec 8 10 12 5 Project.F64Clip.module env
      initial _ ptr (UInt64.ofNat index) (UInt64.ofNat w.size) w index
      rfl rfl rfl rfl rfl hlt (by simp [scanFrame, Locals.validIndex]) hInput hi _ _ ?_
    · unfold scanSuffix
      wp_fixed_frame [FixedArrayTraversalInput.dynamicResultFrame, scanFrame, Locals.set]
      refine wp_call_tw (finite_exact env initial w[index]) ?_
      rintro final values ⟨hFinal, rfl⟩
      subst final
      cases hf : finiteBits w[index]
      · have hAll : w.all (fun x => finiteBits x) = false := by
          apply Bool.eq_false_iff.mpr
          intro hall
          have hh := Array.all_eq_true.mp hall index hi
          rw [hf] at hh
          cases hh
        wp_fixed_frame [scanFrame, hf]
        refine wp_iff_cons rfl ?_
        simp [show (1 : UInt32) ≠ 0 by decide]
        wp_fixed_frame [scanFrame, BlockLoop.stepPost]
        exact ⟨rfl, index, w[index], by simp only [hAll]; rfl⟩
      · wp_fixed_frame [scanFrame, hf]
        refine wp_iff_cons rfl ?_
        simp [show (1 : UInt32) ≠ 0 by decide, show (1 : UInt64) ≠ 0 by decide]
        wp_fixed_frame [scanFrame, BlockLoop.stepPost]
        constructor
        · refine ⟨rfl, index+1, w[index], by omega, ?_, ?_⟩
          · simp [scanFrame, UInt64.ofNat_add]
          · intro i hi'
            by_cases heq : i = index
            · subst i
              simpa [hi] using hf
            · exact hPrefix i (by omega)
        · have hNextNat : (UInt64.ofNat (index+1)).toNat = index+1 :=
            UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt (by omega) hInput.size_lt)
          change w.size-(UInt64.ofNat index+UInt64.ofNat 1).toNat < w.size-(UInt64.ofNat index).toNat
          rw [← UInt64.ofNat_add, hNextNat, hIndexNat]
          omega

#print axioms scan_step
end Project.F64Clip.Spec
