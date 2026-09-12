import Project.ProofKit.CopyAddress
import Project.ProofKit.FixedArrayCopy

namespace Project.ProofKit.OffsetArrayCopy
open Wasm FixedArrayCopy

def body (sourceLocal targetLocal countLocal counterLocal : Nat)
    (sourceOffsetLocal targetOffsetLocal : Option Nat) : Wasm.Program :=
  [.localGet counterLocal, .localGet countLocal, .geUI64, .br_if 1] ++
    CopyAddress.program targetLocal counterLocal targetOffsetLocal ++
    CopyAddress.program sourceLocal counterLocal sourceOffsetLocal ++
    [.load64 0, .store64 0, .localGet counterLocal, .constI64 1,
      .addI64, .localSet counterLocal, .br 0]

def program (sourceLocal targetLocal countLocal counterLocal : Nat)
    (sourceOffsetLocal targetOffsetLocal : Option Nat) : Wasm.Program :=
  [.constI64 0, .localSet counterLocal,
    .block 0 0 [.loop 0 0 (body sourceLocal targetLocal countLocal counterLocal
      sourceOffsetLocal targetOffsetLocal)]]

private theorem offsetAt_counterFrame (frame : Locals) (counterLocal counter offset : Nat)
    (offsetLocal : Option Nat) (hCounter : frame.validIndex counterLocal)
    (hOffset : CopyAddress.OffsetAt frame offsetLocal offset)
    (hSeparate : ∀ index, offsetLocal = some index → index ≠ counterLocal) :
    CopyAddress.OffsetAt (counterFrame frame counterLocal counter hCounter) offsetLocal offset := by
  cases offsetLocal with
  | none => exact hOffset
  | some index =>
    exact (counterFrame_get_ne frame counterLocal counter index hCounter
      (hSeparate index rfl)).trans hOffset

private def copyInvariant (initial : Store Unit) (frame : Locals)
    (counterLocal : Nat) (hCounter : frame.validIndex counterLocal)
    (source target : UInt64) (sourceOffset targetOffset count : Nat) : AssertionF Unit :=
  fun current resultFrame => ∃ counter : Nat, counter ≤ count ∧
    resultFrame = counterFrame frame counterLocal counter hCounter ∧
    Memory.WritesRange initial current (target.toNat + 8 * (targetOffset + 1))
      (target.toNat + 8 * (targetOffset + count + 1)) ∧
    ∀ cell : Nat, cell < counter →
      cellRead current target (targetOffset + cell) =
        cellRead initial source (sourceOffset + cell)

private def measure (counterLocal count : Nat) (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get counterLocal with
  | some (.i64 counter) => count - counter.toNat
  | _ => 0

theorem program_spec
    (sourceLocal targetLocal countLocal counterLocal : Nat)
    (sourceOffsetLocal targetOffsetLocal : Option Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (source target : UInt64) (sourceCells targetCells sourceOffset targetOffset count : Nat)
    (hCounter : frame.validIndex counterLocal)
    (hCounterSource : sourceLocal ≠ counterLocal)
    (hCounterTarget : targetLocal ≠ counterLocal)
    (hCounterCount : countLocal ≠ counterLocal)
    (hCounterSourceOffset : ∀ index, sourceOffsetLocal = some index → index ≠ counterLocal)
    (hCounterTargetOffset : ∀ index, targetOffsetLocal = some index → index ≠ counterLocal)
    (hValues : frame.values = [])
    (hSourceLocal : frame.get sourceLocal = some (.i64 source))
    (hTargetLocal : frame.get targetLocal = some (.i64 target))
    (hCountLocal : frame.get countLocal = some (.i64 (UInt64.ofNat count)))
    (hSourceOffset : CopyAddress.OffsetAt frame sourceOffsetLocal sourceOffset)
    (hTargetOffset : CopyAddress.OffsetAt frame targetOffsetLocal targetOffset)
    (hSourceRange : sourceOffset + count ≤ sourceCells)
    (hTargetRange : targetOffset + count ≤ targetCells)
    (hSource32 : source.toNat + 8 * (sourceCells + 1) ≤ 4294967296)
    (hTarget32 : target.toNat + 8 * (targetCells + 1) ≤ 4294967296)
    (hSourceMemory : source.toNat + 8 * (sourceCells + 1) ≤ initial.mem.pages * 65536)
    (hTargetMemory : target.toNat + 8 * (targetCells + 1) ≤ initial.mem.pages * 65536)
    (hSeparate : source.toNat + 8 * (sourceCells + 1) ≤ target.toNat ∨
      target.toNat + 8 * (targetCells + 1) ≤ source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ final : Store Unit,
      Memory.WritesRange initial final (target.toNat + 8 * (targetOffset + 1))
        (target.toNat + 8 * (targetOffset + count + 1)) →
      (∀ cell : Nat, cell < count →
        cellRead final target (targetOffset + cell) = cellRead initial source (sourceOffset + cell)) →
      wp module_ rest Q final (counterFrame frame counterLocal count hCounter) env) :
    wp module_ (program sourceLocal targetLocal countLocal counterLocal
      sourceOffsetLocal targetOffsetLocal ++ rest) Q initial frame env := by
  have hCount64 : count < UInt64.size := by
    change count < 18446744073709551616
    omega
  have hCountNat := UInt64.toNat_ofNat_of_lt' hCount64
  simp only [program, List.cons_append, List.nil_append]
  apply initializeCounter_spec hCounter hValues
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := copyInvariant initial frame counterLocal hCounter source target sourceOffset targetOffset count)
    (μ := measure counterLocal count)
  · exact ⟨0, Nat.zero_le _, rfl, Memory.WritesRange.refl .., by omega⟩
  · rintro current currentFrame ⟨counter, hLe, rfl, hWrites, hCopied⟩
    have hCounterNat := UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt hLe hCount64)
    have hCounterGet := counterFrame_get_counter frame counterLocal counter hCounter
    have hSourceGet := (counterFrame_get_ne frame counterLocal counter sourceLocal
      hCounter hCounterSource).trans hSourceLocal
    have hTargetGet := (counterFrame_get_ne frame counterLocal counter targetLocal
      hCounter hCounterTarget).trans hTargetLocal
    have hCountGet := (counterFrame_get_ne frame counterLocal counter countLocal
      hCounter hCounterCount).trans hCountLocal
    have hSourceOffsetGet := offsetAt_counterFrame frame counterLocal counter sourceOffset
      sourceOffsetLocal hCounter hSourceOffset hCounterSourceOffset
    have hTargetOffsetGet := offsetAt_counterFrame frame counterLocal counter targetOffset
      targetOffsetLocal hCounter hTargetOffset hCounterTargetOffset
    simp only [body, List.append_assoc, List.cons_append, List.nil_append,
      wp_localGet_cons, Frame.withValues_get, hCounterGet, hCountGet,
      counterFrame_values, wp_geUI64_cons, wp_br_if_cons]
    by_cases hEnd : counter = count
    · subst counter
      simp
      convert hNext current hWrites hCopied using 1
      apply Frame.ext <;> rfl
    · have hLt : counter < count := by omega
      have hGuard : ¬UInt64.ofNat counter ≥ UInt64.ofNat count := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hCounterNat, hCountNat]
        omega
      rw [if_neg hGuard]
      have hSourceCell : sourceOffset + counter < sourceCells := by omega
      have hTargetCell : targetOffset + counter < targetCells := by omega
      have hLoadBound : (cellAddress source (sourceOffset + counter)).toNat + 8 ≤
          current.mem.pages * 65536 := by
        rw [cellAddress_toNat hSource32 hSourceCell, hWrites.2.1]
        omega
      have hStoreBound : (cellAddress target (targetOffset + counter)).toNat + 8 ≤
          current.mem.pages * 65536 := by
        rw [cellAddress_toNat hTarget32 hTargetCell, hWrites.2.1]
        omega
      have hRead : cellRead current source (sourceOffset + counter) =
          cellRead initial source (sourceOffset + counter) := by
        apply hWrites.read64
        rw [cellAddress_toNat hSource32 hSourceCell]
        rcases hSeparate with hBefore | hAfter <;> omega
      apply CopyAddress.program_spec targetLocal counterLocal targetOffsetLocal module_ env current
        (counterFrame frame counterLocal counter hCounter) target targetOffset counter []
        rfl hTargetGet hCounterGet hTargetOffsetGet
      apply CopyAddress.program_spec sourceLocal counterLocal sourceOffsetLocal module_ env current
        { counterFrame frame counterLocal counter hCounter with values :=
          [.i32 (UInt64Array.wordAddress target (targetOffset + counter + 1))] }
        source sourceOffset counter _ rfl hSourceGet hCounterGet
        (by cases sourceOffsetLocal <;> exact hSourceOffsetGet)
      change wp module_ _ _ current
        { counterFrame frame counterLocal counter hCounter with values :=
          [.i32 (cellAddress source (sourceOffset + counter)),
            .i32 (cellAddress target (targetOffset + counter))] } env
      simp only [wp_load64_cons, wp_store64_cons, UInt32.add_zero,
        UInt32.toNat_zero, Nat.add_zero]
      rw [if_neg (Nat.not_lt.mpr hLoadBound), if_neg (Nat.not_lt.mpr hStoreBound)]
      change wp module_ _ _
        { current with
          mem := current.mem.write64 (cellAddress target (targetOffset + counter))
            (cellRead current source (sourceOffset + counter)) }
        (counterFrame frame counterLocal counter hCounter) env
      rw [hRead]
      have hSucc : UInt64.ofNat counter + 1 = UInt64.ofNat (counter + 1) := by
        exact (UInt64.ofNat_add counter 1).symm
      simp only [wp_localGet_cons, hCounterGet, counterFrame_values, wp_constI64_cons,
        wp_addI64_cons, hSucc, wp_localSet_cons, counterFrame_withValues_set?_counter,
        wp_br_cons, List.take_zero, List.drop_zero, List.nil_append]
      refine ⟨?_, ?_⟩
      · refine ⟨counter + 1, by omega, rfl, ?_, ?_⟩
        · apply hWrites.trans
          apply Memory.WritesRange.write64
          · rw [cellAddress_toNat hTarget32 hTargetCell]
            omega
          · rw [cellAddress_toNat hTarget32 hTargetCell]
            omega
        · intro cell hCell
          by_cases hEq : cell = counter
          · subst cell
            exact Memory.read64_write64 ..
          · apply Eq.trans (Memory.read64_write64_disjoint _ _ _ _ ?_)
              (hCopied cell (by omega))
            rw [cellAddress_toNat hTarget32 (by omega : targetOffset + cell < targetCells),
              cellAddress_toNat hTarget32 hTargetCell]
            omega
      · change measure counterLocal count _
          (counterFrame frame counterLocal (counter + 1) hCounter) < _
        simp only [measure, counterFrame_get_counter]
        rw [UInt64.toNat_ofNat_of_lt' (by omega : counter + 1 < UInt64.size), hCounterNat]
        omega

#print axioms program_spec

end Project.ProofKit.OffsetArrayCopy
