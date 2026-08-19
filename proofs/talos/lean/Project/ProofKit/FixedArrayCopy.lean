import Project.ProofKit.Array
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

namespace Project.ProofKit.FixedArrayCopy

open Wasm

def prefixBody (sourceLocal targetLocal prefixLocal counterLocal : Nat) :
    Wasm.Program :=
  [
  .localGet counterLocal,
  .localGet prefixLocal,
  .geUI64,
  .br_if 1,
  .localGet targetLocal,
  .localGet counterLocal,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet sourceLocal,
  .localGet counterLocal,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .load64 0,
  .store64 0,
  .localGet counterLocal,
  .constI64 1,
  .addI64,
  .localSet counterLocal,
  .br 0
  ]

def prefixProgram (sourceLocal targetLocal prefixLocal counterLocal : Nat) :
    Wasm.Program :=
  [
  .constI64 0,
  .localSet counterLocal,
  .block 0 0 [
    .loop 0 0 (prefixBody sourceLocal targetLocal prefixLocal counterLocal)
  ]
  ]

def suffixBody (skipCells sourceLocal targetLocal prefixLocal suffixLocal
    counterLocal : Nat) : Wasm.Program :=
  [
  .localGet counterLocal,
  .localGet suffixLocal,
  .geUI64,
  .br_if 1,
  .localGet targetLocal,
  .localGet prefixLocal,
  .localGet counterLocal,
  .addI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet sourceLocal,
  .localGet prefixLocal,
  .constI64 (UInt64.ofNat skipCells),
  .addI64,
  .localGet counterLocal,
  .addI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .load64 0,
  .store64 0,
  .localGet counterLocal,
  .constI64 1,
  .addI64,
  .localSet counterLocal,
  .br 0
  ]

def suffixProgram (skipCells sourceLocal targetLocal prefixLocal suffixLocal
    counterLocal : Nat) : Wasm.Program :=
  [
  .constI64 0,
  .localSet counterLocal,
  .block 0 0 [
    .loop 0 0 (suffixBody skipCells sourceLocal targetLocal prefixLocal
      suffixLocal counterLocal)
  ]
  ]

def program (skipCells sourceLocal targetLocal prefixLocal suffixLocal
    counterLocal : Nat) : Wasm.Program :=
  prefixProgram sourceLocal targetLocal prefixLocal counterLocal ++
    suffixProgram skipCells sourceLocal targetLocal prefixLocal suffixLocal
      counterLocal

def counterFrame (frame : Locals) (counterLocal counter : Nat)
    (hCounter : frame.validIndex counterLocal) : Locals :=
  { frame.set counterLocal (.i64 (UInt64.ofNat counter)) hCounter with
    values := [] }

@[simp]
private theorem withValues_get (frame : Locals) (values : List Value)
    (index : Nat) :
    ({ frame with values := values } : Locals).get index = frame.get index := rfl

private theorem ofParts_eq (frame : Locals) (hValues : frame.values = []) :
    ({ params := frame.params, locals := frame.locals } : Locals) = frame := by
  cases frame
  simp_all

@[simp]
theorem counterFrame_params_length (frame : Locals) (counterLocal counter : Nat)
    (hCounter : frame.validIndex counterLocal) :
    (counterFrame frame counterLocal counter hCounter).params.length =
      frame.params.length := by
  unfold counterFrame Wasm.Locals.set
  split <;> simp

@[simp]
theorem counterFrame_locals_length (frame : Locals) (counterLocal counter : Nat)
    (hCounter : frame.validIndex counterLocal) :
    (counterFrame frame counterLocal counter hCounter).locals.length =
      frame.locals.length := by
  unfold counterFrame Wasm.Locals.set
  split <;> simp

@[simp]
theorem counterFrame_values (frame : Locals) (counterLocal counter : Nat)
    (hCounter : frame.validIndex counterLocal) :
    (counterFrame frame counterLocal counter hCounter).values = [] := rfl

@[simp]
theorem counterFrame_validIndex (frame : Locals) (counterLocal counter index : Nat)
    (hCounter : frame.validIndex counterLocal) :
    (counterFrame frame counterLocal counter hCounter).validIndex index ↔
      frame.validIndex index := by
  simp [Wasm.Locals.validIndex]

theorem counterFrame_get_counter (frame : Locals) (counterLocal counter : Nat)
    (hCounter : frame.validIndex counterLocal) :
    (counterFrame frame counterLocal counter hCounter).get counterLocal =
      some (.i64 (UInt64.ofNat counter)) := by
  unfold counterFrame Wasm.Locals.set Wasm.Locals.get
  by_cases hParam : counterLocal < frame.params.length
  · simp [hParam]
  · have hLocal : counterLocal < frame.params.length + frame.locals.length :=
      hCounter
    have hIndex : counterLocal - frame.params.length < frame.locals.length := by
      omega
    simp [hParam, hLocal, hIndex]

theorem counterFrame_get_ne (frame : Locals) (counterLocal counter index : Nat)
    (hCounter : frame.validIndex counterLocal) (hNe : index ≠ counterLocal) :
    (counterFrame frame counterLocal counter hCounter).get index =
      frame.get index := by
  unfold counterFrame Wasm.Locals.set Wasm.Locals.get
  by_cases hWriteParam : counterLocal < frame.params.length
  · by_cases hReadParam : index < frame.params.length
    · simp only [hWriteParam, hReadParam, if_true]
      rw [List.getElem?_set]
      simp [hReadParam, hNe.symm]
    · simp [hWriteParam, hReadParam]
  · have hWriteLocal :
        counterLocal < frame.params.length + frame.locals.length := hCounter
    by_cases hReadParam : index < frame.params.length
    · simp [hWriteParam, hReadParam]
    · by_cases hReadLocal : index < frame.params.length + frame.locals.length
      · have hLocalNe :
            index - frame.params.length ≠
              counterLocal - frame.params.length := by
          omega
        simp only [hWriteParam, hReadParam, hReadLocal, if_false, if_true]
        rw [List.getElem?_set]
        simp [hReadLocal, hLocalNe.symm]
      · simp [hWriteParam, hReadParam, hReadLocal]

theorem counterFrame_set?_counter (frame : Locals)
    (counterLocal current next : Nat)
    (hCounter : frame.validIndex counterLocal) :
    (counterFrame frame counterLocal current hCounter).set? counterLocal
        (.i64 (UInt64.ofNat next)) =
      some (counterFrame frame counterLocal next hCounter) := by
  unfold counterFrame Wasm.Locals.set Wasm.Locals.set?
  by_cases hParam : counterLocal < frame.params.length
  · simp [hParam, List.set_set]
  · have hLocal : counterLocal < frame.params.length + frame.locals.length :=
      hCounter
    have hIndex : counterLocal - frame.params.length < frame.locals.length := by
      omega
    simp [hParam, hLocal, List.set_set]

theorem counterFrame_counterFrame (frame : Locals)
    (counterLocal first second : Nat)
    (hCounter : frame.validIndex counterLocal)
    (hNested :
      (counterFrame frame counterLocal first hCounter).validIndex counterLocal) :
    counterFrame (counterFrame frame counterLocal first hCounter)
        counterLocal second hNested =
      counterFrame frame counterLocal second hCounter := by
  unfold counterFrame Wasm.Locals.set
  by_cases hParam : counterLocal < frame.params.length
  · simp [hParam, List.set_set]
  · simp [hParam, List.set_set]

private theorem counterFrame_withValues_set?_counter (frame : Locals)
    (counterLocal current next : Nat) (values : List Value)
    (hCounter : frame.validIndex counterLocal) :
    ({ counterFrame frame counterLocal current hCounter with values := values }
        : Locals).set? counterLocal (.i64 (UInt64.ofNat next)) =
      some ({ counterFrame frame counterLocal next hCounter with
        values := values } : Locals) := by
  unfold counterFrame Wasm.Locals.set Wasm.Locals.set?
  by_cases hParam : counterLocal < frame.params.length
  · simp [hParam, List.set_set]
  · have hLocal : counterLocal < frame.params.length + frame.locals.length :=
      hCounter
    simp [hParam, hLocal, List.set_set]

private theorem initializeCounter_spec
    {module_ : Wasm.Module} {env : HostEnv Unit} {store : Store Unit}
    {frame : Locals} {counterLocal counter : Nat}
    (hCounter : frame.validIndex counterLocal)
    (hValues : frame.values = []) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store
      (counterFrame frame counterLocal counter hCounter) env) :
    wp module_
      (.constI64 (UInt64.ofNat counter) :: .localSet counterLocal :: rest)
      Q store frame env := by
  simp only [wp_constI64_cons, wp_localSet_cons, hValues]
  by_cases hParam : counterLocal < frame.params.length
  · simpa [counterFrame, Wasm.Locals.set, Wasm.Locals.set?, hParam]
      using hNext
  · have hLocal : counterLocal < frame.params.length + frame.locals.length :=
      hCounter
    simpa [counterFrame, Wasm.Locals.set, Wasm.Locals.set?, hParam, hLocal]
      using hNext

def cellAddress (ptr : UInt64) (cell : Nat) : UInt32 :=
  UInt64Array.wordAddress ptr (cell + 1)

def cellRead (store : Store Unit) (ptr : UInt64) (cell : Nat) : UInt64 :=
  store.mem.read64 (cellAddress ptr cell)

theorem cellAddress_toNat {ptr : UInt64} {cells cell : Nat}
    (hFit32 : ptr.toNat + 8 * (cells + 1) ≤ 4294967296)
    (hCell : cell < cells) :
    (cellAddress ptr cell).toNat = ptr.toNat + 8 * (cell + 1) := by
  exact UInt64Array.wordAddress_toNat hFit32 (by omega)

theorem generatedCellAddress_eq {ptr : UInt64} {cells cell : Nat}
    (hFit32 : ptr.toNat + 8 * (cells + 1) ≤ 4294967296)
    (hCell : cell < cells) :
    UInt32.ofNat ((ptr.toNat + (cell + 1) * 8) % 4294967296) =
      cellAddress ptr cell := by
  have hAddress : ptr.toNat + (cell + 1) * 8 < 4294967296 := by
    omega
  apply UInt32.toNat.inj
  rw [cellAddress_toNat hFit32 hCell]
  simp [Nat.mul_comm, Nat.mod_eq_of_lt hAddress]

private def writeCell (store : Store Unit) (ptr : UInt64) (cell : Nat)
    (value : UInt64) : Store Unit :=
  { store with mem := store.mem.write64 (cellAddress ptr cell) value }

@[simp]
private theorem writeCell_pages (store : Store Unit) (ptr : UInt64)
    (cell : Nat) (value : UInt64) :
    (writeCell store ptr cell value).mem.pages = store.mem.pages := by
  simp [writeCell, Mem.write64_pages]

private theorem cellRead_writeCell_same (store : Store Unit) (ptr : UInt64)
    (cell : Nat) (value : UInt64) :
    cellRead (writeCell store ptr cell value) ptr cell = value := by
  exact Mem.read64_write64_same ..

private theorem cellRead_writeCell_ne {store : Store Unit} {ptr : UInt64}
    {cells readCellIndex writeCellIndex : Nat} {value : UInt64}
    (hFit32 : ptr.toNat + 8 * (cells + 1) ≤ 4294967296)
    (hRead : readCellIndex < cells) (hWrite : writeCellIndex < cells)
    (hNe : readCellIndex ≠ writeCellIndex) :
    cellRead (writeCell store ptr writeCellIndex value) ptr readCellIndex =
      cellRead store ptr readCellIndex := by
  apply Project.ProofKit.Memory.read64_write64_disjoint
  rw [cellAddress_toNat hFit32 hRead,
    cellAddress_toNat hFit32 hWrite]
  omega

private theorem cellRead_writeCell_disjoint
    {store : Store Unit} {sourcePtr targetPtr : UInt64}
    {sourceCells targetCells sourceCell targetCell : Nat} {value : UInt64}
    (hSourceFit32 :
      sourcePtr.toNat + 8 * (sourceCells + 1) ≤ 4294967296)
    (hTargetFit32 :
      targetPtr.toNat + 8 * (targetCells + 1) ≤ 4294967296)
    (hSourceCell : sourceCell < sourceCells)
    (hTargetCell : targetCell < targetCells)
    (hDisjoint :
      sourcePtr.toNat + 8 * (sourceCells + 1) ≤ targetPtr.toNat ∨
      targetPtr.toNat + 8 * (targetCells + 1) ≤ sourcePtr.toNat) :
    cellRead (writeCell store targetPtr targetCell value) sourcePtr sourceCell =
      cellRead store sourcePtr sourceCell := by
  apply Project.ProofKit.Memory.read64_write64_disjoint
  rcases hDisjoint with hBefore | hAfter
  · left
    rw [cellAddress_toNat hSourceFit32 hSourceCell,
      cellAddress_toNat hTargetFit32 hTargetCell]
    omega
  · right
    rw [cellAddress_toNat hSourceFit32 hSourceCell,
      cellAddress_toNat hTargetFit32 hTargetCell]
    omega

private theorem headerRead_writeCell {store : Store Unit} {ptr : UInt64}
    {cells cell : Nat} {value : UInt64}
    (hFit32 : ptr.toNat + 8 * (cells + 1) ≤ 4294967296)
    (hCell : cell < cells) :
    (writeCell store ptr cell value).mem.read64 ptr.toUInt32 =
      store.mem.read64 ptr.toUInt32 := by
  apply Project.ProofKit.Memory.read64_write64_disjoint
  left
  rw [Project.ProofKit.Memory.toUInt32_toNat,
    Nat.mod_eq_of_lt (by omega), cellAddress_toNat hFit32 hCell]
  omega

private theorem ofNat_add_one {value : Nat}
    (hValue : value + 1 < UInt64.size) :
    UInt64.ofNat value + 1 = UInt64.ofNat (value + 1) := by
  apply UInt64.toNat.inj
  rw [UInt64.toNat_add,
    UInt64.toNat_ofNat_of_lt' (lt_trans (Nat.lt_succ_self value) hValue)]
  have hOne : (1 : UInt64).toNat = 1 := rfl
  rw [hOne, UInt64.toNat_ofNat_of_lt' hValue, Nat.mod_eq_of_lt hValue]

private theorem runtimeCellAddress_eq {ptr : UInt64} {cells cell : Nat}
    (hFit32 : ptr.toNat + 8 * (cells + 1) ≤ 4294967296)
    (hCell : cell < cells) :
    UInt32.ofNat
        ((ptr + (UInt64.ofNat cell + 1) * 8).toNat % (2 ^ 32)) =
      cellAddress ptr cell := by
  have hCellSucc : cell + 1 < UInt64.size := by
    have hSize : UInt64.size = 18446744073709551616 := rfl
    omega
  have hOffset : (UInt64.ofNat cell + 1) * 8 =
      UInt64.ofNat (8 * (cell + 1)) := by
    rw [ofNat_add_one hCellSucc]
    apply UInt64.toNat.inj
    rw [UInt64.toNat_mul, UInt64.toNat_ofNat_of_lt' hCellSucc]
    have hEight : (8 : UInt64).toNat = 8 := rfl
    rw [hEight, UInt64.toNat_ofNat_of_lt' (by
      have hSize : UInt64.size = 18446744073709551616 := rfl
      omega), Nat.mod_eq_of_lt (by
      have hSize : UInt64.size = 18446744073709551616 := rfl
      omega)]
    omega
  rw [hOffset]
  unfold cellAddress UInt64Array.wordAddress
  simpa using (Project.ProofKit.Memory.toUInt32_eq_ofNat
    (ptr + UInt64.ofNat (8 * (cell + 1)))).symm

private theorem ofNat_add {left right : Nat}
    (hSum : left + right < UInt64.size) :
    UInt64.ofNat left + UInt64.ofNat right = UInt64.ofNat (left + right) := by
  apply UInt64.toNat.inj
  rw [UInt64.toNat_add,
    UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt (Nat.le_add_right left right)
      hSum),
    UInt64.toNat_ofNat_of_lt' (lt_of_le_of_lt (Nat.le_add_left right left)
      hSum),
    UInt64.toNat_ofNat_of_lt' hSum, Nat.mod_eq_of_lt hSum]

private def prefixInvariant (initial : Store Unit) (frame : Locals)
    (counterLocal : Nat) (hCounter : frame.validIndex counterLocal)
    (sourcePtr targetPtr : UInt64) (sourceCells prefixCells : Nat) :
    AssertionF Unit :=
  fun current currentFrame =>
    ∃ counter : Nat, counter ≤ prefixCells ∧
      currentFrame = counterFrame frame counterLocal counter hCounter ∧
      current.mem.pages = initial.mem.pages ∧
      current.mem.read64 targetPtr.toUInt32 =
        initial.mem.read64 targetPtr.toUInt32 ∧
      (∀ cell : Nat, cell < sourceCells →
        cellRead current sourcePtr cell = cellRead initial sourcePtr cell) ∧
      ∀ cell : Nat, cell < counter →
        cellRead current targetPtr cell = cellRead initial sourcePtr cell

private def prefixMeasure (counterLocal prefixCells : Nat)
    (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get counterLocal with
  | some (.i64 counter) => prefixCells - counter.toNat
  | _ => 0

private theorem prefixMeasure_counterFrame (frame : Locals)
    (counterLocal prefixCells counter : Nat) (store : Store Unit)
    (hCounter : frame.validIndex counterLocal) :
    prefixMeasure counterLocal prefixCells store
        (counterFrame frame counterLocal counter hCounter) =
      prefixCells - (UInt64.ofNat counter).toNat := by
  unfold prefixMeasure
  rw [counterFrame_get_counter]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1048576 in
set_option Elab.async false in
theorem prefixProgram_spec
    (sourceLocal targetLocal prefixLocal counterLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (sourcePtr targetPtr : UInt64)
    (sourceCells targetCells prefixCells : Nat)
    (hCounter : frame.validIndex counterLocal)
    (hCounterSource : sourceLocal ≠ counterLocal)
    (hCounterTarget : targetLocal ≠ counterLocal)
    (hCounterPrefix : prefixLocal ≠ counterLocal)
    (hValues : frame.values = [])
    (hSourceLocal : frame.get sourceLocal = some (.i64 sourcePtr))
    (hTargetLocal : frame.get targetLocal = some (.i64 targetPtr))
    (hPrefixLocal : frame.get prefixLocal =
      some (.i64 (UInt64.ofNat prefixCells)))
    (hPrefixSource : prefixCells ≤ sourceCells)
    (hPrefixTarget : prefixCells ≤ targetCells)
    (hSourceFit32 :
      sourcePtr.toNat + 8 * (sourceCells + 1) ≤ 4294967296)
    (hTargetFit32 :
      targetPtr.toNat + 8 * (targetCells + 1) ≤ 4294967296)
    (hSourceFitMemory :
      sourcePtr.toNat + 8 * (sourceCells + 1) ≤
        initial.mem.pages * 65536)
    (hTargetFitMemory :
      targetPtr.toNat + 8 * (targetCells + 1) ≤
        initial.mem.pages * 65536)
    (hDisjoint :
      sourcePtr.toNat + 8 * (sourceCells + 1) ≤ targetPtr.toNat ∨
      targetPtr.toNat + 8 * (targetCells + 1) ≤ sourcePtr.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final : Store Unit,
      final.mem.pages = initial.mem.pages →
      final.mem.read64 targetPtr.toUInt32 =
        initial.mem.read64 targetPtr.toUInt32 →
      (∀ cell : Nat, cell < sourceCells →
        cellRead final sourcePtr cell = cellRead initial sourcePtr cell) →
      (∀ cell : Nat, cell < prefixCells →
        cellRead final targetPtr cell = cellRead initial sourcePtr cell) →
      wp module_ rest Q final
        (counterFrame frame counterLocal prefixCells hCounter) env) :
    wp module_
      (prefixProgram sourceLocal targetLocal prefixLocal counterLocal ++ rest)
      Q initial frame env := by
  have hPrefix64 : prefixCells < UInt64.size := by
    have hSize : UInt64.size = 18446744073709551616 := rfl
    omega
  have hPrefixNat : (UInt64.ofNat prefixCells).toNat = prefixCells :=
    UInt64.toNat_ofNat_of_lt' hPrefix64
  simp only [prefixProgram, List.cons_append, List.nil_append]
  apply initializeCounter_spec hCounter hValues
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := prefixInvariant initial frame counterLocal hCounter sourcePtr
      targetPtr sourceCells prefixCells)
    (μ := prefixMeasure counterLocal prefixCells)
  · exact ⟨0, Nat.zero_le _, rfl, rfl, rfl, (fun _ _ => rfl), by omega⟩
  · rintro current currentFrame
      ⟨counter, hCounterLe, rfl, hPages, hHeader, hSource, hPrefix⟩
    have hCounter64 : counter < UInt64.size := lt_of_le_of_lt hCounterLe hPrefix64
    have hCounterNat : (UInt64.ofNat counter).toNat = counter :=
      UInt64.toNat_ofNat_of_lt' hCounter64
    have hCounterGet := counterFrame_get_counter frame counterLocal counter hCounter
    have hSourceGet :
        (counterFrame frame counterLocal counter hCounter).get sourceLocal =
          some (.i64 sourcePtr) :=
      (counterFrame_get_ne frame counterLocal counter sourceLocal hCounter
        hCounterSource).trans hSourceLocal
    have hTargetGet :
        (counterFrame frame counterLocal counter hCounter).get targetLocal =
          some (.i64 targetPtr) :=
      (counterFrame_get_ne frame counterLocal counter targetLocal hCounter
        hCounterTarget).trans hTargetLocal
    have hPrefixGet :
        (counterFrame frame counterLocal counter hCounter).get prefixLocal =
          some (.i64 (UInt64.ofNat prefixCells)) :=
      (counterFrame_get_ne frame counterLocal counter prefixLocal hCounter
        hCounterPrefix).trans hPrefixLocal
    simp only [prefixBody]
    simp only [wp_localGet_cons, withValues_get, hCounterGet, hPrefixGet,
      counterFrame_values, wp_geUI64_cons, wp_br_if_cons]
    by_cases hAtEnd : counter = prefixCells
    · have hGuard : UInt64.ofNat counter ≥ UInt64.ofNat prefixCells := by
        subst counter
        simp
      rw [if_pos hGuard]
      subst counter
      simp
      convert hDone current hPages hHeader hSource hPrefix using 1
      exact ofParts_eq _
        (counterFrame_values frame counterLocal prefixCells hCounter)
    · have hCounterLt : counter < prefixCells := by omega
      have hGuard : ¬UInt64.ofNat counter ≥ UInt64.ofNat prefixCells := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hCounterNat, hPrefixNat]
        omega
      rw [if_neg hGuard]
      have hSourceCell : counter < sourceCells := by omega
      have hTargetCell : counter < targetCells := by omega
      have hLoadBound :
          (cellAddress sourcePtr counter).toNat + 8 ≤
            current.mem.pages * 65536 := by
        rw [cellAddress_toNat hSourceFit32 hSourceCell]
        calc
          sourcePtr.toNat + 8 * (counter + 1) + 8 ≤
              sourcePtr.toNat + 8 * (sourceCells + 1) := by omega
          _ ≤ initial.mem.pages * 65536 := hSourceFitMemory
          _ = current.mem.pages * 65536 := by rw [hPages]
      have hStoreBound :
          (cellAddress targetPtr counter).toNat + 8 ≤
            current.mem.pages * 65536 := by
        rw [cellAddress_toNat hTargetFit32 hTargetCell, hPages]
        omega
      have hLoadRead :
          current.mem.read64 (cellAddress sourcePtr counter) =
            cellRead initial sourcePtr counter := by
        exact hSource counter hSourceCell
      have hCounterSucc : UInt64.ofNat counter + 1 =
          UInt64.ofNat (counter + 1) :=
        ofNat_add_one (by omega)
      simp only [wp_localGet_cons, withValues_get, hTargetGet, hCounterGet,
        hSourceGet, wp_constI64_cons, wp_addI64_cons,
        wp_mulI64_cons, wp_wrapI64_cons, wp_load64_cons, wp_store64_cons]
      rw [runtimeCellAddress_eq hSourceFit32 hSourceCell,
        runtimeCellAddress_eq hTargetFit32 hTargetCell]
      simp only [UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero]
      rw [if_neg (Nat.not_lt.mpr hLoadBound),
        if_neg (Nat.not_lt.mpr hStoreBound), hLoadRead, hCounterSucc]
      simp only [wp_localSet_cons,
        counterFrame_withValues_set?_counter, wp_br_cons,
        List.take_zero, List.drop_zero, List.nil_append]
      refine ⟨?_, ?_⟩
      · unfold prefixInvariant
        refine ⟨counter + 1, by omega, rfl, ?_, ?_, ?_, ?_⟩
        · exact writeCell_pages current targetPtr counter
            (cellRead initial sourcePtr counter) |>.trans hPages
        · exact (headerRead_writeCell hTargetFit32 hTargetCell).trans hHeader
        · intro cell hCell
          exact (cellRead_writeCell_disjoint hSourceFit32 hTargetFit32 hCell
            hTargetCell hDisjoint).trans (hSource cell hCell)
        · intro cell hCell
          by_cases hEq : cell = counter
          · subst cell
            exact cellRead_writeCell_same ..
          · exact (cellRead_writeCell_ne hTargetFit32 (by omega) hTargetCell
              hEq).trans (hPrefix cell (by omega))
      · rw [ofParts_eq _ (counterFrame_values frame counterLocal (counter + 1)
            hCounter), prefixMeasure_counterFrame, prefixMeasure_counterFrame,
          UInt64.toNat_ofNat_of_lt' (by omega : counter + 1 < UInt64.size),
          hCounterNat]
        omega

private def suffixInvariant (initial : Store Unit) (frame : Locals)
    (counterLocal : Nat) (hCounter : frame.validIndex counterLocal)
    (sourcePtr targetPtr : UInt64) (sourceCells prefixCells skipCells
      suffixCells : Nat) : AssertionF Unit :=
  fun current currentFrame =>
    ∃ counter : Nat, counter ≤ suffixCells ∧
      currentFrame = counterFrame frame counterLocal counter hCounter ∧
      current.mem.pages = initial.mem.pages ∧
      current.mem.read64 targetPtr.toUInt32 =
        initial.mem.read64 targetPtr.toUInt32 ∧
      (∀ cell : Nat, cell < sourceCells →
        cellRead current sourcePtr cell = cellRead initial sourcePtr cell) ∧
      (∀ cell : Nat, cell < prefixCells →
        cellRead current targetPtr cell = cellRead initial targetPtr cell) ∧
      ∀ cell : Nat, cell < counter →
        cellRead current targetPtr (prefixCells + cell) =
          cellRead initial sourcePtr (prefixCells + skipCells + cell)

private def suffixMeasure (counterLocal suffixCells : Nat)
    (_ : Store Unit) (frame : Locals) : Nat :=
  match frame.get counterLocal with
  | some (.i64 counter) => suffixCells - counter.toNat
  | _ => 0

private theorem suffixMeasure_counterFrame (frame : Locals)
    (counterLocal suffixCells counter : Nat) (store : Store Unit)
    (hCounter : frame.validIndex counterLocal) :
    suffixMeasure counterLocal suffixCells store
        (counterFrame frame counterLocal counter hCounter) =
      suffixCells - (UInt64.ofNat counter).toNat := by
  unfold suffixMeasure
  rw [counterFrame_get_counter]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1048576 in
set_option Elab.async false in
theorem suffixProgram_spec
    (skipCells sourceLocal targetLocal prefixLocal suffixLocal
      counterLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (sourcePtr targetPtr : UInt64)
    (sourceCells targetCells prefixCells suffixCells : Nat)
    (hCounter : frame.validIndex counterLocal)
    (hCounterSource : sourceLocal ≠ counterLocal)
    (hCounterTarget : targetLocal ≠ counterLocal)
    (hCounterPrefix : prefixLocal ≠ counterLocal)
    (hCounterSuffix : suffixLocal ≠ counterLocal)
    (hValues : frame.values = [])
    (hSourceLocal : frame.get sourceLocal = some (.i64 sourcePtr))
    (hTargetLocal : frame.get targetLocal = some (.i64 targetPtr))
    (hPrefixLocal : frame.get prefixLocal =
      some (.i64 (UInt64.ofNat prefixCells)))
    (hSuffixLocal : frame.get suffixLocal =
      some (.i64 (UInt64.ofNat suffixCells)))
    (hSourceRange : prefixCells + skipCells + suffixCells ≤ sourceCells)
    (hTargetRange : prefixCells + suffixCells ≤ targetCells)
    (hSourceFit32 :
      sourcePtr.toNat + 8 * (sourceCells + 1) ≤ 4294967296)
    (hTargetFit32 :
      targetPtr.toNat + 8 * (targetCells + 1) ≤ 4294967296)
    (hSourceFitMemory :
      sourcePtr.toNat + 8 * (sourceCells + 1) ≤
        initial.mem.pages * 65536)
    (hTargetFitMemory :
      targetPtr.toNat + 8 * (targetCells + 1) ≤
        initial.mem.pages * 65536)
    (hDisjoint :
      sourcePtr.toNat + 8 * (sourceCells + 1) ≤ targetPtr.toNat ∨
      targetPtr.toNat + 8 * (targetCells + 1) ≤ sourcePtr.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final : Store Unit,
      final.mem.pages = initial.mem.pages →
      final.mem.read64 targetPtr.toUInt32 =
        initial.mem.read64 targetPtr.toUInt32 →
      (∀ cell : Nat, cell < sourceCells →
        cellRead final sourcePtr cell = cellRead initial sourcePtr cell) →
      (∀ cell : Nat, cell < prefixCells →
        cellRead final targetPtr cell = cellRead initial targetPtr cell) →
      (∀ cell : Nat, cell < suffixCells →
        cellRead final targetPtr (prefixCells + cell) =
          cellRead initial sourcePtr (prefixCells + skipCells + cell)) →
      wp module_ rest Q final
        (counterFrame frame counterLocal suffixCells hCounter) env) :
    wp module_
      (suffixProgram skipCells sourceLocal targetLocal prefixLocal suffixLocal
        counterLocal ++ rest)
      Q initial frame env := by
  have hSuffix64 : suffixCells < UInt64.size := by
    have hSize : UInt64.size = 18446744073709551616 := rfl
    omega
  have hSuffixNat : (UInt64.ofNat suffixCells).toNat = suffixCells :=
    UInt64.toNat_ofNat_of_lt' hSuffix64
  simp only [suffixProgram, List.cons_append, List.nil_append]
  apply initializeCounter_spec hCounter hValues
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := suffixInvariant initial frame counterLocal hCounter sourcePtr
      targetPtr sourceCells prefixCells skipCells suffixCells)
    (μ := suffixMeasure counterLocal suffixCells)
  · exact ⟨0, Nat.zero_le _, rfl, rfl, rfl, (fun _ _ => rfl),
      (fun _ _ => rfl), by omega⟩
  · rintro current currentFrame
      ⟨counter, hCounterLe, rfl, hPages, hHeader, hSource, hPrefix,
        hSuffix⟩
    have hCounter64 : counter < UInt64.size :=
      lt_of_le_of_lt hCounterLe hSuffix64
    have hCounterNat : (UInt64.ofNat counter).toNat = counter :=
      UInt64.toNat_ofNat_of_lt' hCounter64
    have hCounterGet := counterFrame_get_counter frame counterLocal counter hCounter
    have hSourceGet :
        (counterFrame frame counterLocal counter hCounter).get sourceLocal =
          some (.i64 sourcePtr) :=
      (counterFrame_get_ne frame counterLocal counter sourceLocal hCounter
        hCounterSource).trans hSourceLocal
    have hTargetGet :
        (counterFrame frame counterLocal counter hCounter).get targetLocal =
          some (.i64 targetPtr) :=
      (counterFrame_get_ne frame counterLocal counter targetLocal hCounter
        hCounterTarget).trans hTargetLocal
    have hPrefixGet :
        (counterFrame frame counterLocal counter hCounter).get prefixLocal =
          some (.i64 (UInt64.ofNat prefixCells)) :=
      (counterFrame_get_ne frame counterLocal counter prefixLocal hCounter
        hCounterPrefix).trans hPrefixLocal
    have hSuffixGet :
        (counterFrame frame counterLocal counter hCounter).get suffixLocal =
          some (.i64 (UInt64.ofNat suffixCells)) :=
      (counterFrame_get_ne frame counterLocal counter suffixLocal hCounter
        hCounterSuffix).trans hSuffixLocal
    simp only [suffixBody]
    simp only [wp_localGet_cons, withValues_get, hCounterGet, hSuffixGet,
      counterFrame_values, wp_geUI64_cons, wp_br_if_cons]
    by_cases hAtEnd : counter = suffixCells
    · have hGuard : UInt64.ofNat counter ≥ UInt64.ofNat suffixCells := by
        subst counter
        simp
      rw [if_pos hGuard]
      subst counter
      simp
      convert hDone current hPages hHeader hSource hPrefix hSuffix using 1
      exact ofParts_eq _
        (counterFrame_values frame counterLocal suffixCells hCounter)
    · have hCounterLt : counter < suffixCells := by omega
      have hGuard : ¬UInt64.ofNat counter ≥ UInt64.ofNat suffixCells := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hCounterNat, hSuffixNat]
        omega
      rw [if_neg hGuard]
      have hSourceCell : prefixCells + skipCells + counter < sourceCells := by
        omega
      have hTargetCell : prefixCells + counter < targetCells := by omega
      have hTargetSum :
          UInt64.ofNat prefixCells + UInt64.ofNat counter =
            UInt64.ofNat (prefixCells + counter) :=
        ofNat_add (by
          have hSize : UInt64.size = 18446744073709551616 := rfl
          omega)
      have hSourcePrefixSkip :
          UInt64.ofNat prefixCells + UInt64.ofNat skipCells =
            UInt64.ofNat (prefixCells + skipCells) :=
        ofNat_add (by
          have hSize : UInt64.size = 18446744073709551616 := rfl
          omega)
      have hSourceSum :
          UInt64.ofNat (prefixCells + skipCells) + UInt64.ofNat counter =
            UInt64.ofNat (prefixCells + skipCells + counter) :=
        ofNat_add (by
          have hSize : UInt64.size = 18446744073709551616 := rfl
          omega)
      have hLoadBound :
          (cellAddress sourcePtr (prefixCells + skipCells + counter)).toNat +
              8 ≤ current.mem.pages * 65536 := by
        rw [cellAddress_toNat hSourceFit32 hSourceCell]
        calc
          sourcePtr.toNat + 8 * (prefixCells + skipCells + counter + 1) + 8 ≤
              sourcePtr.toNat + 8 * (sourceCells + 1) := by omega
          _ ≤ initial.mem.pages * 65536 := hSourceFitMemory
          _ = current.mem.pages * 65536 := by rw [hPages]
      have hStoreBound :
          (cellAddress targetPtr (prefixCells + counter)).toNat + 8 ≤
            current.mem.pages * 65536 := by
        rw [cellAddress_toNat hTargetFit32 hTargetCell, hPages]
        omega
      have hLoadRead :
          current.mem.read64
              (cellAddress sourcePtr (prefixCells + skipCells + counter)) =
            cellRead initial sourcePtr
              (prefixCells + skipCells + counter) := by
        exact hSource _ hSourceCell
      have hCounterSucc : UInt64.ofNat counter + 1 =
          UInt64.ofNat (counter + 1) :=
        ofNat_add_one (by omega)
      simp only [wp_localGet_cons, withValues_get, hTargetGet, hPrefixGet,
        hCounterGet, hSourceGet, wp_addI64_cons, wp_constI64_cons,
        wp_mulI64_cons, wp_wrapI64_cons, wp_load64_cons, wp_store64_cons]
      rw [hTargetSum, hSourcePrefixSkip, hSourceSum,
        runtimeCellAddress_eq hSourceFit32 hSourceCell,
        runtimeCellAddress_eq hTargetFit32 hTargetCell]
      simp only [UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero]
      rw [if_neg (Nat.not_lt.mpr hLoadBound),
        if_neg (Nat.not_lt.mpr hStoreBound), hLoadRead, hCounterSucc]
      simp only [wp_localSet_cons,
        counterFrame_withValues_set?_counter, wp_br_cons,
        List.take_zero, List.drop_zero, List.nil_append]
      refine ⟨?_, ?_⟩
      · unfold suffixInvariant
        refine ⟨counter + 1, by omega, rfl, ?_, ?_, ?_, ?_, ?_⟩
        · exact writeCell_pages current targetPtr (prefixCells + counter)
            (cellRead initial sourcePtr
              (prefixCells + skipCells + counter)) |>.trans hPages
        · exact (headerRead_writeCell hTargetFit32 hTargetCell).trans hHeader
        · intro cell hCell
          exact (cellRead_writeCell_disjoint hSourceFit32 hTargetFit32 hCell
            hTargetCell hDisjoint).trans (hSource cell hCell)
        · intro cell hCell
          exact (cellRead_writeCell_ne hTargetFit32 (by omega) hTargetCell
            (by omega)).trans (hPrefix cell hCell)
        · intro cell hCell
          by_cases hEq : cell = counter
          · subst cell
            exact cellRead_writeCell_same ..
          · exact (cellRead_writeCell_ne hTargetFit32 (by omega) hTargetCell
              (by omega)).trans (hSuffix cell (by omega))
      · rw [ofParts_eq _ (counterFrame_values frame counterLocal (counter + 1)
            hCounter), suffixMeasure_counterFrame, suffixMeasure_counterFrame,
          UInt64.toNat_ofNat_of_lt' (by omega : counter + 1 < UInt64.size),
          hCounterNat]
        omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1048576 in
set_option Elab.async false in
theorem program_spec
    (skipCells sourceLocal targetLocal prefixLocal suffixLocal
      counterLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (sourcePtr targetPtr : UInt64)
    (sourceCells targetCells prefixCells suffixCells : Nat)
    (hCounter : frame.validIndex counterLocal)
    (hCounterSource : sourceLocal ≠ counterLocal)
    (hCounterTarget : targetLocal ≠ counterLocal)
    (hCounterPrefix : prefixLocal ≠ counterLocal)
    (hCounterSuffix : suffixLocal ≠ counterLocal)
    (hValues : frame.values = [])
    (hSourceLocal : frame.get sourceLocal = some (.i64 sourcePtr))
    (hTargetLocal : frame.get targetLocal = some (.i64 targetPtr))
    (hPrefixLocal : frame.get prefixLocal =
      some (.i64 (UInt64.ofNat prefixCells)))
    (hSuffixLocal : frame.get suffixLocal =
      some (.i64 (UInt64.ofNat suffixCells)))
    (hSourceRange : prefixCells + skipCells + suffixCells ≤ sourceCells)
    (hTargetRange : prefixCells + suffixCells ≤ targetCells)
    (hSourceFit32 :
      sourcePtr.toNat + 8 * (sourceCells + 1) ≤ 4294967296)
    (hTargetFit32 :
      targetPtr.toNat + 8 * (targetCells + 1) ≤ 4294967296)
    (hSourceFitMemory :
      sourcePtr.toNat + 8 * (sourceCells + 1) ≤
        initial.mem.pages * 65536)
    (hTargetFitMemory :
      targetPtr.toNat + 8 * (targetCells + 1) ≤
        initial.mem.pages * 65536)
    (hDisjoint :
      sourcePtr.toNat + 8 * (sourceCells + 1) ≤ targetPtr.toNat ∨
      targetPtr.toNat + 8 * (targetCells + 1) ≤ sourcePtr.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final : Store Unit,
      final.mem.pages = initial.mem.pages →
      final.mem.read64 targetPtr.toUInt32 =
        initial.mem.read64 targetPtr.toUInt32 →
      (∀ cell : Nat, cell < sourceCells →
        cellRead final sourcePtr cell = cellRead initial sourcePtr cell) →
      (∀ cell : Nat, cell < prefixCells →
        cellRead final targetPtr cell = cellRead initial sourcePtr cell) →
      (∀ cell : Nat, cell < suffixCells →
        cellRead final targetPtr (prefixCells + cell) =
          cellRead initial sourcePtr (prefixCells + skipCells + cell)) →
      wp module_ rest Q final
        (counterFrame frame counterLocal suffixCells hCounter) env) :
    wp module_
      (program skipCells sourceLocal targetLocal prefixLocal suffixLocal
        counterLocal ++ rest)
      Q initial frame env := by
  rw [program, List.append_assoc]
  refine prefixProgram_spec
    (sourceLocal := sourceLocal) (targetLocal := targetLocal)
    (prefixLocal := prefixLocal) (counterLocal := counterLocal)
    (module_ := module_) (env := env) (initial := initial) (frame := frame)
    (sourcePtr := sourcePtr) (targetPtr := targetPtr)
    (sourceCells := sourceCells) (targetCells := targetCells)
    (prefixCells := prefixCells) (hCounter := hCounter)
    (hCounterSource := hCounterSource) (hCounterTarget := hCounterTarget)
    (hCounterPrefix := hCounterPrefix) (hValues := hValues)
    (hSourceLocal := hSourceLocal) (hTargetLocal := hTargetLocal)
    (hPrefixLocal := hPrefixLocal) (hPrefixSource := by omega)
    (hPrefixTarget := by omega) (hSourceFit32 := hSourceFit32)
    (hTargetFit32 := hTargetFit32)
    (hSourceFitMemory := hSourceFitMemory)
    (hTargetFitMemory := hTargetFitMemory) (hDisjoint := hDisjoint)
    (Q := Q)
    (rest := suffixProgram skipCells sourceLocal targetLocal prefixLocal
      suffixLocal counterLocal ++ rest) ?_
  intro middle hMiddlePages hMiddleHeader hMiddleSource hMiddlePrefix
  have hMiddleCounter :
      (counterFrame frame counterLocal prefixCells hCounter).validIndex
        counterLocal :=
    (counterFrame_validIndex frame counterLocal prefixCells counterLocal
      hCounter).2 hCounter
  refine suffixProgram_spec
    (skipCells := skipCells) (sourceLocal := sourceLocal)
    (targetLocal := targetLocal) (prefixLocal := prefixLocal)
    (suffixLocal := suffixLocal) (counterLocal := counterLocal)
    (module_ := module_) (env := env) (initial := middle)
    (frame := counterFrame frame counterLocal prefixCells hCounter)
    (sourcePtr := sourcePtr) (targetPtr := targetPtr)
    (sourceCells := sourceCells) (targetCells := targetCells)
    (prefixCells := prefixCells) (suffixCells := suffixCells)
    (hCounter := hMiddleCounter) (hCounterSource := hCounterSource)
    (hCounterTarget := hCounterTarget) (hCounterPrefix := hCounterPrefix)
    (hCounterSuffix := hCounterSuffix)
    (hValues := counterFrame_values frame counterLocal prefixCells hCounter)
    (hSourceLocal := (counterFrame_get_ne frame counterLocal prefixCells
      sourceLocal hCounter hCounterSource).trans hSourceLocal)
    (hTargetLocal := (counterFrame_get_ne frame counterLocal prefixCells
      targetLocal hCounter hCounterTarget).trans hTargetLocal)
    (hPrefixLocal := (counterFrame_get_ne frame counterLocal prefixCells
      prefixLocal hCounter hCounterPrefix).trans hPrefixLocal)
    (hSuffixLocal := (counterFrame_get_ne frame counterLocal prefixCells
      suffixLocal hCounter hCounterSuffix).trans hSuffixLocal)
    (hSourceRange := hSourceRange) (hTargetRange := hTargetRange)
    (hSourceFit32 := hSourceFit32) (hTargetFit32 := hTargetFit32)
    (hSourceFitMemory := by rw [hMiddlePages]; exact hSourceFitMemory)
    (hTargetFitMemory := by rw [hMiddlePages]; exact hTargetFitMemory)
    (hDisjoint := hDisjoint) (Q := Q) (rest := rest) ?_
  intro final hFinalPages hFinalHeader hFinalSource hFinalPrefix hFinalSuffix
  have hPages : final.mem.pages = initial.mem.pages :=
    hFinalPages.trans hMiddlePages
  have hHeader : final.mem.read64 targetPtr.toUInt32 =
      initial.mem.read64 targetPtr.toUInt32 :=
    hFinalHeader.trans hMiddleHeader
  have hSource : ∀ cell : Nat, cell < sourceCells →
      cellRead final sourcePtr cell = cellRead initial sourcePtr cell := by
    intro cell hCell
    exact (hFinalSource cell hCell).trans (hMiddleSource cell hCell)
  have hPrefix : ∀ cell : Nat, cell < prefixCells →
      cellRead final targetPtr cell = cellRead initial sourcePtr cell := by
    intro cell hCell
    exact (hFinalPrefix cell hCell).trans (hMiddlePrefix cell hCell)
  have hSuffix : ∀ cell : Nat, cell < suffixCells →
      cellRead final targetPtr (prefixCells + cell) =
        cellRead initial sourcePtr (prefixCells + skipCells + cell) := by
    intro cell hCell
    exact (hFinalSuffix cell hCell).trans
      (hMiddleSource (prefixCells + skipCells + cell) (by omega))
  have hResult := hDone final hPages hHeader hSource hPrefix hSuffix
  rw [counterFrame_counterFrame frame counterLocal prefixCells suffixCells
    hCounter hMiddleCounter]
  exact hResult

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 1048576 in
set_option Elab.async false in
theorem eraseIdxProgram_spec
    (sourceLocal targetLocal prefixLocal suffixLocal counterLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (frame : Locals) (sourcePtr targetPtr : UInt64)
    (input : Array UInt64) (erase : Nat)
    (hErase : erase < input.size)
    (hSource : UInt64Array.At initial sourcePtr input)
    (hCounter : frame.validIndex counterLocal)
    (hCounterSource : sourceLocal ≠ counterLocal)
    (hCounterTarget : targetLocal ≠ counterLocal)
    (hCounterPrefix : prefixLocal ≠ counterLocal)
    (hCounterSuffix : suffixLocal ≠ counterLocal)
    (hValues : frame.values = [])
    (hSourceLocal : frame.get sourceLocal = some (.i64 sourcePtr))
    (hTargetLocal : frame.get targetLocal = some (.i64 targetPtr))
    (hPrefixLocal : frame.get prefixLocal =
      some (.i64 (UInt64.ofNat erase)))
    (hSuffixLocal : frame.get suffixLocal =
      some (.i64 (UInt64.ofNat (input.size - 1 - erase))))
    (hTargetFit32 :
      targetPtr.toNat + 8 * ((input.size - 1) + 1) ≤ 4294967296)
    (hTargetFitMemory :
      targetPtr.toNat + 8 * ((input.size - 1) + 1) ≤
        initial.mem.pages * 65536)
    (hTargetLength : initial.mem.read64 targetPtr.toUInt32 =
      UInt64.ofNat (input.size - 1))
    (hBefore :
      sourcePtr.toNat + 8 * (input.size + 1) ≤ targetPtr.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : ∀ final : Store Unit,
      UInt64Array.At final targetPtr (input.eraseIdx! erase) →
      wp module_ rest Q final
        (counterFrame frame counterLocal (input.size - 1 - erase) hCounter)
        env) :
    wp module_
      (program 1 sourceLocal targetLocal prefixLocal suffixLocal counterLocal ++
        rest)
      Q initial frame env := by
  refine program_spec
    (skipCells := 1) (sourceLocal := sourceLocal) (targetLocal := targetLocal)
    (prefixLocal := prefixLocal) (suffixLocal := suffixLocal)
    (counterLocal := counterLocal) (module_ := module_) (env := env)
    (initial := initial) (frame := frame) (sourcePtr := sourcePtr)
    (targetPtr := targetPtr) (sourceCells := input.size)
    (targetCells := input.size - 1) (prefixCells := erase)
    (suffixCells := input.size - 1 - erase) (hCounter := hCounter)
    (hCounterSource := hCounterSource) (hCounterTarget := hCounterTarget)
    (hCounterPrefix := hCounterPrefix) (hCounterSuffix := hCounterSuffix)
    (hValues := hValues) (hSourceLocal := hSourceLocal)
    (hTargetLocal := hTargetLocal) (hPrefixLocal := hPrefixLocal)
    (hSuffixLocal := hSuffixLocal) (hSourceRange := by omega)
    (hTargetRange := by omega) (hSourceFit32 := hSource.1)
    (hTargetFit32 := hTargetFit32) (hSourceFitMemory := hSource.2.1)
    (hTargetFitMemory := hTargetFitMemory) (hDisjoint := Or.inl hBefore)
    (Q := Q) (rest := rest) ?_
  intro final hPages hHeader _ hPrefix hSuffix
  apply hDone final
  apply UInt64Array.At.eraseIdx!_of_reads hErase hSource hTargetFit32
    (by rw [hPages]; exact hTargetFitMemory)
    (hHeader.trans hTargetLength)
  · intro cell hCell
    simpa [cellRead, cellAddress, UInt64Array.wordAddress] using
      hPrefix cell hCell
  · intro cell hCellLower hCellUpper
    have hOffset : cell - erase < input.size - 1 - erase := by omega
    have hTargetIndex : erase + (cell - erase) = cell := by omega
    have hSourceIndex : erase + 1 + (cell - erase) = cell + 1 := by omega
    simpa [cellRead, cellAddress, UInt64Array.wordAddress, hTargetIndex,
      hSourceIndex, Nat.add_assoc] using hSuffix (cell - erase) hOffset

end Project.ProofKit.FixedArrayCopy
