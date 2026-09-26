import Project.ClobLimit.HeapAppend

/-! Complete residual limit branch with reusable allocation. -/
namespace Project.ClobLimit.LimitResidual
open Wasm Project.Common Project.Clob Project.ClobLimit
open Project.ClobMatchFuel.LoopInvariant Project.ClobMatchFuel.Allocation
open Project.ClobMatchFuel.AllocatorFrame Project.ClobPostOnly.Model

def ExportedResultAt (final : Store Unit) (ctx : Context)
    (data : HeapRunMatch.OutputData) (order : OrderL) : Prop :=
  ∃ matched, HeapRunMatch.OutputAt ctx matched data ∧
    HeapAppendOutcome.At matched final ctx data.toOutputData order

def ResidualSpec : Prop :=
  forall (env : HostEnv Unit) (st : Store Unit)
    (book bookCapacity g0 g2 g4 g5 : UInt64)
    (os : List OrderL) (order : OrderL) (limit : Nat),
    os.length < 4294967296 ->
    48 <= book.toNat ->
    book.toNat + fixedArrayBytes os.length 5 < 4294967296 ->
    fixedArrayBytes os.length 5 <= bookCapacity.toNat ->
    book.toNat + bookCapacity.toNat <= g0.toNat ->
    OwnedOrderArrayAt st book bookCapacity os ->
    g0.toNat + 112 < 4294967296 ->
    g0.toNat + 112 <= st.mem.pages * 65536 ->
    st.mem.pages <= 65536 ->
    st.globals.globals[0]? = some (.i64 g0) ->
    st.globals.globals[1]? = some (.i64 0) ->
    st.globals.globals[2]? = some (.i64 g2) ->
    st.globals.globals[4]? = some (.i64 g4) ->
    st.globals.globals[5]? = some (.i64 g5) ->
    limit < 4294967296 ->
    limit <= st.mem.pages * 65536 ->
    g0.toNat + 112 + (os.length + 1) *
      Project.ClobMatchFuel.Budget.stepBytes os.length (os.length + 1) <=
        limit ->
    limit + 48 + orderArrayBytes
      ((Model.runMatchL os order).book.length + 1) < 4294967296 ->
    limit + 48 + orderArrayBytes
      ((Model.runMatchL os order).book.length + 1) <=
        st.mem.pages * 65536 ->
    validOrderL os order ->
    (Model.runMatchL os order).remaining ≠ 0 ->
    TerminatesWith (m := «module») (id := 21) (initial := st) (env := env)
      (LimitEntry.limitArgs book order)
      (fun st' values =>
        ∃ data,
          values = [.i64 data.trades, .i64 (HeapAppendOutcome.root
            (HeapRunMatch.runMatchContext st os order g0 g2 g4 g5 limit) data.toOutputData), .i64 0] ∧
          ExportedResultAt st'
            (HeapRunMatch.runMatchContext st os order g0 g2 g4 g5 limit) data order)

set_option maxRecDepth 1048576
set_option Elab.async false in
theorem func21_residual : ResidualSpec := by
  intro env st book bookCapacity g0 g2 g4 g5 os order limit hLength hBook48
    hBook32 hBookCapacity hBookBelow hBook hInitial32 hInitialFit hPages
    hg0 hg1 hg2 hg4 hg5 hAddressLimit hMemoryLimit hBudget hReserve32 hReserveFit
    hValid hRemaining
  let ctx := HeapRunMatch.runMatchContext st os order g0 g2 g4 g5 limit
  have hContextResult : ctx.result = Model.runMatchL os order :=
    HeapRunMatch.runMatchContext_result st os order g0 g2 g4 g5 limit hLength
  have hContextRemaining : ctx.result.remaining ≠ 0 := by rwa [hContextResult]
  have hRunMatch := HeapRunMatch.func18_correct env st book bookCapacity g0 g2 g4 g5 os
    order limit hLength hBook48 hBook32 hBookCapacity hBookBelow hBook
    hInitial32 hInitialFit hPages hg0 hg1 hg2 hg4 hg5 hAddressLimit hMemoryLimit hBudget
  apply TerminatesWith.of_wp_entry_for (f := func21Def)
  · simp [«module»]
  · change wp «module» func21 _ st (LimitEntry.entryFrame book order) env
    rw [LimitEntry.func21_decomposition]
    apply LimitValidEntry.entryProg_valid_spec env st book os order hLength hBook.2 hValid
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    simp only [LimitEntry.validProg, LimitEntry.validPrefixProg, List.append_assoc]
    apply LimitRunMatchCall.validCallProg_spec env st book order (HeapRunMatch.Postcondition ctx) hRunMatch
    rintro matched values ⟨data, hValues, hOutput⟩
    apply LimitRunMatchResult.validResultPrefixProg_residual_spec env matched book order
      ctx data values hValues hContextRemaining
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    have geo := HeapResidualFacts.of_output hOutput hContextRemaining
    have hHeap : data.g0.toNat ≤ limit := geo.heapLimit
    have hMatchedPages : matched.mem.pages = st.mem.pages := hOutput.pages
    have hReserve32Ctx : limit + 48 + orderArrayBytes (ctx.result.book.length + 1) < 4294967296 := by
      simpa only [hContextResult] using hReserve32
    have hReserveFitCtx : limit + 48 + orderArrayBytes (ctx.result.book.length + 1) ≤ st.mem.pages * 65536 := by
      simpa only [hContextResult] using hReserveFit
    have hLengthResult : ctx.result.book.length + 1 < UInt64.size := by
      unfold orderArrayBytes fixedArrayBytes at hReserve32Ctx
      rw [size_eq]; omega
    rw [HeapAppendProgram.residual_decomposition]
    simp only [List.append_assoc]
    apply LimitResidualStatus.residualStatusProg_spec env matched book order ctx data
    apply LimitResidualPrepare.residualOrderPrepareProg_spec env matched book order ctx data hOutput hLengthResult
    intro prepared hPrepared
    apply HeapAppend.spec env matched prepared order ctx data hPrepared hOutput hContextRemaining
      (by omega) (by rw [hMatchedPages]; omega)
    intro final hResult frame hFrame
    simp only [wp_simp]
    have hFrameValues := hFrame.values
    have hEmpty : { frame with values := [] ++ [] } = frame := by
      cases frame
      simp_all
    rw [hEmpty, ← List.append_nil LimitEntry.resultProg]
    apply HeapAppendResult.export_spec env final frame
      (HeapAppendOutcome.root ctx data.toOutputData) data.trades hFrame
    simp only [wp_simp, func21Def]
    exact ⟨data, rfl, matched, hOutput, hResult⟩

#print axioms func21_residual
end Project.ClobLimit.LimitResidual
