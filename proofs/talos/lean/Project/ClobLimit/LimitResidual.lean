import Project.ClobLimit.LimitResidualBranch
import Project.ClobLimit.LimitResult
import Project.ClobLimit.LimitResidualExport

/-!
# Valid residual behavior of exported `limit`

The valid residual branch calls the complete matcher and appends its remaining
taker quantity to the returned book.  Its reserve premises cover the one final
stride-five allocation above the matcher's heap limit.
-/

namespace Project.ClobLimit.LimitResidual

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobMatchFuel.Allocation Project.ClobMatchFuel.AllocatorFrame
  Project.ClobPostOnly.Model

def ResidualSpec : Prop :=
  forall (env : HostEnv Unit) (st : Store Unit)
    (book bookCapacity g0 g2 : UInt64)
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
        exists data,
          values = [.i64 data.trades, .i64 (data.g0 + 48), .i64 0] /\
          LimitResidualExport.ExportedResultAt st st'
            (RunMatchCorrect.runMatchContext st os order g0 g2 limit)
            data order g0)

set_option Elab.async false in
theorem func21_residual : ResidualSpec := by
  intro env st book bookCapacity g0 g2 os order limit hLength hBook48
    hBook32 hBookCapacity hBookBelow hBook hInitial32 hInitialFit hPages
    hg0 hg1 hg2 hAddressLimit hMemoryLimit hBudget hReserve32 hReserveFit
    hValid hRemaining
  let ctx := RunMatchCorrect.runMatchContext st os order g0 g2 limit
  have hContextResult : ctx.result = Model.runMatchL os order := by
    exact RunMatchCorrect.runMatchContext_result st os order g0 g2 limit
      hLength
  have hContextRemaining : ctx.result.remaining ≠ 0 := by
    rw [hContextResult]
    exact hRemaining
  have hInitial := RunMatchAllocations.allocationsStore_facts st book
    bookCapacity g0 g2 os hInitial32 hInitialFit hBook48 hBook32
    hBookCapacity hBookBelow hBook hg0 hg1 hg2
  have hRunMatch : TerminatesWith (m := «module») (id := 18)
      (initial := st) (env := env)
      (RunMatchCorrect.runMatchArgs 0 book order)
      (InternalLoopResult.Postcondition ctx) := by
    apply RunMatchCorrect.func18_correct env st 0 book bookCapacity g0 g2 os
      order limit hLength hBook48 hBook32 hBookCapacity hBookBelow hBook
      hInitial32 hInitialFit hPages hg0 hg1 hg2 hAddressLimit hMemoryLimit
      hBudget
  apply TerminatesWith.of_wp_entry_for (f := func21Def)
  · simp [«module»]
  · change wp «module» func21 _ st (LimitEntry.entryFrame book order) env
    rw [LimitEntry.func21_decomposition]
    apply LimitValidEntry.entryProg_valid_spec env st book os order hLength
      hBook.2 hValid
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    simp only [LimitEntry.validProg, LimitEntry.validPrefixProg,
      List.append_assoc]
    apply LimitRunMatchCall.validCallProg_spec env st book order
      (InternalLoopResult.Postcondition ctx) hRunMatch
    rintro st2 values ⟨data, hValues, hOutput⟩
    apply LimitRunMatchResult.validResultPrefixProg_residual_spec env st2 book
      order ctx data values hValues hContextRemaining
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    have hReserve32Ctx : limit + 48 +
        orderArrayBytes (ctx.result.book.length + 1) < 4294967296 := by
      simpa only [hContextResult] using hReserve32
    have hReserveFitCtx : limit + 48 +
        orderArrayBytes (ctx.result.book.length + 1) <=
          st.mem.pages * 65536 := by
      simpa only [hContextResult] using hReserveFit
    have hLengthResult : ctx.result.book.length + 1 < UInt64.size := by
      have h := hReserve32Ctx
      unfold orderArrayBytes fixedArrayBytes at h
      rw [size_eq]
      omega
    have hBytesResult : orderArrayBytes (ctx.result.book.length + 1) + 7 <
        UInt64.size := by
      have h := hReserve32Ctx
      unfold orderArrayBytes fixedArrayBytes at h ⊢
      rw [size_eq]
      omega
    have hNeedNat :
        (orderArrayBytesU (ctx.result.book.length + 1)).toNat =
          orderArrayBytes (ctx.result.book.length + 1) :=
      fixedArrayBytesU_toNat (ctx.result.book.length + 1) 5 hLengthResult
        (by decide) (by
          unfold fixedArrayBytes
          rw [size_eq]
          have h := hReserve32Ctx
          unfold orderArrayBytes fixedArrayBytes at h
          omega)
    have hFit32 : data.g0.toNat + 48 +
        (orderArrayBytesU (ctx.result.book.length + 1)).toNat <
          4294967296 := by
      rw [hNeedNat]
      have hHeap := hOutput.heapLimit
      change data.g0.toNat <= limit at hHeap
      omega
    have hFit : data.g0.toNat + 48 +
        (orderArrayBytesU (ctx.result.book.length + 1)).toNat <=
          st2.mem.pages * 65536 := by
      rw [hNeedNat, hOutput.pages]
      change data.g0.toNat + 48 +
          orderArrayBytes (ctx.result.book.length + 1) <=
        st.mem.pages * 65536
      have hHeap := hOutput.heapLimit
      change data.g0.toNat <= limit at hHeap
      omega
    have hFit32Nat : data.g0.toNat + 48 +
        orderArrayBytes (ctx.result.book.length + 1) < 4294967296 := by
      simpa only [hNeedNat] using hFit32
    have hTop : (data.g0 + 48 +
        orderArrayBytesU (ctx.result.book.length + 1)).toNat =
          data.g0.toNat + 48 +
            (orderArrayBytesU (ctx.result.book.length + 1)).toNat :=
      by
        simpa only [hNeedNat] using
          (Project.ClobMatchFuel.Budget.allocationTop_toNat data.g0
            (orderArrayBytesU (ctx.result.book.length + 1))
            (orderArrayBytes (ctx.result.book.length + 1)) hNeedNat
            hFit32Nat)
    apply LimitResidualBranch.residualProg_spec env st2 book order ctx data
      hLengthResult hBytesResult hTop hFit32 hFit hOutput
    intro st3 hResult final hResultLocals
    simp only [wp_simp]
    have hFinalValues : final.values = [] := hResultLocals.values
    have hFinalFrame : { final with values := [] ++ [] } = final := by
      cases final
      simp_all
    rw [hFinalFrame, ← List.append_nil LimitEntry.resultProg]
    apply LimitResult.resultProg_spec env st3 final ctx data hResultLocals
    simp only [wp_simp, LimitResult.outputFrame, func21Def]
    exact ⟨data, rfl,
      LimitResidualExport.of_result st st2 st3 book bookCapacity g0 g2 os
        order limit data (by
          rw [UInt64.toNat_add]
          have h112 : (112 : UInt64).toNat = 112 := rfl
          rw [h112]
          omega)
        hInitial hOutput hResult⟩

end Project.ClobLimit.LimitResidual
