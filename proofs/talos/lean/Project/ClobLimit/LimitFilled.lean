import Project.ClobLimit.LimitEntry
import Project.ClobLimit.LimitValidEntry
import Project.ClobLimit.LimitRunMatchCall
import Project.ClobLimit.LimitRunMatchResult
import Project.ClobLimit.Allocation

/-!
# Filled branch of exported `limit`

The valid filled branch returns status zero and the two arrays produced by
function 18.  It performs no allocation after the matcher returns.
-/

namespace Project.ClobLimit.LimitFilled

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobMatchFuel.AllocatorFrame Project.ClobPostOnly.Model

set_option maxRecDepth 1048576

def FilledSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit)
    (book bookCapacity g0 g2 : UInt64)
    (os : List OrderL) (order : OrderL) (limit : Nat),
    os.length < 4294967296 →
    48 ≤ book.toNat →
    book.toNat + fixedArrayBytes os.length 5 < 4294967296 →
    fixedArrayBytes os.length 5 ≤ bookCapacity.toNat →
    book.toNat + bookCapacity.toNat ≤ g0.toNat →
    OwnedOrderArrayAt st book bookCapacity os →
    g0.toNat + 112 < 4294967296 →
    g0.toNat + 112 ≤ st.mem.pages * 65536 →
    st.mem.pages ≤ 65536 →
    st.globals.globals[0]? = some (.i64 g0) →
    st.globals.globals[1]? = some (.i64 0) →
    st.globals.globals[2]? = some (.i64 g2) →
    limit < 4294967296 →
    limit ≤ st.mem.pages * 65536 →
    g0.toNat + 112 + (os.length + 1) *
      Project.ClobMatchFuel.Budget.stepBytes os.length (os.length + 1) ≤
        limit →
    validOrderL os order →
    (Model.runMatchL os order).remaining = 0 →
    TerminatesWith (m := «module») (id := 21) (initial := st) (env := env)
      (LimitEntry.limitArgs book order)
      (fun st' values =>
        ∃ data,
          values = [.i64 data.trades, .i64 data.book, .i64 0] ∧
          InternalLoopResult.OutputAt
            (RunMatchCorrect.runMatchContext st os order g0 g2 limit)
            st' data)

set_option Elab.async false in
theorem func21_filled : FilledSpec := by
  intro env st book bookCapacity g0 g2 os order limit hLength hBook48
    hBook32 hBookCapacity hBookBelow hBook hFit32 hFit hPages hg0 hg1 hg2
    hAddressLimit hMemoryLimit hBudget hValid hRemaining
  let ctx := RunMatchCorrect.runMatchContext st os order g0 g2 limit
  have hContextResult : ctx.result = Model.runMatchL os order := by
    exact RunMatchCorrect.runMatchContext_result st os order g0 g2 limit
      hLength
  have hContextRemaining : ctx.result.remaining = 0 := by
    rw [hContextResult]
    exact hRemaining
  have hRunMatch : TerminatesWith (m := «module») (id := 18)
      (initial := st) (env := env)
      (RunMatchCorrect.runMatchArgs 0 book order)
      (InternalLoopResult.Postcondition ctx) := by
    apply RunMatchCorrect.func18_correct env st 0 book bookCapacity g0 g2 os
      order limit hLength hBook48 hBook32 hBookCapacity hBookBelow hBook
      hFit32 hFit hPages hg0 hg1 hg2 hAddressLimit hMemoryLimit hBudget
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
    apply LimitRunMatchResult.validResultPrefixProg_filled_spec env st2 book
      order ctx data values hValues hContextRemaining
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    simp only [LimitEntry.filledProg, List.nil_append]
    wp_run
    refine wp_call_tw (Allocation.func19_spec env st2) ?_
    rintro st3 values ⟨rfl, rfl⟩
    simp only [LimitEntry.resultProg]
    wp_run
    simp only [func21Def]
    exact ⟨data, rfl, hOutput⟩

end Project.ClobLimit.LimitFilled
