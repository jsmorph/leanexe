import Project.ClobMarket.ValidResult

/-!
# Valid exported `market` branch

The valid branch transforms the taker's price, runs the transported matcher,
and returns the matcher book and trades with status zero.  Its postcondition
retains the complete matcher ownership, allocator, page, and memory facts.
-/

namespace Project.ClobMarket.Valid

open Wasm Project.Common Project.Clob Project.ClobMarket
  Project.ClobMarket.Model
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobMatchFuel.AllocatorFrame Project.ClobPostOnly.Model

def ValidSpec : Prop :=
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
    TerminatesWith (m := Project.ClobMarket.«module») (id := 21)
      (initial := st) (env := env) (Entry.marketArgs book order)
      (fun st' values =>
        ∃ data,
          values = [.i64 data.trades, .i64 data.book, .i64 0] ∧
          Project.ClobLimit.InternalLoopResult.OutputAt
            (Project.ClobLimit.RunMatchCorrect.runMatchContext st os
              (unlimitedTakerL order) g0 g2 limit) st' data)

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem func21_valid : ValidSpec := by
  intro env st book bookCapacity g0 g2 os order limit hLength hBook48
    hBook32 hBookCapacity hBookBelow hBook hFit32 hFit hPages hg0 hg1 hg2
    hAddressLimit hMemoryLimit hBudget hValid
  let taker := unlimitedTakerL order
  let ctx := Project.ClobLimit.RunMatchCorrect.runMatchContext st os taker
    g0 g2 limit
  have hRunMatch : TerminatesWith (m := Project.ClobMarket.«module»)
      (id := 18) (initial := st) (env := env)
      (Project.ClobLimit.RunMatchCorrect.runMatchArgs 0 book taker)
      (Project.ClobLimit.InternalLoopResult.Postcondition ctx) := by
    apply RunMatch.func18_correct env st 0 book bookCapacity g0 g2 os taker
      limit hLength hBook48 hBook32 hBookCapacity hBookBelow hBook hFit32
      hFit hPages hg0 hg1 hg2 hAddressLimit hMemoryLimit hBudget
  apply TerminatesWith.of_wp_entry_for (f := func21Def)
  · simp [Project.ClobMarket.«module»]
  · change wp Project.ClobMarket.«module» func21 _ st
      (Entry.entryFrame book order) env
    rw [Entry.func21_decomposition]
    apply ValidEntry.entryProg_valid_spec env st book os order hLength
      hBook.2 hValid
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    simp only [Entry.validProg, List.append_assoc]
    apply Price.priceProg_spec env st book order
    apply Call.callProg_spec env st book order
      (Project.ClobLimit.InternalLoopResult.Postcondition ctx) hRunMatch
    rintro st2 values ⟨data, hValues, hOutput⟩
    apply ValidResult.validResultProg_spec env st2 book order ctx data values
      hValues
    simp only [wp_simp]
    apply ValidResult.resultProg_spec env st2 book order ctx data
    simp only [wp_simp]
    refine ⟨data, rfl, ?_⟩
    simpa [ctx, taker] using hOutput

end Project.ClobMarket.Valid
