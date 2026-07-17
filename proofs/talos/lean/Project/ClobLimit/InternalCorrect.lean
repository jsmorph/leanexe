import Project.ClobLimit.InternalEntry
import Project.ClobLimit.InternalEarlyExit

/-!
# Internal matcher correctness

Function 17 terminates with the exact source-model remaining quantity and
represented result arrays.  Its five return values retain both owner-and-pointer
pairs.  The premises state the input ownership, allocator state, address bounds,
and allocation budget used by the loop invariant.
-/

namespace Project.ClobLimit.InternalCorrect

open Wasm Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobMatchFuel.AllocatorFrame

def InternalMatchSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ctx : Context)
    (bookOwner book bookCapacity tradesOwner trades tradesCapacity g0 : UInt64),
    48 ≤ book.toNat →
    book.toNat + fixedArrayBytes ctx.initialState.book.length 5 < 4294967296 →
    fixedArrayBytes ctx.initialState.book.length 5 ≤ bookCapacity.toNat →
    book.toNat + bookCapacity.toNat ≤ g0.toNat →
    48 ≤ trades.toNat →
    trades.toNat + fixedArrayBytes ctx.initialState.trades.length 4 <
      4294967296 →
    fixedArrayBytes ctx.initialState.trades.length 4 ≤ tradesCapacity.toNat →
    trades.toNat + tradesCapacity.toNat ≤ g0.toNat →
    OwnedOrderArrayAt st book bookCapacity ctx.initialState.book →
    OwnedTradeArrayAt st trades tradesCapacity ctx.initialState.trades →
    ctx.initialG0 = g0 →
    ctx.initialMem = st.mem →
    st.globals.globals[0]? = some (.i64 g0) →
    st.globals.globals[1]? = some (.i64 0) →
    st.globals.globals[2]? = some (.i64 ctx.initialG2) →
    st.mem.pages = ctx.initialPages →
    st.mem.pages ≤ 65536 →
    ctx.limit < 4294967296 →
    ctx.limit ≤ st.mem.pages * 65536 →
    g0.toNat + ctx.initialFuel.toNat *
      Project.ClobMatchFuel.Budget.stepBytes ctx.bookLimit ctx.tradeLimit ≤
        ctx.limit →
    TerminatesWith (m := «module») (id := 17) (initial := st) (env := env)
      (InternalEarlyExit.internalArgs ctx.initialFuel ctx.taker bookOwner book
        tradesOwner trades ctx.initialState.remaining)
      (fun st' values => InternalLoopResult.Postcondition ctx st' values)

theorem func17_correct : InternalMatchSpec := by
  intro env st ctx bookOwner book bookCapacity tradesOwner trades
    tradesCapacity g0 hBook48 hBook32 hBookCapacity hBookBelow hTrades48
    hTrades32 hTradesCapacity hTradesBelow hBookOwned hTradesOwned hInitialG0
    hInitialMem hG0 hG1 hG2 hPages hPageLimit hAddressLimit hMemoryLimit
    hBudget
  apply TerminatesWith.of_wp_entry_for (f := func17Def)
  · simp [«module»]
  · change wp «module» func17 _ st
      (InternalEntry.entryFrame ctx bookOwner book tradesOwner trades) env
    rw [InternalEntry.func17_decomposition]
    apply InternalInitialization.initProg_spec env st
      (InternalEntry.entryFrame ctx bookOwner book tradesOwner trades)
    · simp [InternalEntry.entryFrame, func17Def, Function.toLocals]
    · simp [InternalEntry.entryFrame, func17Def, Function.toLocals]
    · simp [InternalEntry.entryFrame, func17Def, Function.toLocals]
    · apply InternalLoop.loopProg_spec env ctx st
        (InternalInitialization.initFrame
          (InternalEntry.entryFrame ctx bookOwner book tradesOwner trades))
      · left
        refine ⟨InternalLoopInitial.initialData ctx bookOwner book bookCapacity
          tradesOwner trades tradesCapacity g0, ?_⟩
        apply InternalLoopInitial.of_initial ctx st _ bookOwner book
          bookCapacity tradesOwner trades tradesCapacity g0
        · exact InternalEntry.initialized_loop_locals ctx bookOwner book
            bookCapacity tradesOwner trades tradesCapacity g0
        · exact hBook48
        · exact hBook32
        · exact hBookCapacity
        · exact hBookBelow
        · exact hTrades48
        · exact hTrades32
        · exact hTradesCapacity
        · exact hTradesBelow
        · exact hBookOwned
        · exact hTradesOwned
        · exact hG0
        · exact hG1
        · exact hG2
        · rw [hInitialG0]
        · rw [hInitialMem]
          intro a ha
          rfl
        · exact hPages
        · exact hPageLimit
        · exact hAddressLimit
        · exact hMemoryLimit
        · exact hBudget
      · intro st1 s1 hExit
        apply InternalLoopResult.resultEpilogueProg_spec env ctx st1 s1 hExit
        intro data final hValues hOutput
        simp only [wp_simp]
        refine ⟨data, ?_, hOutput⟩
        simp [func17Def, Function.numParams, hValues,
          InternalLoopResult.outputValues, InternalEarlyExit.internalArgs]

end Project.ClobLimit.InternalCorrect
