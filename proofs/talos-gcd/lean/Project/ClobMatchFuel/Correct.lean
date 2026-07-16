import Project.ClobMatchFuel.Entry

/-!
# The `matchFuel` export theorem

The public export terminates with the exact source-model remaining quantity
and represented result arrays.  Its final store contains the represented free
list and the exact allocation and release counters.  The premises state the
input ownership, allocator state, address bounds, and allocation budget used by
the loop invariant.
-/

namespace Project.ClobMatchFuel.Correct

open Wasm Project.Clob Project.Runtime Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation Project.ClobMatchFuel.AllocatorFrame
  Project.ClobMatchFuel.LoopInvariant

set_option maxRecDepth 1048576

@[spec_of "lean" "LeanExe.Examples.Clob.matchFuel"]
def MatchFuelSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ctx : Context)
    (book bookCapacity trades tradesCapacity g0 : UInt64)
    (nodes : List FreeNode),
    48 ≤ book.toNat →
    book.toNat + fixedArrayBytes ctx.initialState.book.length 5 < 4294967296 →
    fixedArrayBytes ctx.initialState.book.length 5 ≤ bookCapacity.toNat →
    book.toNat + bookCapacity.toNat ≤ g0.toNat →
    FreeListSeparatedFromFixedArray nodes book bookCapacity →
    48 ≤ trades.toNat →
    trades.toNat + fixedArrayBytes ctx.initialState.trades.length 4 <
      4294967296 →
    fixedArrayBytes ctx.initialState.trades.length 4 ≤ tradesCapacity.toNat →
    trades.toNat + tradesCapacity.toNat ≤ g0.toNat →
    FreeListSeparatedFromFixedArray nodes trades tradesCapacity →
    (∀ node ∈ nodes,
      node.root.toNat + node.capacity.toNat ≤ g0.toNat) →
    OwnedOrderArrayAt st book bookCapacity ctx.initialState.book →
    OwnedTradeArrayAt st trades tradesCapacity ctx.initialState.trades →
    FreeListAt st.mem nodes →
    ctx.initialMem = st.mem →
    st.globals.globals[0]? = some (.i64 g0) →
    st.globals.globals[1]? = some (.i64 (freeHead nodes)) →
    st.globals.globals[2]? = some (.i64 ctx.initialG2) →
    st.globals.globals[4]? = some (.i64 ctx.initialG4) →
    st.globals.globals[5]? = some (.i64 ctx.initialG5) →
    st.mem.pages = ctx.initialPages →
    st.mem.pages ≤ 65536 →
    ctx.limit < 4294967296 →
    ctx.limit ≤ st.mem.pages * 65536 →
    g0.toNat + ctx.initialFuel.toNat *
      Budget.stepBytes ctx.bookLimit ctx.tradeLimit ≤ ctx.limit →
    TerminatesWith (m := «module») (id := 14) (initial := st) (env := env)
      [.i64 ctx.initialState.remaining, .i64 trades, .i64 book,
       .i64 ctx.taker.oqty, .i64 ctx.taker.oprice, .i64 ctx.taker.oside,
       .i64 ctx.taker.otrader, .i64 ctx.taker.oid, .i64 ctx.initialFuel]
      (fun st' values => LoopResult.Postcondition ctx st' values)

@[proves Project.ClobMatchFuel.Correct.MatchFuelSpec]
theorem matchFuel_correct : MatchFuelSpec := by
  intro env st ctx book bookCapacity trades tradesCapacity g0 nodes
    hBook48 hBook32 hBookCapacity hBookBelow hBookFree hTrades48 hTrades32
    hTradesCapacity hTradesBelow hTradesFree hNodesBelow hBookOwned
    hTradesOwned hFreeList hInitialMem hG0 hG1 hG2 hG4 hG5 hPages hPageLimit
    hAddressLimit hMemoryLimit hBudget
  apply TerminatesWith.of_wp_entry_for (f := func14Def)
  · simp [«module»]
  · change wp «module» func14 _ st (Entry.entryFrame ctx book trades) env
    rw [Entry.func14_decomposition]
    apply Initialization.initProg_spec env st (Entry.entryFrame ctx book trades)
      book trades ctx.initialState.remaining ctx.taker
    · simp [Entry.entryFrame, func14Def, Function.toLocals]
    · simp [Entry.entryFrame, func14Def, Function.toLocals]
    · simp [Entry.entryFrame, func14Def, Function.toLocals]
    · simp [Entry.entryFrame, func14Def, Function.toLocals]
    · simp [Entry.entryFrame, func14Def, Function.toLocals]
    · simp [Entry.entryFrame, func14Def, Function.toLocals]
    · simp [Entry.entryFrame, func14Def, Function.toLocals]
    · simp [Entry.entryFrame, func14Def, Function.toLocals]
    · simp [Entry.entryFrame, func14Def, Function.toLocals]
    · simp [Entry.entryFrame, func14Def, Function.toLocals]
    · simp [Entry.entryFrame, func14Def, Function.toLocals]
    · apply Loop.loopProg_spec env ctx st
        (Initialization.initFrame (Entry.entryFrame ctx book trades) ctx.taker
          book trades ctx.initialState.remaining)
      · left
        refine ⟨LoopInitial.initialData ctx book bookCapacity trades
          tradesCapacity g0 nodes, ?_⟩
        apply LoopInitial.of_initial ctx st _ book bookCapacity trades
          tradesCapacity g0 nodes
        · exact Entry.initialized_loop_locals ctx book bookCapacity trades
            tradesCapacity g0 nodes
        · exact hBook48
        · exact hBook32
        · exact hBookCapacity
        · exact hBookBelow
        · exact hBookFree
        · exact hTrades48
        · exact hTrades32
        · exact hTradesCapacity
        · exact hTradesBelow
        · exact hTradesFree
        · exact hNodesBelow
        · exact hBookOwned
        · exact hTradesOwned
        · exact hFreeList
        · exact hG0
        · exact hG1
        · exact hG2
        · exact hG4
        · exact hG5
        · rw [hInitialMem]
          exact MemoryFrame.BytesEqFrom.refl st.mem ctx.limit
        · exact hPages
        · exact hPageLimit
        · exact hAddressLimit
        · exact hMemoryLimit
        · exact hBudget
      · intro st1 s1 hExit
        apply LoopResult.resultEpilogueProg_spec env ctx st1 s1 hExit
        intro data final hValues hOutput
        simp only [wp_simp]
        refine ⟨data, ?_, hOutput⟩
        simp [func14Def, Function.numParams, hValues,
          LoopResult.outputValues]

end Project.ClobMatchFuel.Correct
