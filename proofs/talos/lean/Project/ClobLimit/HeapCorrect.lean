import Project.ClobLimit.HeapEntry

namespace Project.ClobLimit.HeapCorrect
open Wasm Project.Clob Project.Runtime Project.ClobMatchFuel
open Project.ClobMatchFuel.Allocation Project.ClobMatchFuel.AllocatorFrame
open Project.ClobMatchFuel.LoopInvariant
set_option maxRecDepth 1048576

def Spec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ctx : Context)
    (book bookCapacity tradesOwner trades tradesCapacity g0 : UInt64)
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
    TerminatesWith (m := Project.ClobLimit.«module») (id := 17) (initial := st) (env := env)
      (HeapEntry.args ctx book tradesOwner trades)
      (fun st' values => ∃ data bookOwner tradesOwner,
        values = HeapResult.outputValues ctx data bookOwner tradesOwner ∧
        LoopResult.OutputAt ctx st' data)

set_option Elab.async false in
theorem spec : Spec := by
  intro env st ctx book bookCapacity tradesOwner trades tradesCapacity g0 nodes
    hBook48 hBook32 hBookCapacity hBookBelow hBookFree hTrades48 hTrades32
    hTradesCapacity hTradesBelow hTradesFree hNodesBelow hBookOwned
    hTradesOwned hFreeList hInitialMem hG0 hG1 hG2 hG4 hG5 hPages hPageLimit
    hAddressLimit hMemoryLimit hBudget
  apply TerminatesWith.of_wp_entry_for (f := func17Def)
  · simp [Project.ClobLimit.«module»]
  · change wp Project.ClobLimit.«module» func17 _ st (HeapEntry.entryFrame ctx book tradesOwner trades) env
    rw [HeapProgram.decomposition]
    apply HeapEntry.init_spec
    apply HeapLoop.spec env ctx st (HeapEntry.entryFrame ctx book tradesOwner trades)
    · refine ⟨HeapEntry.sourceFrame ctx book tradesOwner trades,
        HeapEntry.related ctx book tradesOwner trades, Or.inl ?_⟩
      refine ⟨LoopInitial.initialData ctx book bookCapacity trades tradesCapacity g0 nodes, ?_⟩
      exact LoopInitial.of_initial ctx st _ book bookCapacity trades tradesCapacity g0 nodes
        (HeapEntry.source_locals ctx book bookCapacity tradesOwner trades tradesCapacity g0 nodes)
        hBook48 hBook32 hBookCapacity hBookBelow hBookFree hTrades48 hTrades32
        hTradesCapacity hTradesBelow hTradesFree hNodesBelow hBookOwned hTradesOwned
        hFreeList hG0 hG1 hG2 hG4 hG5
        (by rw [hInitialMem]; exact MemoryFrame.BytesEqFrom.refl st.mem ctx.limit)
        hPages hPageLimit hAddressLimit hMemoryLimit hBudget
    · intro st1 s1 hExit
      apply HeapResult.spec env ctx st1 s1 hExit
      intro data bookOwner tradesOwner final hValues hOutput
      simp only [wp_simp]
      refine ⟨data, bookOwner, tradesOwner, ?_, hOutput⟩
      simp [func17Def, Function.numParams, hValues, HeapEntry.args, HeapResult.outputValues]

#print axioms spec
end Project.ClobLimit.HeapCorrect
