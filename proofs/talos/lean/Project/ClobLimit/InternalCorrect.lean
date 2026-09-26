import Project.ClobLimit.MatchEntry
import Project.ClobLimit.MatchResult

namespace Project.ClobLimit.InternalCorrect
open Wasm Project.Clob Project.Runtime Project.ClobLimit.MatchInvariant
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
    st.globals.globals[4]? = some (.i64 ctx.initialG4) →
    st.globals.globals[5]? = some (.i64 ctx.initialG5) →
    st.mem.pages = ctx.initialPages →
    st.mem.pages ≤ 65536 →
    ctx.limit < 4294967296 →
    ctx.limit ≤ st.mem.pages * 65536 →
    g0.toNat + ctx.initialFuel.toNat *
      Project.ClobMatchFuel.Budget.stepBytes ctx.bookLimit ctx.tradeLimit ≤
        ctx.limit →
    TerminatesWith (m := «module») (id := 17) (initial := st) (env := env)
      (MatchEntry.args ctx bookOwner book tradesOwner trades)
      (fun st' values => MatchOutput.Postcondition ctx st' values)

set_option Elab.async false in
theorem func17_correct : InternalMatchSpec := by
  intro env st ctx bookOwner book bookCapacity tradesOwner trades tradesCapacity
    g0 hBook48 hBook32 hBookCapacity hBookBelow hTrades48 hTrades32 hTradesCapacity
    hTradesBelow hBookOwned hTradesOwned hInitialG0 hInitialMem hG0 hG1 hG2 hG4 hG5
    hPages hPageLimit hAddressLimit hMemoryLimit hBudget
  let source := MatchEntry.sourceFrame ctx bookOwner book tradesOwner trades
  let target := MatchEntry.entryFrame ctx bookOwner book tradesOwner trades
  let initial := MatchEntry.initialData ctx bookOwner book bookCapacity trades tradesCapacity g0
  have hRelated : MatchLocals.mapping.Related source target :=
    MatchEntry.related ctx bookOwner book tradesOwner trades
  have hBase : Project.ClobMatchFuel.LoopInvariant.RunningFacts ctx.base st source initial := by
    apply Project.ClobMatchFuel.LoopInitial.of_initial ctx.base st source book
      bookCapacity trades tradesCapacity g0 [] bookOwner
    · exact MatchEntry.initial_locals ctx bookOwner book bookCapacity tradesOwner trades tradesCapacity g0
    · exact hBook48
    · exact hBook32
    · exact hBookCapacity
    · exact hBookBelow
    · intro node hNode
      cases hNode
    · exact hTrades48
    · exact hTrades32
    · exact hTradesCapacity
    · exact hTradesBelow
    · intro node hNode
      cases hNode
    · intro node hNode
      cases hNode
    · exact hBookOwned
    · exact hTradesOwned
    · exact .nil
    · exact hG0
    · exact hG1
    · exact hG2
    · exact hG4
    · exact hG5
    · change Project.ClobMatchFuel.MemoryFrame.BytesEqFrom ctx.initialMem st.mem ctx.limit
      rw [hInitialMem]
      exact .refl _ _
    · exact hPages
    · exact hPageLimit
    · exact hAddressLimit
    · exact hMemoryLimit
    · exact hBudget
  have hInitial : RunningFacts ctx st source initial tradesOwner := {
    base := hBase
    owner := MatchEntry.initial_owner ctx bookOwner book tradesOwner trades
    floor48 := by change 48 ≤ ctx.initialG0.toNat; rw [hInitialG0]; omega
    heapMono := by change ctx.initialG0.toNat ≤ g0.toNat; rw [hInitialG0]
    memoryBelow := by change Project.ClobMatchFuel.MemoryBelow.BytesEqBelow ctx.initialMem st.mem _
                      rw [hInitialMem]; exact .refl _ _
    nodesAbove := by intro node hNode; cases hNode
    trackedAbove := by change (0 : UInt64) ≠ 0 → _; intro h; exact (h rfl).elim }
  apply TerminatesWith.of_wp_entry_for (f := func17Def)
  · simp [«module»]
  · change wp «module» func17 _ st target env
    rw [MatchProgram.decomposition, List.append_assoc]
    apply MatchEntry.init_spec env ctx st bookOwner book tradesOwner trades
    apply MatchTargetLoop.loop_spec env ctx st source target hRelated
      (Or.inl ⟨initial, tradesOwner, hInitial⟩)
    intro st1 source1 target1 hExit hRelated1
    have hFinish := MatchResult.finish_spec env ctx st1 source1 target1 hRelated1 hExit
    apply hFinish _ []
    intro data final hValues hOutput
    simp only [wp_simp]
    refine ⟨data, ?_, hOutput⟩
    simp [func17Def, Function.numParams, hValues, MatchOutput.outputValues,
      MatchEntry.args, MatchEntry.internalArgs]

#print axioms func17_correct
end Project.ClobLimit.InternalCorrect
