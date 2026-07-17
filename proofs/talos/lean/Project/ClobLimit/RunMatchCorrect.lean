import Project.ClobLimit.RunMatchResult
import Project.ClobLimit.Model

/-!
# Complete `runMatch` correctness

Function 18 initializes an empty match state and delegates to function 17.
The theorem composes its preparation, both initial allocations, the complete
internal matcher, and the five-value result epilogue.
-/

namespace Project.ClobLimit.RunMatchCorrect

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobMatchFuel.AllocatorFrame

set_option maxRecDepth 1048576

def runMatchArgs (bookOwner book : UInt64) (taker : OrderL) : List Value :=
  [.i64 taker.oqty, .i64 taker.oprice, .i64 taker.oside,
    .i64 taker.otrader, .i64 taker.oid, .i64 book, .i64 bookOwner]

def runMatchContext (st : Store Unit) (os : List OrderL) (taker : OrderL)
    (g0 g2 : UInt64) (limit : Nat) : Context :=
  { initialFuel := UInt64.ofNat (os.length + 1)
    taker := taker
    initialState := { book := os, trades := [], remaining := taker.oqty }
    initialG0 := g0 + 112
    initialG2 := g2 + 2
    initialMem := (RunMatchAllocations.allocationsStore st g0 g2).mem
    initialPages := st.mem.pages
    limit := limit }

theorem runMatchContext_result
    (st : Store Unit) (os : List OrderL) (taker : OrderL)
    (g0 g2 : UInt64) (limit : Nat)
    (hLength : os.length < 4294967296) :
    (runMatchContext st os taker g0 g2 limit).result =
      Project.ClobLimit.Model.runMatchL os taker := by
  have hFuel : (UInt64.ofNat (os.length + 1)).toNat = os.length + 1 :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  unfold runMatchContext Context.result Project.ClobLimit.Model.runMatchL
  rw [hFuel]

def RunMatchSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit)
    (bookOwner book bookCapacity g0 g2 : UInt64)
    (os : List OrderL) (taker : OrderL) (limit : Nat),
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
    TerminatesWith (m := «module») (id := 18) (initial := st) (env := env)
      (runMatchArgs bookOwner book taker)
      (InternalLoopResult.Postcondition
        (runMatchContext st os taker g0 g2 limit))

set_option Elab.async false in
theorem func18_correct : RunMatchSpec := by
  intro env st bookOwner book bookCapacity g0 g2 os taker limit hLength
    hBook48 hBook32 hBookCapacity hBookBelow hBook hFit32 hFit hPages hg0
    hg1 hg2 hAddressLimit hMemoryLimit hBudget
  let stA := RunMatchAllocations.allocationsStore st g0 g2
  let ctx := runMatchContext st os taker g0 g2 limit
  have hHeapNat : (g0 + 112).toNat = g0.toNat + 112 := by
    rw [UInt64.toNat_add]
    have h112 : (112 : UInt64).toNat = 112 := rfl
    rw [h112]
    omega
  have hTradesNat : (g0 + 104).toNat = g0.toNat + 104 := by
    rw [UInt64.toNat_add]
    have h104 : (104 : UInt64).toNat = 104 := rfl
    rw [h104]
    omega
  have hFuelNat : (UInt64.ofNat (os.length + 1)).toNat = os.length + 1 :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  have hAlloc := RunMatchAllocations.allocationsStore_facts st book
    bookCapacity g0 g2 os hFit32 hFit hBook48 hBook32 hBookCapacity
    hBookBelow hBook hg0 hg1 hg2
  have hInternal : TerminatesWith (m := «module») (id := 17)
      (initial := stA) (env := env)
      (InternalEarlyExit.internalArgs (UInt64.ofNat (os.length + 1)) taker
        bookOwner book (g0 + 48) (g0 + 104) taker.oqty)
      (fun st' values => InternalLoopResult.Postcondition ctx st' values) := by
    apply InternalCorrect.func17_correct env stA ctx bookOwner book
      bookCapacity (g0 + 48) (g0 + 104) 8 (g0 + 112)
    · exact hBook48
    · exact hBook32
    · exact hBookCapacity
    · rw [hHeapNat]
      omega
    · rw [hTradesNat]
      omega
    · change (g0 + 104).toNat + fixedArrayBytes 0 4 < 4294967296
      rw [hTradesNat]
      simp [fixedArrayBytes]
      omega
    · change fixedArrayBytes 0 4 ≤ (8 : UInt64).toNat
      simp [fixedArrayBytes]
    · rw [hTradesNat, hHeapNat]
      have h8 : (8 : UInt64).toNat = 8 := rfl
      rw [h8]
    · simpa [ctx, runMatchContext] using hAlloc.book
    · simpa [ctx, runMatchContext] using hAlloc.trades
    · rfl
    · rfl
    · exact hAlloc.global0
    · exact hAlloc.global1
    · exact hAlloc.global2
    · exact hAlloc.pages
    · rw [hAlloc.pages]
      exact hPages
    · exact hAddressLimit
    · rw [hAlloc.pages]
      exact hMemoryLimit
    · change (g0 + 112).toNat +
          (UInt64.ofNat (os.length + 1)).toNat *
            Project.ClobMatchFuel.Budget.stepBytes os.length
              (0 + (UInt64.ofNat (os.length + 1)).toNat) ≤ limit
      rw [hHeapNat, hFuelNat]
      simpa using hBudget
  apply TerminatesWith.of_wp_entry_for (f := func18Def)
  · simp [«module»]
  · change wp «module» func18 _ st
      (RunMatchPrepare.entryFrame bookOwner book taker) env
    rw [RunMatchEntry.func18_decomposition]
    apply RunMatchPrepare.prepareProg_spec env st bookOwner book taker os
      hLength hBook.2
    apply RunMatchAllocations.allocationsProg_spec env st bookOwner book g0 g2
      taker os hFit32 hFit hPages hg0 hg1 hg2
    have hCallLocals := RunMatchCall.finalFrame_callLocals
      bookOwner book g0 taker os
    apply RunMatchCall.callProg_spec env stA
      (RunMatchAllocations.finalFrame bookOwner book taker os g0)
      (UInt64.ofNat (os.length + 1)) taker bookOwner book (g0 + 48)
      (g0 + 104) taker.oqty hCallLocals
      (InternalLoopResult.Postcondition ctx) hInternal
    intro st' values hPost
    rcases hPost with ⟨data, hValues, hOutput⟩
    apply RunMatchResult.resultProg_spec env st'
      (RunMatchAllocations.finalFrame bookOwner book taker os g0) values
      ctx data
    · exact hCallLocals.params
    · exact hCallLocals.locals
    · exact hValues
    · intro final hFinalValues
      simp only [wp_simp]
      refine ⟨data, ?_, hOutput⟩
      simp [func18Def, Function.numParams, hFinalValues,
        InternalLoopResult.outputValues, runMatchArgs, ctx]

end Project.ClobLimit.RunMatchCorrect
