import Project.ClobLimit.Invalid
import Project.ClobLimit.LimitFilled
import Project.ClobLimit.LimitResidual

/-!
# Complete exported `limit` correctness

The primary theorem covers invalid, filled, and residual inputs.  One common
predicate states the exact source result, while the outcome predicate retains
the ownership, allocator, page, and memory facts specific to each branch.
-/

namespace Project.ClobLimit.LimitCorrect

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobMatchFuel.Allocation Project.ClobMatchFuel.AllocatorFrame
  Project.ClobPostOnly.Model

def SourceResultAt (st : Store Unit) (values : List Value)
    (result : Model.OpResultL) : Prop :=
  ∃ bookPtr tradesPtr : UInt64,
    values = [.i64 tradesPtr, .i64 bookPtr, .i64 result.status] ∧
    OrdersAt st bookPtr result.book ∧
    TradesAt st tradesPtr result.trades

inductive OutcomeAt (initial final : Store Unit) (book g0 g2 : UInt64)
    (os : List OrderL) (order : OrderL) (limit : Nat)
    (values : List Value) : Prop where
  | invalid
      (hInvalid : ¬validOrderL os order)
      (hValues : values = [.i64 (g0 + 48), .i64 book, .i64 1])
      (hBook : OrdersAt final book os)
      (hTrades : LimitCorrect.SourceResultAt final values
        (Model.limitL os order))
      (hFresh : Project.ClobLimit.Allocation.FreshTradeArrayAt final
        (g0 + 48))
      (hPages : final.mem.pages = initial.mem.pages)
      (hGlobals : final.globals.globals =
        ((initial.globals.globals.set 0 (.i64 (g0 + 56))).set 2
          (.i64 (g2 + 1))))
      (hMemory : ∀ a : Nat, a < g0.toNat →
        final.mem.bytes a = initial.mem.bytes a)
  | filled
      (hValid : validOrderL os order)
      (hRemaining : (Model.runMatchL os order).remaining = 0)
      (data : InternalLoopResult.OutputData)
      (hValues : values = [.i64 data.trades, .i64 data.book, .i64 0])
      (hOutput : InternalLoopResult.OutputAt
        (RunMatchCorrect.runMatchContext initial os order g0 g2 limit)
        final data)
  | residual
      (hValid : validOrderL os order)
      (hRemaining : (Model.runMatchL os order).remaining ≠ 0)
      (data : InternalLoopResult.OutputData)
      (hValues : values =
        [.i64 data.trades, .i64 (data.g0 + 48), .i64 0])
      (hOutput : LimitResidualExport.ExportedResultAt initial final
        (RunMatchCorrect.runMatchContext initial os order g0 g2 limit)
        data order g0)

def Postcondition (initial : Store Unit) (book g0 g2 : UInt64)
    (os : List OrderL) (order : OrderL) (limit : Nat)
    (final : Store Unit) (values : List Value) : Prop :=
  SourceResultAt final values (Model.limitL os order) ∧
    OutcomeAt initial final book g0 g2 os order limit values

def CorrectSpec : Prop :=
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
    limit + 48 + orderArrayBytes
      ((Model.runMatchL os order).book.length + 1) < 4294967296 →
    limit + 48 + orderArrayBytes
      ((Model.runMatchL os order).book.length + 1) ≤
        st.mem.pages * 65536 →
    TerminatesWith (m := «module») (id := 21) (initial := st) (env := env)
      (LimitEntry.limitArgs book order)
      (Postcondition st book g0 g2 os order limit)

set_option Elab.async false in
theorem func21_correct : CorrectSpec := by
  intro env st book bookCapacity g0 g2 os order limit hLength hBook48
    hBook32 hBookCapacity hBookBelow hBook hInitial32 hInitialFit hPages
    hg0 hg1 hg2 hAddressLimit hMemoryLimit hBudget hReserve32 hReserveFit
  by_cases hValid : validOrderL os order
  · by_cases hRemaining : (Model.runMatchL os order).remaining = 0
    · refine TerminatesWith.mono
        (LimitFilled.func21_filled env st book bookCapacity g0 g2 os order
          limit hLength hBook48 hBook32 hBookCapacity hBookBelow hBook
          hInitial32 hInitialFit hPages hg0 hg1 hg2 hAddressLimit
          hMemoryLimit hBudget hValid hRemaining) ?_
      rintro final values ⟨data, hValues, hOutput⟩
      have hModel := Model.limitL_filled os order hValid hRemaining
      have hContext := RunMatchCorrect.runMatchContext_result st os order g0
        g2 limit hLength
      constructor
      · refine ⟨data.book, data.trades, ?_, ?_, ?_⟩
        · simpa [hModel] using hValues
        · simpa [hModel, hContext] using hOutput.bookOwned.2
        · simpa [hModel, hContext] using hOutput.tradesOwned.2
      · exact .filled hValid hRemaining data hValues hOutput
    · refine TerminatesWith.mono
        (LimitResidual.func21_residual env st book bookCapacity g0 g2 os
          order limit hLength hBook48 hBook32 hBookCapacity hBookBelow hBook
          hInitial32 hInitialFit hPages hg0 hg1 hg2 hAddressLimit
          hMemoryLimit hBudget hReserve32 hReserveFit hValid hRemaining) ?_
      rintro final values ⟨data, hValues, hOutput⟩
      have hModel := Model.limitL_residual os order hValid hRemaining
      have hContext := RunMatchCorrect.runMatchContext_result st os order g0
        g2 limit hLength
      constructor
      · refine ⟨data.g0 + 48, data.trades, ?_, ?_, ?_⟩
        · simpa [hModel] using hValues
        · simpa [hModel, hContext] using hOutput.bookOwned.2
        · simpa [hModel, hContext] using hOutput.tradesOwned.2
      · exact .residual hValid hRemaining data hValues hOutput
  · have hInput32 : book.toNat + (os.length * 5 + 1) * 8 <
        4294967296 := by
      unfold fixedArrayBytes at hBook32
      omega
    have hInputBelow : book.toNat + (os.length * 5 + 1) * 8 ≤
        g0.toNat := by
      unfold fixedArrayBytes at hBookCapacity
      omega
    refine TerminatesWith.mono
      (Invalid.limit_invalid env st book g0 g2 os order hLength hInput32
        hInputBelow (by omega) (by omega) hPages hg0 hg1 hg2 hBook.2
        hValid) ?_
    rintro final values
      ⟨hValues, hOrders, hFresh, hFinalPages, hFinalGlobals, hMemory⟩
    have hRoot : (g0 + 48).toNat = g0.toNat + 48 := by
      rw [UInt64.toNat_add]
      have h48 : (48 : UInt64).toNat = 48 := rfl
      rw [h48]
      omega
    have hTradeBound : (g0 + 48).toNat % 4294967296 + 8 ≤
        final.mem.pages * 65536 := by
      rw [hRoot, Nat.mod_eq_of_lt (by omega), hFinalPages]
      omega
    have hTrades : TradesAt final (g0 + 48) [] := by
      constructor
      · constructor
        · rw [← toUInt32_eq_ofNat]
          exact hFresh.2
        · exact hTradeBound
      · intro j hj
        simp at hj
    have hModel := Model.limitL_invalid os order hValid
    have hSource : SourceResultAt final values (Model.limitL os order) := by
      refine ⟨book, g0 + 48, ?_, ?_, ?_⟩
      · simpa [hModel] using hValues
      · simpa [hModel] using hOrders
      · simpa [hModel] using hTrades
    exact ⟨hSource, .invalid hValid hValues hOrders hSource hFresh
      hFinalPages hFinalGlobals hMemory⟩

end Project.ClobLimit.LimitCorrect
