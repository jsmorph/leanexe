import Project.ClobMarket.Valid
import Project.ClobMarket.Invalid

/-!
# Complete exported `market` correctness

The primary theorem covers valid and invalid orders.  Its source predicate
relates all three returned values to `Model.marketL`, while its outcome
predicate retains the branch-specific ownership and allocator facts.
-/

namespace Project.ClobMarket.Correct

open Wasm Project.Common Project.Clob Project.ClobMarket
  Project.ClobMarket.Model Project.ClobLimit.InternalLoopInvariant
  Project.ClobMatchFuel.AllocatorFrame Project.ClobPostOnly.Model

def SourceResultAt (st : Store Unit) (values : List Value)
    (result : Project.ClobLimit.Model.OpResultL) : Prop :=
  ∃ bookPtr tradesPtr : UInt64,
    values = [.i64 tradesPtr, .i64 bookPtr, .i64 result.status] ∧
    OrdersAt st bookPtr result.book ∧
    TradesAt st tradesPtr result.trades

inductive OutcomeAt (initial final : Store Unit)
    (book bookCapacity g0 g2 : UInt64) (os : List OrderL)
    (order : OrderL) (limit : Nat) (values : List Value) : Prop where
  | invalid
      (hInvalid : ¬validOrderL os order)
      (hPost : InvalidPost.Postcondition initial final book bookCapacity
        g0 g2 os values)
  | valid
      (hValid : validOrderL os order)
      (data : Project.ClobLimit.InternalLoopResult.OutputData)
      (hValues : values = [.i64 data.trades, .i64 data.book, .i64 0])
      (hOutput : Project.ClobLimit.InternalLoopResult.OutputAt
        (Project.ClobLimit.RunMatchCorrect.runMatchContext initial os
          (unlimitedTakerL order) g0 g2 limit) final data)

def Postcondition (initial : Store Unit)
    (book bookCapacity g0 g2 : UInt64) (os : List OrderL)
    (order : OrderL) (limit : Nat)
    (final : Store Unit) (values : List Value) : Prop :=
  SourceResultAt final values (marketL os order) ∧
  OutcomeAt initial final book bookCapacity g0 g2 os order limit values

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
    TerminatesWith (m := Project.ClobMarket.«module») (id := 21)
      (initial := st) (env := env) (Entry.marketArgs book order)
      (Postcondition st book bookCapacity g0 g2 os order limit)

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem func21_correct : CorrectSpec := by
  intro env st book bookCapacity g0 g2 os order limit hLength hBook48
    hBook32 hBookCapacity hBookBelow hBook hFit32 hFit hPages hg0 hg1 hg2
    hAddressLimit hMemoryLimit hBudget
  by_cases hValid : validOrderL os order
  · refine TerminatesWith.mono
      (Valid.func21_valid env st book bookCapacity g0 g2 os order limit
        hLength hBook48 hBook32 hBookCapacity hBookBelow hBook hFit32 hFit
        hPages hg0 hg1 hg2 hAddressLimit hMemoryLimit hBudget hValid) ?_
    rintro final values ⟨data, hValues, hOutput⟩
    have hModel := Model.marketL_valid os order hValid
    have hContext :=
      Project.ClobLimit.RunMatchCorrect.runMatchContext_result st os
        (unlimitedTakerL order) g0 g2 limit hLength
    constructor
    · refine ⟨data.book, data.trades, ?_, ?_, ?_⟩
      · simpa [hModel] using hValues
      · simpa [hModel, hContext] using hOutput.bookOwned.2
      · simpa [hModel, hContext] using hOutput.tradesOwned.2
    · exact .valid hValid data hValues hOutput
  · refine TerminatesWith.mono
      (Invalid.func21_invalid env st book bookCapacity g0 g2 os order
        hLength hBook48 hBook32 hBookCapacity hBookBelow hBook (by omega)
        (by omega) hPages hg0 hg1 hg2 hValid) ?_
    rintro final values hPost
    have hModel := Model.marketL_invalid os order hValid
    have hSource : SourceResultAt final values (marketL os order) := by
      refine ⟨book, g0 + 48, ?_, ?_, ?_⟩
      · simpa [hModel] using hPost.1
      · simpa [hModel] using hPost.2.1.2
      · simpa [hModel] using hPost.2.2.1.2
    exact ⟨hSource, .invalid hValid hPost⟩

end Project.ClobMarket.Correct
