import Project.ClobMarket.FrozenMatchRegion
import Project.ClobLimit.FrozenRunMatchCorrect

/-!
# Transported `runMatch` correctness

Function 18 and its complete direct-call closure are identical in the market
and limit artifacts.  The function-region theorem transfers termination and
the exact limit matcher postcondition to the market module.  No generated
matcher instruction is reproved here.
-/

namespace Project.ClobMarket.Frozen.RunMatch

open Wasm Project.Common Project.Clob
  Project.ClobMarket.Frozen.MatchRegion
  Project.ClobLimit.Frozen.InternalLoopInvariant
  Project.ClobMatchFuel.Frozen.AllocatorFrame

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
      Project.ClobMatchFuel.Frozen.Budget.stepBytes os.length (os.length + 1) ≤
        limit →
    TerminatesWith (m := Project.ClobMarket.Frozen.«module») (id := 18)
      (initial := st) (env := env)
      (Project.ClobLimit.Frozen.RunMatchCorrect.runMatchArgs bookOwner book taker)
      (Project.ClobLimit.Frozen.InternalLoopResult.Postcondition
        (Project.ClobLimit.Frozen.RunMatchCorrect.runMatchContext st os taker g0 g2
          limit))

theorem func18_correct : RunMatchSpec := by
  intro env st bookOwner book bookCapacity g0 g2 os taker limit hLength
    hBook48 hBook32 hBookCapacity hBookBelow hBook hFit32 hFit hPages hg0
    hg1 hg2 hAddressLimit hMemoryLimit hBudget
  exact Project.FunctionRegion.terminatesWith matchShift 18
    (by simp [MatchDomain])
    (Project.ClobLimit.Frozen.RunMatchCorrect.func18_correct env st bookOwner book
      bookCapacity g0 g2 os taker limit hLength hBook48 hBook32 hBookCapacity
      hBookBelow hBook hFit32 hFit hPages hg0 hg1 hg2 hAddressLimit
      hMemoryLimit hBudget)

end Project.ClobMarket.Frozen.RunMatch
