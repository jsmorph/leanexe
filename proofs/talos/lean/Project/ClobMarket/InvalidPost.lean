import Project.ClobMarket.InvalidFinish

/-!
# Invalid `market` result predicate

The postcondition names the invalid branch's returned values and physical
state.  A constructor theorem derives it from the shared empty-array store.
Keeping the predicate opaque reduces the control-flow proof's elaboration
term.
-/

namespace Project.ClobMarket.InvalidPost

open Wasm Project.Clob Project.ClobMarket
  Project.ClobMatchFuel.AllocatorFrame

def Postcondition (initial final : Store Unit)
    (book bookCapacity g0 g2 : UInt64) (os : List OrderL)
    (values : List Value) : Prop :=
  values = [.i64 (g0 + 48), .i64 book, .i64 1] ∧
  OwnedOrderArrayAt final book bookCapacity os ∧
  OwnedTradeArrayAt final (g0 + 48) 8 [] ∧
  final.mem.pages = initial.mem.pages ∧
  final.globals.globals =
    ((initial.globals.globals.set 0 (.i64 (g0 + 56))).set 2
      (.i64 (g2 + 1))) ∧
  ∀ a : Nat, a < g0.toNat → final.mem.bytes a = initial.mem.bytes a

theorem allocStore_postcondition
    (st : Store Unit) (book bookCapacity g0 g2 : UInt64)
    (os : List OrderL)
    (hBook48 : 48 ≤ book.toNat)
    (hBook32 : book.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hBookCapacity : fixedArrayBytes os.length 5 ≤ bookCapacity.toNat)
    (hBookBelow : book.toNat + bookCapacity.toNat ≤ g0.toNat)
    (hBook : OwnedOrderArrayAt st book bookCapacity os)
    (hFit32 : g0.toNat + 56 < 4294967296)
    (hFit : g0.toNat + 56 ≤ st.mem.pages * 65536) :
    Postcondition st
      (Project.ClobLimit.RunMatchEmptyAlloc.allocStore st g0 g2)
      book bookCapacity g0 g2 os
      [.i64 (g0 + 48), .i64 book, .i64 1] := by
  unfold Postcondition
  refine ⟨rfl, ?_, ?_, ?_, rfl, ?_⟩
  · exact Project.ClobLimit.RunMatchEmptyAlloc.ownedOrderArrayAt_allocStore
      hFit32 hBook48 hBook32 hBookCapacity hBookBelow hBook
  · exact Project.ClobLimit.RunMatchEmptyAlloc.allocStore_empty_trade st
      g0 g2 hFit32 hFit
  · exact Project.ClobLimit.RunMatchEmptyAlloc.allocStore_pages st g0 g2
  · intro a ha
    exact Project.ClobLimit.RunMatchEmptyAlloc.allocStore_bytes_before st
      g0 g2 a hFit32 ha

end Project.ClobMarket.InvalidPost
