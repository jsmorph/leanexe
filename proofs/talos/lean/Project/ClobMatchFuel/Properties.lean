import Project.ClobMatchFuel.Model
import Mathlib.Logic.Relation

/-!
# Source properties for `matchFuel`

The step relation records the two state changes made by matching.  The
recursive model follows its reflexive transitive closure.  Natural-number
totals then state maker-quantity and taker-quantity conservation without a
fixed-width overflow premise.
-/

namespace Project.ClobMatchFuel.Properties

open Project.Clob Project.ClobFindBest.Model Project.ClobMatchFuel.Model

def orderQtyTotal (orders : List OrderL) : Nat :=
  (orders.map fun order => order.oqty.toNat).sum

def tradeQtyTotal (trades : List TradeL) : Nat :=
  (trades.map fun trade => trade.tqty.toNat).sum

def fullStepStateL (taker : OrderL) (state : MatchStateL) (i : Nat) :
    MatchStateL :=
  { book := state.book.eraseIdx i
    trades := state.trades ++
      [fillTradeL taker state.book[i]! state.book[i]!.oqty]
    remaining := state.remaining - state.book[i]!.oqty }

def partialStepStateL (taker : OrderL) (state : MatchStateL) (i : Nat) :
    MatchStateL :=
  { book := setQtyL state.book i
      (state.book[i]!.oqty - state.remaining)
    trades := state.trades ++
      [fillTradeL taker state.book[i]! state.remaining]
    remaining := 0 }

inductive MatchStepL (taker : OrderL) : MatchStateL → MatchStateL → Prop
  | full (state : MatchStateL) (i : Nat)
      (hRemaining : state.remaining ≠ 0)
      (hFind : findBestL state.book taker = some i)
      (hQty : state.book[i]!.oqty ≤ state.remaining) :
      MatchStepL taker state (fullStepStateL taker state i)
  | reduce (state : MatchStateL) (i : Nat)
      (hRemaining : state.remaining ≠ 0)
      (hFind : findBestL state.book taker = some i)
      (hQty : ¬state.book[i]!.oqty ≤ state.remaining) :
      MatchStepL taker state (partialStepStateL taker state i)

@[simp]
theorem tradeQtyTotal_append_fill (trades : List TradeL) (taker maker : OrderL)
    (qty : UInt64) :
    tradeQtyTotal (trades ++ [fillTradeL taker maker qty]) =
      tradeQtyTotal trades + qty.toNat := by
  simp [tradeQtyTotal, fillTradeL]

theorem orderQtyTotal_eraseIdx (orders : List OrderL) (i : Nat)
    (hi : i < orders.length) :
    orderQtyTotal (orders.eraseIdx i) + orders[i]!.oqty.toNat =
      orderQtyTotal orders := by
  induction orders generalizing i with
  | nil => simp at hi
  | cons order orders ih =>
      cases i with
      | zero => simp [orderQtyTotal, Nat.add_comm]
      | succ i =>
          have hi' : i < orders.length := by simpa using hi
          have h := ih i hi'
          simpa [orderQtyTotal, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using congrArg (order.oqty.toNat + ·) h

theorem orderQtyTotal_setQtyL (orders : List OrderL) (i : Nat) (qty : UInt64)
    (hi : i < orders.length) :
    orderQtyTotal (setQtyL orders i qty) + orders[i]!.oqty.toNat =
      orderQtyTotal orders + qty.toNat := by
  induction orders generalizing i with
  | nil => simp at hi
  | cons order orders ih =>
      cases i with
      | zero => simp [setQtyL, orderQtyTotal,
          Nat.add_left_comm, Nat.add_comm]
      | succ i =>
          have hi' : i < orders.length := by simpa using hi
          have h := ih i hi'
          simpa [setQtyL, orderQtyTotal, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using congrArg (order.oqty.toNat + ·) h

theorem eraseIdx_getElem! (orders : List OrderL) (i j : Nat)
    (hi : i < orders.length) (hj : j < (orders.eraseIdx i).length) :
    (orders.eraseIdx i)[j]! =
      if j < i then orders[j]! else orders[j + 1]! := by
  rw [Project.Common.getBang_eq hj, List.getElem_eraseIdx]
  split <;> rename_i hji
  · rw [Project.Common.getBang_eq (by omega)]
  · rw [Project.Common.getBang_eq (by
      rw [List.length_eraseIdx_of_lt hi] at hj
      omega)]

theorem setQtyL_getElem!_of_ne (orders : List OrderL) (i j : Nat)
    (qty : UInt64) (hi : i < orders.length) (hj : j < orders.length)
    (hij : i ≠ j) :
    (setQtyL orders i qty)[j]! = orders[j]! := by
  rw [setQtyL_eq_set orders i qty hi]
  rw [Project.Common.getBang_eq (by simpa using hj)]
  rw [List.getElem_set_of_ne hij _ (by simpa using hj)]
  rw [Project.Common.getBang_eq hj]

theorem MatchStepL.trades_eq_append_singleton {taker : OrderL}
    {before after : MatchStateL} (h : MatchStepL taker before after) :
    ∃ trade, after.trades = before.trades ++ [trade] := by
  cases h with
  | full i _ _ _ =>
      exact ⟨fillTradeL taker before.book[i]! before.book[i]!.oqty, rfl⟩
  | reduce i _ _ _ =>
      exact ⟨fillTradeL taker before.book[i]! before.remaining, rfl⟩

theorem MatchStepL.orderTradeTotal {taker : OrderL}
    {before after : MatchStateL} (h : MatchStepL taker before after) :
    orderQtyTotal after.book + tradeQtyTotal after.trades =
      orderQtyTotal before.book + tradeQtyTotal before.trades := by
  cases h with
  | full i _ hFind hQty =>
      have hi : i < before.book.length :=
        findBestL_some_lt before.book taker i hFind
      have hBook := orderQtyTotal_eraseIdx before.book i hi
      simp only [fullStepStateL, tradeQtyTotal_append_fill]
      omega
  | reduce i _ hFind hQty =>
      have hi : i < before.book.length :=
        findBestL_some_lt before.book taker i hFind
      have hBook := orderQtyTotal_setQtyL before.book i
        (before.book[i]!.oqty - before.remaining) hi
      have hQtyNat : ¬before.book[i]!.oqty.toNat ≤ before.remaining.toNat := by
        simpa [UInt64.le_iff_toNat_le] using hQty
      have hRemainingLe : before.remaining ≤ before.book[i]!.oqty :=
        UInt64.le_iff_toNat_le.mpr (by omega)
      have hSub := UInt64.toNat_sub_of_le before.book[i]!.oqty
        before.remaining hRemainingLe
      simp only [partialStepStateL, tradeQtyTotal_append_fill]
      omega

theorem MatchStepL.remainingTradeTotal {taker : OrderL}
    {before after : MatchStateL} (h : MatchStepL taker before after) :
    after.remaining.toNat + tradeQtyTotal after.trades =
      before.remaining.toNat + tradeQtyTotal before.trades := by
  cases h with
  | full i _ _ hQty =>
      have hQtyNat : before.book[i]!.oqty.toNat ≤ before.remaining.toNat :=
        UInt64.le_iff_toNat_le.mp hQty
      have hSub := UInt64.toNat_sub_of_le before.remaining
        before.book[i]!.oqty hQty
      simp only [fullStepStateL, tradeQtyTotal_append_fill]
      omega
  | reduce i _ _ _ =>
      simp [partialStepStateL, Nat.add_comm]

theorem matchFuelL_steps (fuel : Nat) (taker : OrderL) (state : MatchStateL) :
    Relation.ReflTransGen (MatchStepL taker) state
      (matchFuelL fuel taker state) := by
  induction fuel generalizing state with
  | zero =>
      simp only [matchFuelL]
      exact .refl
  | succ fuel ih =>
      by_cases hRemaining : state.remaining = 0
      · rw [matchFuelL_succ_zero fuel taker state hRemaining]
      · cases hFind : findBestL state.book taker with
        | none =>
            rw [matchFuelL_succ_none fuel taker state hRemaining hFind]
        | some i =>
            by_cases hQty : state.book[i]!.oqty ≤ state.remaining
            · rw [matchFuelL_succ_full fuel taker state i hRemaining hFind hQty]
              exact Relation.ReflTransGen.head
                (MatchStepL.full state i hRemaining hFind hQty) (ih _)
            · rw [matchFuelL_succ_partial fuel taker state i hRemaining hFind
                hQty]
              exact Relation.ReflTransGen.single
                (MatchStepL.reduce state i hRemaining hFind hQty)

theorem matchSteps_orderTradeTotal {taker : OrderL}
    {before after : MatchStateL}
    (h : Relation.ReflTransGen (MatchStepL taker) before after) :
    orderQtyTotal after.book + tradeQtyTotal after.trades =
      orderQtyTotal before.book + tradeQtyTotal before.trades := by
  induction h with
  | refl => rfl
  | tail hSteps hStep ih =>
      exact (hStep.orderTradeTotal).trans ih

theorem matchSteps_remainingTradeTotal {taker : OrderL}
    {before after : MatchStateL}
    (h : Relation.ReflTransGen (MatchStepL taker) before after) :
    after.remaining.toNat + tradeQtyTotal after.trades =
      before.remaining.toNat + tradeQtyTotal before.trades := by
  induction h with
  | refl => rfl
  | tail hSteps hStep ih =>
      exact (hStep.remainingTradeTotal).trans ih

theorem matchFuelL_quantity_conservation (fuel : Nat) (taker : OrderL)
    (state : MatchStateL) :
    orderQtyTotal (matchFuelL fuel taker state).book +
        tradeQtyTotal (matchFuelL fuel taker state).trades =
      orderQtyTotal state.book + tradeQtyTotal state.trades ∧
    (matchFuelL fuel taker state).remaining.toNat +
        tradeQtyTotal (matchFuelL fuel taker state).trades =
      state.remaining.toNat + tradeQtyTotal state.trades := by
  have hSteps := matchFuelL_steps fuel taker state
  exact ⟨matchSteps_orderTradeTotal hSteps,
    matchSteps_remainingTradeTotal hSteps⟩

end Project.ClobMatchFuel.Properties
