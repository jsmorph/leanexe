import Project.OrderBook.Program
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Call

/-!
# Specification for `matchBook`
-/

namespace Project.OrderBook.Spec

open Wasm

private def matchBookArgs
    (bidQuantity bidPrice askQuantity askPrice side quantity limitPrice : UInt64) :
    List Value :=
  [.i64 limitPrice, .i64 quantity, .i64 side, .i64 askPrice,
   .i64 askQuantity, .i64 bidPrice, .i64 bidQuantity]

private def minU64 (left right : UInt64) : UInt64 :=
  if left < right then
    left
  else
    right

private def tradeStackResult (tag quantity price : UInt64) : List Value :=
  [.i64 price, .i64 quantity, .i64 tag]

private def expectedStack
    (bidQuantity bidPrice askQuantity askPrice side quantity limitPrice : UInt64) :
    List Value :=
  if side = 0 then
    if askPrice ≤ limitPrice then
      tradeStackResult 1 (minU64 quantity askQuantity) askPrice
    else
      tradeStackResult 0 0 0
  else
    if limitPrice ≤ bidPrice then
      tradeStackResult 1 (minU64 quantity bidQuantity) bidPrice
    else
      tradeStackResult 0 0 0

private theorem u32CondTrue {p : Prop} [Decidable p] (h : p) :
    ((if p then (1 : UInt32) else 0) ≠ 0) := by
  simp [h]

private theorem u32CondFalse {p : Prop} [Decidable p] (h : ¬p) :
    ¬ ((if p then (1 : UInt32) else 0) ≠ 0) := by
  simp [h]

private theorem func0_min
    (env : HostEnv Unit) (initial : Store Unit) (left right : UInt64) :
    TerminatesWith env «module» 0 initial [.i64 right, .i64 left]
      (fun st vs => st = initial ∧ vs = [.i64 (minU64 left right)]) := by
  apply TerminatesWith.of_wp_entry_for (f := func0Def) rfl
  change wp «module» func0 _ initial
    { params := [.i64 left, .i64 right],
      locals := [.i64 0],
      values := [] } env
  unfold func0
  by_cases hLt : left < right
  · wp_run
    wp_peel
    simp [func0Def, minU64, hLt]
  · wp_run
    wp_peel
    simp [func0Def, minU64, hLt]

/-- The generated WASM export `matchBook` implements the order-book match rule
for every supplied one-level book and incoming order. -/
@[spec_of "lean" "LeanExe.Examples.OrderBook.matchBook"]
def MatchBookSpec : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
    (bidQuantity bidPrice askQuantity askPrice side quantity limitPrice : UInt64),
    TerminatesWith env «module» 1 initial
      (matchBookArgs bidQuantity bidPrice askQuantity askPrice side quantity limitPrice)
      (fun _ rs =>
        rs = expectedStack bidQuantity bidPrice askQuantity askPrice side quantity limitPrice)

set_option maxHeartbeats 1000000 in
@[proves Project.OrderBook.Spec.MatchBookSpec]
theorem matchBook_correct : MatchBookSpec := by
  intro env initial bidQuantity bidPrice askQuantity askPrice side quantity limitPrice
  apply TerminatesWith.of_wp_entry_for (f := func1Def) rfl
  change wp «module» func1 _ initial
    { params := [.i64 bidQuantity, .i64 bidPrice, .i64 askQuantity, .i64 askPrice,
        .i64 side, .i64 quantity, .i64 limitPrice],
      locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
        .i64 0, .i64 0, .i64 0],
      values := [] } env
  unfold func1
  by_cases hSide : side = 0
  · by_cases hCross : askPrice ≤ limitPrice
    · wp_run
      apply wp_iff_cons rfl
      rw [if_pos (u32CondTrue hSide)]
      wp_run
      apply wp_iff_cons rfl
      simp
      try wp_run
      apply wp_iff_cons rfl
      rw [if_pos (u32CondTrue hCross)]
      wp_run
      apply wp_iff_cons rfl
      rw [if_pos (u32CondTrue hSide)]
      wp_run
      apply wp_iff_cons rfl
      simp
      try wp_run
      apply wp_iff_cons rfl
      rw [if_pos (u32CondTrue hCross)]
      wp_run
      apply wp_call_tw (func0_min env initial quantity askQuantity)
      rintro st1 vs1 ⟨hst1, hvs1⟩
      subst st1
      subst vs1
      wp_run
      apply wp_iff_cons rfl
      rw [if_pos (u32CondTrue hSide)]
      wp_run
      apply wp_iff_cons rfl
      simp
      try wp_run
      apply wp_iff_cons rfl
      rw [if_pos (u32CondTrue hCross)]
      wp_run
      simp [func1Def, matchBookArgs, expectedStack, tradeStackResult, hSide, hCross]
    · wp_run
      apply wp_iff_cons rfl
      rw [if_pos (u32CondTrue hSide)]
      wp_run
      apply wp_iff_cons rfl
      simp
      try wp_run
      apply wp_iff_cons rfl
      rw [if_neg (u32CondFalse hCross)]
      wp_run
      apply wp_iff_cons rfl
      rw [if_pos (u32CondTrue hSide)]
      wp_run
      apply wp_iff_cons rfl
      simp
      try wp_run
      apply wp_iff_cons rfl
      rw [if_neg (u32CondFalse hCross)]
      wp_run
      apply wp_iff_cons rfl
      rw [if_pos (u32CondTrue hSide)]
      wp_run
      apply wp_iff_cons rfl
      simp
      try wp_run
      apply wp_iff_cons rfl
      rw [if_neg (u32CondFalse hCross)]
      wp_run
      simp [func1Def, matchBookArgs, expectedStack, tradeStackResult, hSide, hCross]
  · by_cases hCross : limitPrice ≤ bidPrice
    · wp_run
      apply wp_iff_cons rfl
      rw [if_neg (u32CondFalse hSide)]
      wp_run
      apply wp_iff_cons rfl
      simp
      try wp_run
      apply wp_iff_cons rfl
      rw [if_pos (u32CondTrue hCross)]
      wp_run
      apply wp_iff_cons rfl
      rw [if_neg (u32CondFalse hSide)]
      wp_run
      apply wp_iff_cons rfl
      simp
      try wp_run
      apply wp_iff_cons rfl
      rw [if_pos (u32CondTrue hCross)]
      wp_run
      apply wp_call_tw (func0_min env initial quantity bidQuantity)
      rintro st1 vs1 ⟨hst1, hvs1⟩
      subst st1
      subst vs1
      wp_run
      apply wp_iff_cons rfl
      rw [if_neg (u32CondFalse hSide)]
      wp_run
      apply wp_iff_cons rfl
      simp
      try wp_run
      apply wp_iff_cons rfl
      rw [if_pos (u32CondTrue hCross)]
      wp_run
      simp [func1Def, matchBookArgs, expectedStack, tradeStackResult, hSide, hCross]
    · wp_run
      apply wp_iff_cons rfl
      rw [if_neg (u32CondFalse hSide)]
      wp_run
      apply wp_iff_cons rfl
      simp
      try wp_run
      apply wp_iff_cons rfl
      rw [if_neg (u32CondFalse hCross)]
      wp_run
      apply wp_iff_cons rfl
      rw [if_neg (u32CondFalse hSide)]
      wp_run
      apply wp_iff_cons rfl
      simp
      try wp_run
      apply wp_iff_cons rfl
      rw [if_neg (u32CondFalse hCross)]
      wp_run
      apply wp_iff_cons rfl
      rw [if_neg (u32CondFalse hSide)]
      wp_run
      apply wp_iff_cons rfl
      simp
      try wp_run
      apply wp_iff_cons rfl
      rw [if_neg (u32CondFalse hCross)]
      wp_run
      simp [func1Def, matchBookArgs, expectedStack, tradeStackResult, hSide, hCross]

end Project.OrderBook.Spec
