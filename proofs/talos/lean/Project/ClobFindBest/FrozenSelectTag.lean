import Project.ClobFindBest.FrozenLoopState

namespace Project.ClobFindBest.Frozen.Loop
open Wasm Project.Common Project.Clob Project.ClobFindBest
  Project.ClobFindBest.Frozen.Model Project.ClobFindBest.Frozen.Helpers Project.ProofKit.PackedFloatFrame

set_option maxRecDepth 32768
set_option maxHeartbeats 400000

syntax "frozen_select_peel" Lean.Parser.Tactic.simpArgs : tactic
macro_rules
  | `(tactic| frozen_select_peel [$args,*]) => `(tactic|
    (wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, $args,*]
     try norm_num [UInt64.toNat_ofNat, $args,*]
     repeat
       (refine wp_iff_cons rfl ?_
        first
        | rw [ite_eq_left (by decide)]
        | rw [ite_eq_right (by decide)]
        wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, $args,*]
        try norm_num [UInt64.toNat_ofNat, $args,*])))


theorem select_tag_spec (env : HostEnv Unit) (st : Store Unit)
    (fuel owner ptr : UInt64) (taker : OrderL) (os : List OrderL) (k : Nat)
    (best : Option Nat) (tag payload : UInt64) (scratch : List Value)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os)
    (hk : k < os.length) (hBest : ∀ j, best = some j → j < os.length)
    (hScratch : scratch.length = 44)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ next : List Value, next.length = 44 →
      next[29]? = some (.i64 (optionTag (bestStepL os taker k best))) →
      next[0]? = scratch[0]? →
      next[1]? = scratch[1]? →
      next[2]? = scratch[2]? →
      next[3]? = scratch[3]? →
      next[4]? = scratch[4]? →
      next[5]? = scratch[5]? →
      next[6]? = scratch[6]? →
      next[7]? = scratch[7]? →
      wp module rest Q st (fbFrame fuel owner ptr taker k best tag payload 0 next) env) :
    wp module ((stepCode.drop 26).take 5 ++ rest) Q st
      (fbFrame fuel owner ptr taker k best tag payload 0 scratch) env := by
  obtain ⟨⟨hHead, hHeadB⟩, hElems⟩ := hInput
  obtain ⟨⟨hr1, hb1⟩, ⟨hr2, hb2⟩, ⟨hr3, hb3⟩, ⟨hr4, hb4⟩, ⟨hr5, hb5⟩⟩ := hElems k hk
  have hlt : UInt64.ofNat k < UInt64.ofNat os.length := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by rw [size_eq]; omega),
      UInt64.toNat_ofNat_of_lt' (by rw [size_eq]; omega)]
    exact hk
  unfold stepCode loopCode func7
  dsimp only
  cases best with
  | none =>
    frozen_select_peel [fbFrame, hScratch, optionTag, hHead, hlt, hr1, hr2, hr3, hr4, hr5,
      Nat.not_lt_of_ge hHeadB, Nat.not_lt_of_ge hb1, Nat.not_lt_of_ge hb2,
      Nat.not_lt_of_ge hb3, Nat.not_lt_of_ge hb4, Nat.not_lt_of_ge hb5]
    refine wp_call_tw (func5_spec env st taker (os[k]?.getD default)) ?_
    rintro nextStore values ⟨rfl, rfl⟩
    by_cases hEligible : eligibleL taker os[k]!
    · have hWord : boolWord (eligibleL taker (os[k]?.getD default)) = 1 := by
        simpa only [List.getElem!_eq_getElem?_getD] using
          (show boolWord (eligibleL taker os[k]!) = 1 by simp only [boolWord, ite_eq_left hEligible])
      frozen_select_peel [hScratch, hWord]
      simp only [fbFrame, optionTag, optionPayload, List.cons_append, List.nil_append] at hNext ⊢
      apply hNext
      · simpa only [List.length_set] using hScratch
      · simp only [bestStepL, ite_eq_left hEligible, optionTag]
        simp [List.getElem?_set, hScratch]
      all_goals simp [List.getElem?_set, hScratch]
    · have hWord : boolWord (eligibleL taker (os[k]?.getD default)) = 0 := by
        simpa only [List.getElem!_eq_getElem?_getD] using
          (show boolWord (eligibleL taker os[k]!) = 0 by simp only [boolWord, ite_eq_right hEligible])
      frozen_select_peel [hScratch, hWord]
      simp only [fbFrame, optionTag, optionPayload, List.cons_append, List.nil_append] at hNext ⊢
      apply hNext
      · simpa only [List.length_set] using hScratch
      · simp only [bestStepL, ite_eq_right hEligible, optionTag]
        simp [List.getElem?_set, hScratch]
      all_goals simp [List.getElem?_set, hScratch]
  | some j =>
    have hj := hBest j rfl
    obtain ⟨_, _, _, ⟨hPrice, hPriceB⟩, _⟩ := hElems j (hBest j rfl)
    have hjlt : UInt64.ofNat j < UInt64.ofNat os.length := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by rw [size_eq]; omega),
        UInt64.toNat_ofNat_of_lt' (by rw [size_eq]; omega)]
      exact hBest j rfl
    frozen_select_peel [fbFrame, hScratch, optionTag, hHead, hlt, hr1, hr2, hr3, hr4, hr5,
      Nat.not_lt_of_ge hHeadB, Nat.not_lt_of_ge hb1, Nat.not_lt_of_ge hb2,
      Nat.not_lt_of_ge hb3, Nat.not_lt_of_ge hb4, Nat.not_lt_of_ge hb5]
    refine wp_call_tw (func5_spec env st taker (os[k]?.getD default)) ?_
    rintro nextStore values ⟨rfl, rfl⟩
    by_cases hEligible : eligibleL taker os[k]!
    · have hWord : boolWord (eligibleL taker (os[k]?.getD default)) = 1 := by
        simpa only [List.getElem!_eq_getElem?_getD] using
          (show boolWord (eligibleL taker os[k]!) = 1 by simp only [boolWord, ite_eq_left hEligible])
      by_cases hSide : taker.oside = 0
      all_goals
        by_cases hCmp : betterPriceL taker os[k]! os[j]!
        all_goals
          have hComparison := hCmp
          simp only [betterPriceL, hSide, ite_true, ite_false, List.getElem!_eq_getElem?_getD] at hComparison
          frozen_select_peel [hScratch, hWord, hSide, hHead, hlt, hjlt, hr4, hPrice,
            optionPayload, hComparison, Nat.not_lt_of_ge hHeadB, Nat.not_lt_of_ge hb4,
            Nat.not_lt_of_ge hPriceB]
          simp only [fbFrame, hSide] at hNext
          simp only [fbFrame, optionTag, optionPayload, List.cons_append, List.nil_append] at hNext ⊢
          apply hNext
          · simpa only [List.length_set] using hScratch
          · have hDecision : (eligibleL taker os[k]! ∧ betterPriceL taker os[k]! os[j]!) ↔
                betterPriceL taker os[k]! os[j]! := ⟨And.right, fun h => ⟨hEligible, h⟩⟩
            simp only [bestStepL]
            simp only [hDecision]
            simp only [hCmp, ite_true, ite_false, optionTag]
            simp [List.getElem?_set, hScratch]
          all_goals simp [List.getElem?_set, hScratch]
    · have hWord : boolWord (eligibleL taker (os[k]?.getD default)) = 0 := by
        simpa only [List.getElem!_eq_getElem?_getD] using
          (show boolWord (eligibleL taker os[k]!) = 0 by simp only [boolWord, ite_eq_right hEligible])
      frozen_select_peel [hScratch, hWord, optionPayload]
      simp only [fbFrame, optionTag, optionPayload, List.cons_append, List.nil_append] at hNext ⊢
      apply hNext
      · simpa only [List.length_set] using hScratch
      · simp only [bestStepL, hEligible, false_and, ite_false, optionTag]
        simp [List.getElem?_set, hScratch]
      all_goals simp [List.getElem?_set, hScratch]

#print axioms select_tag_spec
end Project.ClobFindBest.Frozen.Loop
