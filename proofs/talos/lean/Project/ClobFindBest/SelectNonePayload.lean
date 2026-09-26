import Project.ClobFindBest.Candidate

namespace Project.ClobFindBest.Loop
open Wasm Project.Common Project.Clob Project.ClobFindBest
  Project.ClobFindBest.Model Project.ClobFindBest.Helpers Project.ProofKit.PackedFloatFrame

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

theorem select_none_payload_spec (env : HostEnv Unit) (st : Store Unit)
    (fuel owner ptr : UInt64) (taker : OrderL) (os : List OrderL) (k : Nat)
    (tag payload : UInt64) (scratch : List Value)
    (hScratch : scratch.length = 52)
    (h0 : scratch[0]? = some (.i64 os[k]!.oid))
    (h1 : scratch[1]? = some (.i64 os[k]!.otrader))
    (h2 : scratch[2]? = some (.i64 os[k]!.oside))
    (h3 : scratch[3]? = some (.i64 os[k]!.oprice))
    (h4 : scratch[4]? = some (.i64 os[k]!.oqty))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ next : List Value, next.length = 52 →
      next[27]? = some (.i64 (optionPayload (bestStepL os taker k none))) →
      next[26]? = scratch[26]? →
      wp module rest Q st (fbFrame fuel owner ptr taker k none tag payload 0 next) env) :
    wp module ((stepCode.drop 60).take 5 ++ rest) Q st
      (fbFrame fuel owner ptr taker k none tag payload 0 scratch) env := by
  unfold stepCode loopCode func7
  dsimp only
  wp_packed_frame [fbFrame, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch]
  norm_num
  refine wp_iff_cons rfl ?_
  rw [ite_eq_left (by simp [optionTag])]
  wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch]
  norm_num [UInt64.toNat_ofNat, h0, h1, h2, h3, h4, List.getElem!_eq_getElem?_getD]
  refine wp_call_tw (func5_spec env st taker (os[k]?.getD default)) ?_
  rintro nextStore values ⟨rfl, rfl⟩
  by_cases hEligible : eligibleL taker os[k]!
  · have hWord : boolWord (eligibleL taker (os[k]?.getD default)) = 1 := by
      simpa only [List.getElem!_eq_getElem?_getD] using (show boolWord (eligibleL taker os[k]!) = 1 by simp only [boolWord, ite_eq_left hEligible])
    wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch, hWord]
    norm_num
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by decide)]
    wp_packed_frame []
    norm_num
    refine wp_iff_cons rfl ?_
    rw [ite_eq_left (by decide)]
    wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch]
    apply hNext
    · simpa only [List.length_set] using hScratch
    · simp only [bestStepL, ite_eq_left hEligible, optionPayload]
      simp [List.getElem?_set, hScratch]
    all_goals simp [List.getElem?_set, hScratch]
  · have hWord : boolWord (eligibleL taker (os[k]?.getD default)) = 0 := by
      simpa only [List.getElem!_eq_getElem?_getD] using (show boolWord (eligibleL taker os[k]!) = 0 by simp only [boolWord, ite_eq_right hEligible])
    wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch, hWord]
    norm_num
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide)]
    wp_packed_frame []
    norm_num
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by decide)]
    wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch]
    apply hNext
    · simpa only [List.length_set] using hScratch
    · simp only [bestStepL, ite_eq_right hEligible, optionPayload]
      simp [List.getElem?_set, hScratch]
    all_goals simp [List.getElem?_set, hScratch]

#print axioms select_none_payload_spec
end Project.ClobFindBest.Loop
