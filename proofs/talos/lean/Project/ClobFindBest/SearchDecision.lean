import Project.ClobFindBest.SearchFrame

namespace Project.ClobFindBest.SearchDecision
open Wasm Project.Common Project.Clob Project.ClobFindBest.Model
  Project.ClobFindBest.Helpers Project.ClobFindBest.SearchFrame Project.ClobFindBest.SearchProgram

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

def selectedWord (tag : Bool) (best : Option Nat) : UInt64 :=
  if tag then optionTag best else optionPayload best

theorem decision_spec (m : Wasm.Module) (env : HostEnv Unit) (st : Store Unit)
    (eligibleId : Nat) (tag : Bool) (base : Locals) (fuel owner ptr : UInt64)
    (os : List OrderL) (taker : OrderL) (k : Nat) (best : Option Nat)
    (hParams : base.params = params fuel owner ptr taker k best)
    (hLocals : base.locals.length = 56) (hValues : base.values = [])
    (hCandidate : Candidate base os[k]!)
    (hLength : os.length < 4294967296) (hk : k < os.length)
    (hBest : ∀ j, best = some j → j < k) (hInput : OrdersAt st ptr os)
    (hEligible : TerminatesWith env m eligibleId st
      [.i64 os[k]!.oqty, .i64 os[k]!.oprice, .i64 os[k]!.oside,
        .i64 os[k]!.otrader, .i64 os[k]!.oid, .i64 taker.oqty, .i64 taker.oprice,
        .i64 taker.oside, .i64 taker.otrader, .i64 taker.oid]
      (fun st1 vs => vs = [.i64 (boolWord (eligibleL taker os[k]!))] ∧ st1 = st))
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ final, DecisionFrame base final (selectedWord tag (bestStepL os taker k best)) →
      wp m rest Q st final env) :
    wp m (decision tag eligibleId ++ rest) Q st base env := by
  have hOid := getElem_of_some hCandidate.oid
  have hTrader := getElem_of_some hCandidate.trader
  have hSide := getElem_of_some hCandidate.side
  have hPrice := getElem_of_some hCandidate.price
  have hQty := getElem_of_some hCandidate.qty
  cases best with
  | none =>
    simp only [decision, List.cons_append, List.nil_append]
    wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hOid, hTrader, hSide, hPrice, hQty]
    simp only [← List.getElem!_eq_getElem?_getD]
    refine wp_call_tw hEligible ?_
    rintro st1 vs ⟨rfl, rfl⟩
    by_cases hMatch : eligibleL taker os[k]!
    · simp only [boolWord, if_pos hMatch]
      wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues]
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues]
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      cases tag <;> wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues]
      all_goals
        apply hNext
        refine ⟨hParams.symm, by simp [List.length_set, hLocals], ?_, ?_⟩
        · simp only [List.getElem!_eq_getElem?_getD] at hMatch
          simp [selectedWord, bestStepL, betterPriceL, hMatch, optionTag, optionPayload] <;> try rw [if_pos hMatch]
        · intro i hi
          simp (discharger := omega) [List.getElem?_set, hLocals]
    · simp only [boolWord, if_neg hMatch]
      wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues]
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues]
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues]
      apply hNext
      refine ⟨hParams.symm, by simp [List.length_set, hLocals], ?_, ?_⟩
      · simp only [List.getElem!_eq_getElem?_getD] at hMatch
        cases tag <;> simp [selectedWord, bestStepL, hMatch, optionTag, optionPayload] <;> try rw [if_pos hMatch]
      · intro i hi
        simp (discharger := omega) [List.getElem?_set, hLocals]
  | some j =>
    have hj := hBest j rfl
    have hjlt : UInt64.ofNat j < UInt64.ofNat os.length := by
      rw [UInt64.lt_iff_toNat_lt, toNat_ofNat_lt (by rw [size_eq]; omega),
        toNat_ofNat_lt (by rw [size_eq]; omega)]
      omega
    have hjU : (UInt64.ofNat j).toNat = j := by u64_omega
    have hHead := hInput.1.1
    have hHeadB := hInput.1.2
    have hRead := (hInput.2 j (by omega)).2.2.2.1.1
    have hReadB := (hInput.2 j (by omega)).2.2.2.1.2
    have hSafeHead := Nat.not_lt.mpr hHeadB
    have hSafeRead := Nat.not_lt.mpr hReadB
    simp only [decision, List.cons_append, List.nil_append]
    wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hOid, hTrader, hSide, hPrice, hQty]
    simp only [← List.getElem!_eq_getElem?_getD]
    refine wp_call_tw hEligible ?_
    rintro st1 vs ⟨rfl, rfl⟩
    by_cases hMatch : eligibleL taker os[k]!
    · simp only [boolWord, if_pos hMatch]
      wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues]
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues]
      by_cases hBuy : taker.oside = 0
      · rw [if_pos hBuy]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp [hjlt])]
        wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
        simp only [← List.getElem!_eq_getElem?_getD]
        by_cases hBetter : os[k]!.oprice < os[j]!.oprice
        · rw [if_pos hBetter]
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          cases tag <;> wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          all_goals
            apply hNext
            refine ⟨hParams.symm, by simp [List.length_set, hLocals], ?_, ?_⟩
            · simp only [List.getElem!_eq_getElem?_getD] at hMatch hBetter
              simp [selectedWord, bestStepL, betterPriceL, hMatch, hBuy, hBetter, optionTag, optionPayload] <;> try rw [if_pos hMatch]
            · intro i hi
              simp (discharger := omega) [List.getElem?_set, hLocals]
        · rw [if_neg hBetter]
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          cases tag <;> wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          all_goals
            apply hNext
            refine ⟨hParams.symm, by simp [List.length_set, hLocals], ?_, ?_⟩
            · simp only [List.getElem!_eq_getElem?_getD] at hMatch hBetter
              simp [selectedWord, bestStepL, betterPriceL, hMatch, hBuy, hBetter, optionTag, optionPayload] <;> try rw [if_pos hMatch]
            · intro i hi
              simp (discharger := omega) [List.getElem?_set, hLocals]
      · rw [if_neg hBuy]
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp [hjlt])]
        wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
        simp only [← List.getElem!_eq_getElem?_getD]
        by_cases hBetter : os[j]!.oprice < os[k]!.oprice
        · rw [if_pos hBetter]
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          cases tag <;> wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          all_goals
            apply hNext
            refine ⟨hParams.symm, by simp [List.length_set, hLocals], ?_, ?_⟩
            · simp only [List.getElem!_eq_getElem?_getD] at hMatch hBetter
              simp [selectedWord, bestStepL, betterPriceL, hMatch, hBuy, hBetter, optionTag, optionPayload] <;> try rw [if_pos hMatch]
            · intro i hi
              simp (discharger := omega) [List.getElem?_set, hLocals]
        · rw [if_neg hBetter]
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          cases tag <;> wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
          all_goals
            apply hNext
            refine ⟨hParams.symm, by simp [List.length_set, hLocals], ?_, ?_⟩
            · simp only [List.getElem!_eq_getElem?_getD] at hMatch hBetter
              simp [selectedWord, bestStepL, betterPriceL, hMatch, hBuy, hBetter, optionTag, optionPayload] <;> try rw [if_pos hMatch]
            · intro i hi
              simp (discharger := omega) [List.getElem?_set, hLocals]
    · simp only [boolWord, if_neg hMatch]
      wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues]
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues]
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
      cases tag <;> wp_run_with [hParams, params, optionTag, optionPayload, hLocals, hValues, hPrice, hjU, hHead, hRead, hSafeHead, hSafeRead]
      all_goals
        apply hNext
        refine ⟨hParams.symm, by simp [List.length_set, hLocals], ?_, ?_⟩
        · simp only [List.getElem!_eq_getElem?_getD] at hMatch
          simp [selectedWord, bestStepL, betterPriceL, hMatch, optionTag, optionPayload] <;> try rw [if_pos hMatch]
        · intro i hi
          simp (discharger := omega) [List.getElem?_set, hLocals]

end Project.ClobFindBest.SearchDecision
