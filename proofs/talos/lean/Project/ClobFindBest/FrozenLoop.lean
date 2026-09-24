import Project.ClobFindBest.FrozenStep

namespace Project.ClobFindBest.Frozen.Loop
open Wasm Project.Common Project.Clob Project.ClobFindBest
  Project.ClobFindBest.Frozen.Model Project.ClobFindBest.Frozen.Helpers Project.ProofKit.PackedFloatFrame

set_option maxHeartbeats 64000000
set_option maxRecDepth 100000

theorem func7_spec_owner (env : HostEnv Unit) (st : Store Unit) (owner ptr : UInt64)
    (os : List OrderL) (taker : OrderL)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os) :
    TerminatesWith (m := «module») (id := 7) (initial := st) (env := env)
      [.i64 0, .i64 0, .i64 0, .i64 taker.oqty, .i64 taker.oprice,
       .i64 taker.oside, .i64 taker.otrader, .i64 taker.oid, .i64 ptr,
       .i64 owner, .i64 (UInt64.ofNat (os.length+1))]
      (fun st' vs => vs = optionVals (findBestL os taker) ∧ st' = st) := by
  obtain ⟨⟨hHead, hHeadB⟩, hElems⟩ := hInput
  have hlenU : (UInt64.ofNat os.length).toNat = os.length := by u64_omega
  refine TerminatesWith.of_wp_entry_for (f := func7Def) rfl ?_ (by decide)
  change wp «module» func7 _ st (func7Def.toLocals _) env
  unfold func7
  wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, func7Def]
  norm_num
  apply wp_block_cons
  apply wp_loop_cons (Inv := fbInv st owner ptr os taker) (μ := fbMeasure)
  · refine ⟨rfl, 0, Nat.zero_le _, UInt64.ofNat (os.length+1), 0, 0, 0,
      List.replicate 44 (.i64 0), by simp, ?_, Or.inl ⟨rfl, rfl⟩⟩
    simp [fbFrame, bestPrefixL, optionTag, optionPayload, List.replicate]
  · rintro st2 s ⟨rfl, k, hk, fuel, tag, payload, done, scratch, hScratch, rfl, hState⟩
    rcases hState with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, fbFrame]
      have hfuel_ne : UInt64.ofNat (os.length+1-k) ≠ 0 := by
        intro h
        have hz := congrArg UInt64.toNat h
        rw [toNat_ofNat_lt (by rw [size_eq]; omega)] at hz
        simp at hz
        omega
      refine wp_iff_cons rfl ?_
      rw [ite_eq_left (by simp [hfuel_ne])]
      wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch]
      norm_num
      rw [hHead]
      refine ⟨hHeadB, ?_⟩
      refine wp_iff_cons rfl ?_
      by_cases hEnd : k = os.length
      · subst k
        rw [ite_eq_right (by simp)]
        wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch]
        norm_num
        constructor
        · refine ⟨rfl, os.length, Nat.le_refl _, _, _, _, 1, _, ?_, rfl,
            Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
          simpa only [List.length_set] using hScratch
        · simp [fbMeasure]
      · have hklt : k < os.length := by omega
        have hkU : (UInt64.ofNat k).toNat = k := by u64_omega
        have hlt : UInt64.ofNat k < UInt64.ofNat os.length := by
          rw [UInt64.lt_iff_toNat_lt, hlenU,
            toNat_ofNat_lt (by rw [size_eq]; omega)]
          exact hklt
        have hkadd : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
          apply UInt64.toNat.inj
          rw [toNat_add_one (by rw [hkU, size_eq]; omega), hkU,
            toNat_ofNat_lt (by rw [size_eq]; omega)]
        have hfuel_next :
            UInt64.ofNat (os.length + 1 - k) - 1 =
              UInt64.ofNat (os.length + 1 - (k + 1)) := by
          have hstep : UInt64.ofNat (os.length + 1 - k) =
              UInt64.ofNat (os.length + 1 - (k + 1)) + 1 := by
            apply UInt64.toNat.inj
            rw [toNat_ofNat_lt (by rw [size_eq]; omega), toNat_add_one,
              toNat_ofNat_lt (by rw [size_eq]; omega)]
            · omega
            · rw [toNat_ofNat_lt (by rw [size_eq]; omega), size_eq]
              omega
          rw [hstep]
          simp
        rw [ite_eq_left (by simp [hHead, hlt])]
        change wp module stepCode _ st2
          (fbFrame (UInt64.ofNat (os.length+1-k)) owner ptr taker k
            (bestPrefixL os taker k) tag payload 0
            (scratch.set 41 (.i64 ptr))) env
        have hEmpty : stepCode = stepCode ++ [] := by simp
        rw [hEmpty]
        apply step_spec env st2 (UInt64.ofNat (os.length+1-k)) owner ptr taker os k
          (bestPrefixL os taker k) tag payload _ hlen ⟨⟨hHead, hHeadB⟩, hElems⟩ hklt
          (fun j h => Nat.lt_of_lt_of_le (bestPrefixL_some_lt os taker k j h) hk)
          (by simpa only [List.length_set] using hScratch)
        intro next hNext
        wp_packed_frame [fbFrame]
        norm_num
        rw [hfuel_next]
        try rw [hkadd]
        constructor
        · refine ⟨rfl, k+1, by omega, _, tag, payload, 0, next, hNext, ?_, Or.inl ⟨rfl, rfl⟩⟩
          rfl
        · simp only [fbMeasure]
          rw [toNat_ofNat_lt, toNat_ofNat_lt]
          · omega
          · rw [size_eq]; omega
          · rw [size_eq]; omega
    · wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, fbFrame]
      refine wp_iff_cons rfl ?_
      by_cases hfz : fuel = 0
      · rw [ite_eq_right (by simp [hfz])]
        wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch]
        norm_num
        refine wp_iff_cons rfl ?_
        rw [ite_eq_right (by simp)]
        wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch]
        norm_num
        simp [func7Def, optionVals, findBestL_eq_prefix]
      · rw [ite_eq_left (by simp [hfz])]
        wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch]
        norm_num
        refine wp_iff_cons rfl ?_
        rw [ite_eq_right (by simp)]
        wp_packed_frame [List.set, List.getElem?_cons_zero, List.getElem?_cons_succ, hScratch]
        norm_num
        simp [func7Def, optionVals, findBestL_eq_prefix]

theorem func7_spec (env : HostEnv Unit) (st : Store Unit) (ptr : UInt64)
    (os : List OrderL) (taker : OrderL)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os) :
    TerminatesWith (m := «module») (id := 7) (initial := st) (env := env)
      [.i64 0, .i64 0, .i64 0, .i64 taker.oqty, .i64 taker.oprice,
       .i64 taker.oside, .i64 taker.otrader, .i64 taker.oid, .i64 ptr,
       .i64 0, .i64 (UInt64.ofNat (os.length+1))]
      (fun st' vs => vs = optionVals (findBestL os taker) ∧ st' = st) :=
  func7_spec_owner env st 0 ptr os taker hlen hInput

end Project.ClobFindBest.Frozen.Loop
