import Project.ClobMatchFuel.Helpers
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# The embedded `findBest` fuel loop

The loop carries the best index selected from the consumed prefix.  Its fuel
is the array length plus one minus the cursor, which leaves one final
iteration to copy the result and set the done flag.
-/

namespace Project.ClobMatchFuel.FindBest

open Wasm Project.Common Project.Clob Project.ClobMatchFuel
  Project.ClobFindBest.Model Project.ClobMatchFuel.Helpers

set_option maxHeartbeats 64000000
set_option maxRecDepth 100000

macro "mf_read_candidate_tail " hHead:ident hHeadB:ident hlt:ident
    hb1:ident hb2:ident hb3:ident hb4:ident hb5:ident : tactic => `(tactic|
  (refine ⟨$hHeadB, ?_⟩
   rw [($hHead)]
   refine wp_iff_cons rfl ?_
   rw [if_pos (by simpa using $hlt)]
   norm_num
   refine ⟨$hb1, ?_⟩
   norm_num
   rw [($hHead)]
   refine ⟨$hHeadB, ?_⟩
   refine wp_iff_cons rfl ?_
   rw [if_pos (by simpa using $hlt)]
   norm_num
   refine ⟨$hb2, ?_⟩
   norm_num
   rw [($hHead)]
   refine ⟨$hHeadB, ?_⟩
   refine wp_iff_cons rfl ?_
   rw [if_pos (by simpa using $hlt)]
   norm_num
   refine ⟨$hb3, ?_⟩
   norm_num
   rw [($hHead)]
   refine ⟨$hHeadB, ?_⟩
   refine wp_iff_cons rfl ?_
   rw [if_pos (by simpa using $hlt)]
   norm_num
   refine ⟨$hb4, ?_⟩
   norm_num
   rw [($hHead)]
   refine ⟨$hHeadB, ?_⟩
   refine wp_iff_cons rfl ?_
   rw [if_pos (by simpa using $hlt)]
   norm_num
   refine ⟨$hb5, ?_⟩
   norm_num))

private def mfFrame (fuel owner ptr : UInt64) (taker : OrderL) (k : Nat)
    (best : Option Nat) (rTag rPayload done
      s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29
      s30 s31 s32 s33 s34 s35 s36 s37 s38 s39 s40 s41 s42 s43 s44 s45
      s46 s47 s48 s49 s50 s51 s52 s53 s54 s55 s56 s57 : UInt64) : Locals :=
  { params := [.i64 fuel, .i64 owner, .i64 ptr, .i64 taker.oid,
      .i64 taker.otrader, .i64 taker.oside, .i64 taker.oprice,
      .i64 taker.oqty, .i64 (UInt64.ofNat k), .i64 (optionTag best),
      .i64 (optionPayload best)],
    locals := [.i64 rTag, .i64 rPayload, .i64 done,
      .i64 s14, .i64 s15, .i64 s16, .i64 s17, .i64 s18, .i64 s19,
      .i64 s20, .i64 s21, .i64 s22, .i64 s23, .i64 s24, .i64 s25,
      .i64 s26, .i64 s27, .i64 s28, .i64 s29, .i64 s30, .i64 s31,
      .i64 s32, .i64 s33, .i64 s34, .i64 s35, .i64 s36, .i64 s37,
      .i64 s38, .i64 s39, .i64 s40, .i64 s41, .i64 s42, .i64 s43,
      .i64 s44, .i64 s45, .i64 s46, .i64 s47, .i64 s48, .i64 s49,
      .i64 s50, .i64 s51, .i64 s52, .i64 s53, .i64 s54, .i64 s55,
      .i64 s56, .i64 s57],
    values := [] }

private def mfInv (st0 : Store Unit) (owner ptr : UInt64)
    (os : List OrderL) (taker : OrderL) : AssertionF Unit :=
  fun st s =>
    st = st0 ∧
    ∃ k : Nat, k ≤ os.length ∧
    ∃ fuel rTag rPayload done
      s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29
      s30 s31 s32 s33 s34 s35 s36 s37 s38 s39 s40 s41 s42 s43 s44 s45
      s46 s47 s48 s49 s50 s51 s52 s53 s54 s55 s56 s57 : UInt64,
      s = mfFrame fuel owner ptr taker k (bestPrefixL os taker k)
        rTag rPayload done s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24
        s25 s26 s27 s28 s29 s30 s31 s32 s33 s34 s35 s36 s37 s38 s39
        s40 s41 s42 s43 s44 s45 s46 s47 s48 s49 s50 s51 s52 s53 s54
        s55 s56 s57 ∧
      ((done = 0 ∧ fuel = UInt64.ofNat (os.length + 1 - k)) ∨
        (done = 1 ∧ k = os.length ∧
          rTag = optionTag (bestPrefixL os taker os.length) ∧
          rPayload = optionPayload (bestPrefixL os taker os.length)))

private def mfMeasure (_ : Store Unit) (s : Locals) : Nat :=
  match s.params, s.locals with
  | .i64 fuel :: _, _ :: _ :: .i64 done :: _ =>
      2 * fuel.toNat + (if done = 0 then 1 else 0)
  | _, _ => 0

private theorem mfInv_some_step (st : Store Unit) (owner ptr : UInt64)
    (os : List OrderL) (taker : OrderL) (k selected lastRead : Nat)
    (candidate : OrderL)
    {rTag rPayload s22 s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 : UInt64}
    (hk : k + 1 ≤ os.length)
    (hnext : bestPrefixL os taker (k + 1) = some selected) :
    mfInv st owner ptr os taker st
      (mfFrame (UInt64.ofNat (os.length + 1 - (k + 1))) owner ptr taker (k + 1)
        (some selected) rTag rPayload 0
        owner ptr taker.oid taker.otrader taker.oside taker.oprice taker.oqty
        (UInt64.ofNat (k + 1))
        s22 s23 s24 s25 s26 s27 s28 s29 s30 s31 s32
        taker.oid taker.otrader taker.oside taker.oprice taker.oqty
        candidate.oid candidate.otrader candidate.oside candidate.oprice
        candidate.oqty 1 (UInt64.ofNat selected) owner ptr taker.oid
        taker.otrader taker.oside taker.oprice taker.oqty
        (UInt64.ofNat (k + 1)) 1 (UInt64.ofNat selected) ptr
        (UInt64.ofNat lastRead) (UInt64.ofNat (k + 1))) := by
  unfold mfInv
  refine ⟨rfl, k + 1, hk,
    UInt64.ofNat (os.length + 1 - (k + 1)), rTag, rPayload, 0,
    owner, ptr, taker.oid, taker.otrader, taker.oside, taker.oprice, taker.oqty,
    UInt64.ofNat (k + 1),
    s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32,
    taker.oid, taker.otrader, taker.oside, taker.oprice, taker.oqty,
    candidate.oid, candidate.otrader, candidate.oside, candidate.oprice,
    candidate.oqty, 1, UInt64.ofNat selected, owner, ptr, taker.oid,
    taker.otrader, taker.oside, taker.oprice, taker.oqty,
    UInt64.ofNat (k + 1), 1, UInt64.ofNat selected, ptr,
    UInt64.ofNat lastRead, UInt64.ofNat (k + 1), ?_, Or.inl ⟨rfl, rfl⟩⟩
  simp only [hnext]

/-- The generated matching artifact fuel loop returns the source search result and preserves the
store. -/
theorem func8_spec_owner (env : HostEnv Unit) (st : Store Unit)
    (owner ptr : UInt64) (os : List OrderL) (taker : OrderL)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os) :
    TerminatesWith (m := «module») (id := 8) (initial := st) (env := env)
      [.i64 0, .i64 0, .i64 0, .i64 taker.oqty, .i64 taker.oprice,
       .i64 taker.oside, .i64 taker.otrader, .i64 taker.oid, .i64 ptr,
       .i64 owner, .i64 (UInt64.ofNat (os.length + 1))]
      (fun st' vs => vs = optionVals (findBestL os taker) ∧ st' = st) := by
  obtain ⟨⟨hHead, hHeadB⟩, hElems⟩ := hInput
  have hlenU : (UInt64.ofNat os.length).toNat = os.length :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  apply TerminatesWith.of_wp_entry_for (f := func8Def)
  · simp [«module»]
  · change wp «module» func8 _ st
      { params := [.i64 (UInt64.ofNat (os.length + 1)), .i64 owner, .i64 ptr,
          .i64 taker.oid, .i64 taker.otrader, .i64 taker.oside,
          .i64 taker.oprice, .i64 taker.oqty, .i64 0, .i64 0, .i64 0],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func8
    wp_run
    apply wp_block_cons
    apply wp_loop_cons (Inv := mfInv st owner ptr os taker) (μ := mfMeasure)
    · refine ⟨rfl, 0, Nat.zero_le _, UInt64.ofNat (os.length + 1), 0, 0, 0, ?_⟩
      repeat' apply Exists.intro 0
      refine ⟨?_, Or.inl ⟨rfl, ?_⟩⟩
      · simp [mfFrame, bestPrefixL, optionTag, optionPayload]
      · rfl
    · rintro st2 s ⟨rfl, k, hk, fuel, rTag, rPayload, done,
        s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25,
        s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37,
        s38, s39, s40, s41, s42, s43, s44, s45, s46, s47, s48, s49,
        s50, s51, s52, s53, s54, s55, s56, s57, rfl, hstate⟩
      rcases hstate with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
      · simp [mfFrame]
        have hfuel_ne : UInt64.ofNat (os.length + 1 - k) ≠ 0 := by
          intro h
          have hz := congrArg UInt64.toNat h
          rw [toNat_ofNat_lt (by rw [size_eq]; omega)] at hz
          simp at hz
          omega
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp [hfuel_ne])]
        norm_num
        rw [hHead]
        refine ⟨hHeadB, ?_⟩
        refine wp_iff_cons rfl ?_
        by_cases hkend : k = os.length
        · have hnlt : ¬ UInt64.ofNat k < UInt64.ofNat os.length := by
            rw [UInt64.lt_iff_toNat_lt, hlenU,
              toNat_ofNat_lt (by rw [size_eq]; omega)]
            omega
          rw [if_neg (by simp [hnlt])]
          wp_run
          subst k
          refine ⟨⟨rfl, os.length, Nat.le_refl _,
            UInt64.ofNat (os.length + 1 - os.length),
            optionTag (bestPrefixL os taker os.length),
            optionPayload (bestPrefixL os taker os.length), 1,
            s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25,
            s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37,
            s38, s39, s40, s41, s42, s43, s44, s45, s46, s47, s48, s49,
            s50, s51, s52, s53, s54, ptr, s56, s57, ?_,
            Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩, ?_⟩
          · simp [mfFrame]
          · simp [mfMeasure]
        · have hklt : k < os.length := Nat.lt_of_le_of_ne hk hkend
          have hkU : (UInt64.ofNat k).toNat = k :=
            toNat_ofNat_lt (by rw [size_eq]; omega)
          have hlt : UInt64.ofNat k < UInt64.ofNat os.length := by
            rw [UInt64.lt_iff_toNat_lt, hlenU,
              toNat_ofNat_lt (by rw [size_eq]; omega)]
            exact hklt
          have hkadd : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
            apply UInt64.toNat.inj
            rw [toNat_add_one (by rw [hkU, size_eq]; omega), hkU,
              toNat_ofNat_lt (by rw [size_eq]; omega)]
          have hsucc_no_wrap : ¬ UInt64.ofNat k + 1 < UInt64.ofNat k := by
            rw [UInt64.lt_iff_toNat_lt,
              toNat_add_one (by rw [hkU, size_eq]; omega), hkU]
            omega
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
          obtain ⟨⟨hr1, hb1⟩, ⟨hr2, hb2⟩, ⟨hr3, hb3⟩, ⟨hr4, hb4⟩,
            ⟨hr5, hb5⟩⟩ := hElems k hklt
          rw [if_pos (by simp [hlt])]
          norm_num
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp [hsucc_no_wrap])]
          norm_num
          refine wp_iff_cons rfl ?_
          cases hbest : bestPrefixL os taker k with
          | none =>
              rw [if_pos (by simp [optionTag])]
              norm_num
              rw [hHead]
              refine ⟨hHeadB, ?_⟩
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp [hlt])]
              norm_num
              refine ⟨hb1, ?_⟩
              rw [hHead]
              refine ⟨hHeadB, ?_⟩
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp [hlt])]
              norm_num
              refine ⟨hb2, ?_⟩
              rw [hHead]
              refine ⟨hHeadB, ?_⟩
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp [hlt])]
              norm_num
              refine ⟨hb3, ?_⟩
              rw [hHead]
              refine ⟨hHeadB, ?_⟩
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp [hlt])]
              norm_num
              refine ⟨hb4, ?_⟩
              rw [hHead]
              refine ⟨hHeadB, ?_⟩
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp [hlt])]
              norm_num
              refine ⟨hb5, ?_⟩
              let maker : OrderL := {
                oid := st2.mem.read64 (UInt32.ofNat ((ptr.toNat +
                  (k * (5 : UInt64).toNat + (1 : UInt64).toNat) *
                    (8 : UInt64).toNat) % 4294967296))
                otrader := st2.mem.read64 (UInt32.ofNat ((ptr.toNat +
                  (k * (5 : UInt64).toNat + (2 : UInt64).toNat) *
                    (8 : UInt64).toNat) % 4294967296))
                oside := st2.mem.read64 (UInt32.ofNat ((ptr.toNat +
                  (k * (5 : UInt64).toNat + (3 : UInt64).toNat) *
                    (8 : UInt64).toNat) % 4294967296))
                oprice := st2.mem.read64 (UInt32.ofNat ((ptr.toNat +
                  (k * (5 : UInt64).toNat + (4 : UInt64).toNat) *
                    (8 : UInt64).toNat) % 4294967296))
                oqty := st2.mem.read64 (UInt32.ofNat ((ptr.toNat +
                  (k * (5 : UInt64).toNat + (5 : UInt64).toNat) *
                    (8 : UInt64).toNat) % 4294967296)) }
              have hmaker : maker = os[k]! := by
                rcases horder : os[k]! with ⟨oid, trader, side, price, qty⟩
                simp only [horder] at hr1 hr2 hr3 hr4 hr5 ⊢
                simp [maker, hr1, hr2, hr3, hr4, hr5]
              refine wp_call_tw (func6_spec env st2 taker maker) ?_
              rintro st3 vs ⟨rfl, rfl⟩
              rw [hmaker]
              by_cases helig : eligibleL taker os[k]!
              · simp only [boolWord, if_pos helig]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp)]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp)]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp [optionTag])]
                norm_num
                refine ⟨hHeadB, ?_⟩
                rw [hHead]
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp [hlt])]
                norm_num
                refine ⟨hb1, ?_⟩
                rw [hHead]
                refine ⟨hHeadB, ?_⟩
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp [hlt])]
                norm_num
                refine ⟨hb2, ?_⟩
                rw [hHead]
                refine ⟨hHeadB, ?_⟩
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp [hlt])]
                norm_num
                refine ⟨hb3, ?_⟩
                rw [hHead]
                refine ⟨hHeadB, ?_⟩
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp [hlt])]
                norm_num
                refine ⟨hb4, ?_⟩
                rw [hHead]
                refine ⟨hHeadB, ?_⟩
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp [hlt])]
                norm_num
                refine ⟨hb5, ?_⟩
                refine wp_call_tw (func6_spec env st3 taker maker) ?_
                rintro st4 vs ⟨rfl, rfl⟩
                rw [hmaker]
                simp only [boolWord, if_pos helig]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp)]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp)]
                norm_num
                have hnext : bestPrefixL os taker (k + 1) = some k := by
                  simp only [bestPrefixL, hbest, bestStepL, if_pos helig]
                constructor
                · rw [hfuel_next, hkadd]
                  unfold mfInv
                  refine ⟨rfl, k + 1, by omega,
                    UInt64.ofNat (os.length + 1 - (k + 1)), rTag, rPayload, 0,
                    owner, ptr, taker.oid, taker.otrader, taker.oside,
                    taker.oprice, taker.oqty, UInt64.ofNat (k + 1),
                    taker.oid, taker.otrader, taker.oside, taker.oprice,
                    taker.oqty, maker.oid, maker.otrader, maker.oside,
                    maker.oprice, maker.oqty, 1, s33, s34, s35, s36, s37,
                    s38, s39, s40, s41, s42, 1, UInt64.ofNat k, owner, ptr,
                    taker.oid, taker.otrader, taker.oside, taker.oprice,
                    taker.oqty, UInt64.ofNat (k + 1), 1, UInt64.ofNat k,
                    ptr, UInt64.ofNat k, UInt64.ofNat (k + 1), ?_,
                    Or.inl ⟨rfl, rfl⟩⟩
                  simp only [mfFrame, hnext, optionTag, optionPayload, maker]
                · simp only [mfMeasure]
                  rw [hfuel_next, toNat_ofNat_lt, toNat_ofNat_lt]
                  · omega
                  · rw [size_eq]
                    omega
                  · rw [size_eq]
                    omega
              · simp only [boolWord, if_neg helig]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_neg (by simp)]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_neg (by simp)]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp [optionTag])]
                norm_num
                refine ⟨hHeadB, ?_⟩
                rw [hHead]
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp [hlt])]
                norm_num
                refine ⟨hb1, ?_⟩
                rw [hHead]
                refine ⟨hHeadB, ?_⟩
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp [hlt])]
                norm_num
                refine ⟨hb2, ?_⟩
                rw [hHead]
                refine ⟨hHeadB, ?_⟩
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp [hlt])]
                norm_num
                refine ⟨hb3, ?_⟩
                rw [hHead]
                refine ⟨hHeadB, ?_⟩
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp [hlt])]
                norm_num
                refine ⟨hb4, ?_⟩
                rw [hHead]
                refine ⟨hHeadB, ?_⟩
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp [hlt])]
                norm_num
                refine ⟨hb5, ?_⟩
                refine wp_call_tw (func6_spec env st3 taker maker) ?_
                rintro st4 vs ⟨rfl, rfl⟩
                rw [hmaker]
                simp only [boolWord, if_neg helig]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_neg (by simp)]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_neg (by simp)]
                norm_num
                have hnext : bestPrefixL os taker (k + 1) = none := by
                  simp only [bestPrefixL, hbest, bestStepL, if_neg helig]
                constructor
                · rw [hfuel_next, hkadd]
                  unfold mfInv
                  refine ⟨rfl, k + 1, by omega,
                    UInt64.ofNat (os.length + 1 - (k + 1)), rTag, rPayload, 0,
                    owner, ptr, taker.oid, taker.otrader, taker.oside,
                    taker.oprice, taker.oqty, UInt64.ofNat (k + 1),
                    taker.oid, taker.otrader, taker.oside, taker.oprice,
                    taker.oqty, maker.oid, maker.otrader, maker.oside,
                    maker.oprice, maker.oqty, 0, s33, s34, s35, s36, s37,
                    s38, s39, s40, s41, s42, 0, 0, owner, ptr, taker.oid,
                    taker.otrader, taker.oside, taker.oprice, taker.oqty,
                    UInt64.ofNat (k + 1), 0, 0, ptr, UInt64.ofNat k,
                    UInt64.ofNat (k + 1), ?_, Or.inl ⟨rfl, rfl⟩⟩
                  simp only [mfFrame, hnext, optionTag, optionPayload, maker]
                · simp only [mfMeasure]
                  rw [hfuel_next, toNat_ofNat_lt, toNat_ofNat_lt]
                  · omega
                  · rw [size_eq]
                    omega
                  · rw [size_eq]
                    omega
          | some j =>
              rw [if_neg (by simp [optionTag])]
              norm_num
              have hjlt : j < k := bestPrefixL_some_lt os taker k j hbest
              have hjlen : j < os.length := lt_trans hjlt hklt
              have hjU : (UInt64.ofNat j).toNat = j :=
                toNat_ofNat_lt (by rw [size_eq]; omega)
              have hjltU : UInt64.ofNat j < UInt64.ofNat os.length := by
                rw [UInt64.lt_iff_toNat_lt, hlenU, hjU]
                exact hjlen
              have hjPayload : optionPayload (some j) = UInt64.ofNat j := rfl
              obtain ⟨⟨jr1, jb1⟩, ⟨jr2, jb2⟩, ⟨jr3, jb3⟩, ⟨jr4, jb4⟩,
                ⟨jr5, jb5⟩⟩ := hElems j hjlen
              refine ⟨hHeadB, ?_⟩
              rw [hHead]
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp [hlt])]
              norm_num
              refine ⟨hb1, ?_⟩
              rw [hHead]
              refine ⟨hHeadB, ?_⟩
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp [hlt])]
              norm_num
              refine ⟨hb2, ?_⟩
              rw [hHead]
              refine ⟨hHeadB, ?_⟩
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp [hlt])]
              norm_num
              refine ⟨hb3, ?_⟩
              rw [hHead]
              refine ⟨hHeadB, ?_⟩
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp [hlt])]
              norm_num
              refine ⟨hb4, ?_⟩
              rw [hHead]
              refine ⟨hHeadB, ?_⟩
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp [hlt])]
              norm_num
              refine ⟨hb5, ?_⟩
              let candidate : OrderL := {
                oid := st2.mem.read64 (UInt32.ofNat ((ptr.toNat +
                  (k * (5 : UInt64).toNat + (1 : UInt64).toNat) *
                    (8 : UInt64).toNat) % 4294967296))
                otrader := st2.mem.read64 (UInt32.ofNat ((ptr.toNat +
                  (k * (5 : UInt64).toNat + (2 : UInt64).toNat) *
                    (8 : UInt64).toNat) % 4294967296))
                oside := st2.mem.read64 (UInt32.ofNat ((ptr.toNat +
                  (k * (5 : UInt64).toNat + (3 : UInt64).toNat) *
                    (8 : UInt64).toNat) % 4294967296))
                oprice := st2.mem.read64 (UInt32.ofNat ((ptr.toNat +
                  (k * (5 : UInt64).toNat + (4 : UInt64).toNat) *
                    (8 : UInt64).toNat) % 4294967296))
                oqty := st2.mem.read64 (UInt32.ofNat ((ptr.toNat +
                  (k * (5 : UInt64).toNat + (5 : UInt64).toNat) *
                    (8 : UInt64).toNat) % 4294967296)) }
              have hcandidate : candidate = os[k]! := by
                rcases horder : os[k]! with ⟨oid, trader, side, price, qty⟩
                simp only [horder] at hr1 hr2 hr3 hr4 hr5 ⊢
                simp [candidate, hr1, hr2, hr3, hr4, hr5]
              refine wp_call_tw (func6_spec env st2 taker candidate) ?_
              rintro st3 vs ⟨rfl, rfl⟩
              rw [hcandidate]
              by_cases helig : eligibleL taker os[k]!
              · simp only [boolWord, if_pos helig]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp)]
                norm_num
                by_cases hside : taker.oside = 0
                · refine wp_iff_cons rfl ?_
                  rw [if_pos (by simp [hside])]
                  norm_num
                  refine wp_iff_cons rfl ?_
                  rw [if_pos (by simp)]
                  norm_num
                  refine wp_iff_cons rfl ?_
                  rw [if_pos (by simp)]
                  norm_num
                  refine wp_iff_cons rfl ?_
                  rw [if_pos (by simp)]
                  norm_num
                  refine ⟨hHeadB, ?_⟩
                  rw [hHead]
                  refine wp_iff_cons rfl ?_
                  rw [if_pos (by simp [hlt])]
                  norm_num
                  refine ⟨hb4, ?_⟩
                  rw [hHead]
                  refine ⟨hHeadB, ?_⟩
                  rw [hjPayload]
                  refine wp_iff_cons rfl ?_
                  rw [if_pos (by simp [hjltU])]
                  norm_num
                  refine ⟨jb4, ?_⟩
                  by_cases hprice :
                      (os[k]?.getD default).oprice <
                        (os[j]?.getD default).oprice
                  · refine wp_iff_cons rfl ?_
                    rw [if_pos (by
                      simp [hr4, jr4]
                      simpa only using hprice)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp [optionTag])]
                    norm_num
                    mf_read_candidate_tail hHead hHeadB hlt hb1 hb2 hb3 hb4 hb5
                    refine wp_call_tw (func6_spec env st3 taker candidate) ?_
                    rintro st4 vs ⟨rfl, rfl⟩
                    rw [hcandidate]
                    simp only [boolWord, if_pos helig]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp [hside])]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine ⟨hHeadB, ?_⟩
                    rw [hHead]
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp [hlt])]
                    norm_num
                    refine ⟨hb4, ?_⟩
                    rw [hHead]
                    refine ⟨hHeadB, ?_⟩
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp [hjltU])]
                    norm_num
                    refine ⟨jb4, ?_⟩
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by
                      simp [hr4, jr4]
                      simpa only using hprice)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    have hchoose : eligibleL taker os[k]! ∧
                        betterPriceL taker os[k]! os[j]! := ⟨helig, by
                      simpa [betterPriceL, hside] using hprice⟩
                    have hnext : bestPrefixL os taker (k + 1) = some k := by
                      simp only [bestPrefixL, hbest, bestStepL,
                        if_pos hchoose]
                    constructor
                    · rw [hfuel_next, hkadd]
                      simpa only [mfFrame, candidate, optionTag, optionPayload] using
                        (mfInv_some_step st4 owner ptr os taker k k j candidate
                          (by omega) hnext)
                    · simp only [mfMeasure]
                      rw [hfuel_next, toNat_ofNat_lt, toNat_ofNat_lt]
                      · omega
                      · rw [size_eq]
                        omega
                      · rw [size_eq]
                        omega
                  · refine wp_iff_cons rfl ?_
                    rw [if_neg (by
                      simp [hr4, jr4]
                      rw [UInt64.le_iff_toNat_le]
                      rw [UInt64.lt_iff_toNat_lt] at hprice
                      omega)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp [optionTag])]
                    norm_num
                    mf_read_candidate_tail hHead hHeadB hlt hb1 hb2 hb3 hb4 hb5
                    refine wp_call_tw (func6_spec env st3 taker candidate) ?_
                    rintro st4 vs ⟨rfl, rfl⟩
                    rw [hcandidate]
                    simp only [boolWord, if_pos helig]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp [hside])]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine ⟨hHeadB, ?_⟩
                    rw [hHead]
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp [hlt])]
                    norm_num
                    refine ⟨hb4, ?_⟩
                    rw [hHead]
                    refine ⟨hHeadB, ?_⟩
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp [hjltU])]
                    norm_num
                    refine ⟨jb4, ?_⟩
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by
                      simp [hr4, jr4]
                      rw [UInt64.le_iff_toNat_le]
                      rw [UInt64.lt_iff_toNat_lt] at hprice
                      omega)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    have hnprice : ¬betterPriceL taker os[k]! os[j]! := by
                      simpa [betterPriceL, hside] using hprice
                    have hkeep : ¬(eligibleL taker os[k]! ∧
                        betterPriceL taker os[k]! os[j]!) := by
                      exact fun h => hnprice h.2
                    have hnext : bestPrefixL os taker (k + 1) = some j := by
                      simp only [bestPrefixL, hbest, bestStepL, if_neg hkeep]
                    constructor
                    · rw [hfuel_next, hkadd]
                      simpa only [mfFrame, candidate, optionTag, optionPayload] using
                        (mfInv_some_step st4 owner ptr os taker k j j candidate
                          (by omega) hnext)
                    · simp only [mfMeasure]
                      rw [hfuel_next, toNat_ofNat_lt, toNat_ofNat_lt]
                      · omega
                      · rw [size_eq]
                        omega
                      · rw [size_eq]
                        omega
                · refine wp_iff_cons rfl ?_
                  rw [if_neg (by simp [hside])]
                  norm_num
                  refine wp_iff_cons rfl ?_
                  rw [if_neg (by simp)]
                  norm_num
                  refine wp_iff_cons rfl ?_
                  rw [if_neg (by simp)]
                  norm_num
                  refine wp_iff_cons rfl ?_
                  rw [if_neg (by simp)]
                  norm_num
                  refine ⟨hHeadB, ?_⟩
                  rw [hHead]
                  rw [hjPayload]
                  refine wp_iff_cons rfl ?_
                  rw [if_pos (by simp [hjltU])]
                  norm_num
                  refine ⟨jb4, ?_⟩
                  rw [hHead]
                  refine ⟨hHeadB, ?_⟩
                  refine wp_iff_cons rfl ?_
                  rw [if_pos (by simp [hlt])]
                  norm_num
                  refine ⟨hb4, ?_⟩
                  by_cases hprice :
                      (os[j]?.getD default).oprice <
                        (os[k]?.getD default).oprice
                  · refine wp_iff_cons rfl ?_
                    rw [if_pos (by
                      simp [jr4, hr4]
                      simpa only using hprice)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp [optionTag])]
                    norm_num
                    mf_read_candidate_tail hHead hHeadB hlt hb1 hb2 hb3 hb4 hb5
                    refine wp_call_tw (func6_spec env st3 taker candidate) ?_
                    rintro st4 vs ⟨rfl, rfl⟩
                    rw [hcandidate]
                    simp only [boolWord, if_pos helig]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp [hside])]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    refine ⟨hHeadB, ?_⟩
                    rw [hHead]
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp [hjltU])]
                    norm_num
                    refine ⟨jb4, ?_⟩
                    rw [hHead]
                    refine ⟨hHeadB, ?_⟩
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp [hlt])]
                    norm_num
                    refine ⟨hb4, ?_⟩
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by
                      simp [jr4, hr4]
                      simpa only using hprice)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    have hchoose : eligibleL taker os[k]! ∧
                        betterPriceL taker os[k]! os[j]! := ⟨helig, by
                      simpa [betterPriceL, hside] using hprice⟩
                    have hnext : bestPrefixL os taker (k + 1) = some k := by
                      simp only [bestPrefixL, hbest, bestStepL,
                        if_pos hchoose]
                    constructor
                    · rw [hfuel_next, hkadd]
                      simpa only [mfFrame, candidate, optionTag, optionPayload] using
                        (mfInv_some_step st4 owner ptr os taker k k k candidate
                          (by omega) hnext)
                    · simp only [mfMeasure]
                      rw [hfuel_next, toNat_ofNat_lt, toNat_ofNat_lt]
                      · omega
                      · rw [size_eq]
                        omega
                      · rw [size_eq]
                        omega
                  · refine wp_iff_cons rfl ?_
                    rw [if_neg (by
                      simp [jr4, hr4]
                      rw [UInt64.le_iff_toNat_le]
                      rw [UInt64.lt_iff_toNat_lt] at hprice
                      omega)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp [optionTag])]
                    norm_num
                    mf_read_candidate_tail hHead hHeadB hlt hb1 hb2 hb3 hb4 hb5
                    refine wp_call_tw (func6_spec env st3 taker candidate) ?_
                    rintro st4 vs ⟨rfl, rfl⟩
                    rw [hcandidate]
                    simp only [boolWord, if_pos helig]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp [hside])]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    refine ⟨hHeadB, ?_⟩
                    rw [hHead]
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp [hjltU])]
                    norm_num
                    refine ⟨jb4, ?_⟩
                    rw [hHead]
                    refine ⟨hHeadB, ?_⟩
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp [hlt])]
                    norm_num
                    refine ⟨hb4, ?_⟩
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by
                      simp [jr4, hr4]
                      rw [UInt64.le_iff_toNat_le]
                      rw [UInt64.lt_iff_toNat_lt] at hprice
                      omega)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    norm_num
                    have hnprice : ¬betterPriceL taker os[k]! os[j]! := by
                      simpa [betterPriceL, hside] using hprice
                    have hkeep : ¬(eligibleL taker os[k]! ∧
                        betterPriceL taker os[k]! os[j]!) := by
                      exact fun h => hnprice h.2
                    have hnext : bestPrefixL os taker (k + 1) = some j := by
                      simp only [bestPrefixL, hbest, bestStepL, if_neg hkeep]
                    constructor
                    · rw [hfuel_next, hkadd]
                      simpa only [mfFrame, candidate, optionTag, optionPayload] using
                        (mfInv_some_step st4 owner ptr os taker k j k candidate
                          (by omega) hnext)
                    · simp only [mfMeasure]
                      rw [hfuel_next, toNat_ofNat_lt, toNat_ofNat_lt]
                      · omega
                      · rw [size_eq]
                        omega
                      · rw [size_eq]
                        omega
              · simp only [boolWord, if_neg helig]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_neg (by simp)]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_neg (by simp)]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_neg (by simp)]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_neg (by simp)]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_neg (by simp [optionTag])]
                norm_num
                mf_read_candidate_tail hHead hHeadB hlt hb1 hb2 hb3 hb4 hb5
                refine wp_call_tw (func6_spec env st3 taker candidate) ?_
                rintro st4 vs ⟨rfl, rfl⟩
                rw [hcandidate]
                simp only [boolWord, if_neg helig]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_neg (by simp)]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_neg (by simp)]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_neg (by simp)]
                norm_num
                refine wp_iff_cons rfl ?_
                rw [if_neg (by simp)]
                norm_num
                have hkeep : ¬(eligibleL taker os[k]! ∧
                    betterPriceL taker os[k]! os[j]!) := by
                  exact fun h => helig h.1
                have hnext : bestPrefixL os taker (k + 1) = some j := by
                  simp only [bestPrefixL, hbest, bestStepL, if_neg hkeep]
                constructor
                · rw [hfuel_next, hkadd]
                  simpa only [mfFrame, candidate, optionTag, optionPayload] using
                    (mfInv_some_step st4 owner ptr os taker k j k candidate
                      (by omega) hnext)
                · simp only [mfMeasure]
                  rw [hfuel_next, toNat_ofNat_lt, toNat_ofNat_lt]
                  · omega
                  · rw [size_eq]
                    omega
                  · rw [size_eq]
                    omega
      · simp [mfFrame]
        refine wp_iff_cons rfl ?_
        by_cases hfz : fuel = 0
        · rw [if_neg (by simp [hfz])]
          wp_run
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          simp [func8Def, optionVals, findBestL_eq_prefix]
        · rw [if_pos (by simp [hfz])]
          wp_run
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          simp [func8Def, optionVals, findBestL_eq_prefix]

theorem func8_spec (env : HostEnv Unit) (st : Store Unit) (ptr : UInt64)
    (os : List OrderL) (taker : OrderL)
    (hlen : os.length < 4294967296) (hInput : OrdersAt st ptr os) :
    TerminatesWith (m := «module») (id := 8) (initial := st) (env := env)
      [.i64 0, .i64 0, .i64 0, .i64 taker.oqty, .i64 taker.oprice,
       .i64 taker.oside, .i64 taker.otrader, .i64 taker.oid, .i64 ptr,
       .i64 0, .i64 (UInt64.ofNat (os.length + 1))]
      (fun st' vs => vs = optionVals (findBestL os taker) ∧ st' = st) :=
  func8_spec_owner env st 0 ptr os taker hlen hInput

end Project.ClobMatchFuel.FindBest
