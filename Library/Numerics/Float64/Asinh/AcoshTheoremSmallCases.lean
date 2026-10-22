import Library.Numerics.Float64.Asinh.AcoshTheoremPieces0
import Library.Numerics.Float64.Asinh.AcoshTheoremPieces1
import Library.Numerics.Float64.Asinh.AcoshTheoremPieces2
import Library.Numerics.Float64.Asinh.AcoshTheoremPieces3

/-!
`Asinh.acosh` from 1 to `2 (1 + 2 ^ -20)` within two steps.  `t = x - 1` is `N 2 ^ -52` for a
natural `N` (`AcoshTheoremSmall.acosh_t`), and the 79 ranges of `AcoshTheoremPieces0` to
`AcoshTheoremPieces3` cover `N` from 1 to 4503608634569750 without gaps.  The ranges split where
`2t + t²` passes a power of 2, so that in each range the hypotheses of `acosh_piece_exact` or
`acosh_piece_half`, checked by `norm_num`, place the computed sum `2t + t²` and its root in one
binade each.  Each step of the case split compares `N` with the last numerator of a range.
-/

namespace Library.Numerics.Float64.Asinh.AcoshTheoremSmallCases
open CodeLib.IEEE64 LeanExe.ProofKit AcoshTheoremSmall

set_option exponentiation.threshold 4096

/-- **`acosh` from 1 to `2 (1 + 2 ^ -20)`.** -/
theorem acosh_small (x : Float) (hx : Finite x.toBits) (h1 : 1 < value x.toBits)
    (h2 : value x.toBits < 1048577 / 524288) :
    F64SignedRounding.WithinSteps 2 (Real.arcosh (value x.toBits))
      (Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt)).toBits := by
  obtain ⟨-, htv, N, hN⟩ := acosh_t x hx h1.le (by linarith [(by norm_num : (1048577 : ℝ) / 524288 ≤ 3)])
  have hv : value x.toBits - 1 = (N : ℝ) / 2 ^ 52 := by rw [← htv, hN]
  have le_of : ∀ a : ℕ, a ≤ N → (a : ℝ) / 2 ^ 52 ≤ value x.toBits - 1 := by
    intro a ha
    rw [hv]
    exact div_le_div_of_nonneg_right (by exact_mod_cast ha) (by positivity)
  have ge_of : ∀ b : ℕ, N ≤ b → value x.toBits - 1 ≤ (b : ℝ) / 2 ^ 52 := by
    intro b hb
    rw [hv]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hb) (by positivity)
  have hN1 : 1 ≤ N := by
    by_contra hc
    have h0 : N = 0 := by omega
    rw [h0] at hv
    simp at hv
    linarith
  have hNmax : N ≤ 4503608634569750 := by
    by_contra hc
    have hc' : (4503608634569750 : ℝ) + 1 ≤ N := by exact_mod_cast (show 4503608634569750 + 1 ≤ N by omega)
    have : value x.toBits - 1 = (N : ℝ) / 2 ^ 52 := hv
    have h3 : ((4503608634569750 : ℝ) + 1) / 2 ^ 52 ≤ (N : ℝ) / 2 ^ 52 :=
      div_le_div_of_nonneg_right hc' (by positivity)
    have h4 : (1048577 : ℝ) / 524288 - 1 < ((4503608634569750 : ℝ) + 1) / 2 ^ 52 := by norm_num
    linarith
  rcases Nat.lt_or_ge N (1 + 1) with c1 | c1
  · exact AcoshTheoremPieces0.piece0 x hx (by have h := le_of 1 hN1; push_cast at h; linarith only [h]) (by have h := ge_of 1 (Nat.lt_succ_iff.mp c1); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (2 + 1) with c2 | c2
  · exact AcoshTheoremPieces0.piece1 x hx (by have h := le_of 2 c1; push_cast at h; linarith only [h]) (by have h := ge_of 2 (Nat.lt_succ_iff.mp c2); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (7 + 1) with c3 | c3
  · exact AcoshTheoremPieces0.piece2 x hx (by have h := le_of 3 c2; push_cast at h; linarith only [h]) (by have h := ge_of 7 (Nat.lt_succ_iff.mp c3); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (14 + 1) with c4 | c4
  · exact AcoshTheoremPieces0.piece3 x hx (by have h := le_of 8 c3; push_cast at h; linarith only [h]) (by have h := ge_of 14 (Nat.lt_succ_iff.mp c4); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (31 + 1) with c5 | c5
  · exact AcoshTheoremPieces0.piece4 x hx (by have h := le_of 15 c4; push_cast at h; linarith only [h]) (by have h := ge_of 31 (Nat.lt_succ_iff.mp c5); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (62 + 1) with c6 | c6
  · exact AcoshTheoremPieces0.piece5 x hx (by have h := le_of 32 c5; push_cast at h; linarith only [h]) (by have h := ge_of 62 (Nat.lt_succ_iff.mp c6); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (127 + 1) with c7 | c7
  · exact AcoshTheoremPieces0.piece6 x hx (by have h := le_of 63 c6; push_cast at h; linarith only [h]) (by have h := ge_of 127 (Nat.lt_succ_iff.mp c7); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (254 + 1) with c8 | c8
  · exact AcoshTheoremPieces0.piece7 x hx (by have h := le_of 128 c7; push_cast at h; linarith only [h]) (by have h := ge_of 254 (Nat.lt_succ_iff.mp c8); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (511 + 1) with c9 | c9
  · exact AcoshTheoremPieces0.piece8 x hx (by have h := le_of 255 c8; push_cast at h; linarith only [h]) (by have h := ge_of 511 (Nat.lt_succ_iff.mp c9); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (1022 + 1) with c10 | c10
  · exact AcoshTheoremPieces0.piece9 x hx (by have h := le_of 512 c9; push_cast at h; linarith only [h]) (by have h := ge_of 1022 (Nat.lt_succ_iff.mp c10); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (2047 + 1) with c11 | c11
  · exact AcoshTheoremPieces0.piece10 x hx (by have h := le_of 1023 c10; push_cast at h; linarith only [h]) (by have h := ge_of 2047 (Nat.lt_succ_iff.mp c11); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (4094 + 1) with c12 | c12
  · exact AcoshTheoremPieces0.piece11 x hx (by have h := le_of 2048 c11; push_cast at h; linarith only [h]) (by have h := ge_of 4094 (Nat.lt_succ_iff.mp c12); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (8191 + 1) with c13 | c13
  · exact AcoshTheoremPieces0.piece12 x hx (by have h := le_of 4095 c12; push_cast at h; linarith only [h]) (by have h := ge_of 8191 (Nat.lt_succ_iff.mp c13); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (16382 + 1) with c14 | c14
  · exact AcoshTheoremPieces0.piece13 x hx (by have h := le_of 8192 c13; push_cast at h; linarith only [h]) (by have h := ge_of 16382 (Nat.lt_succ_iff.mp c14); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (32767 + 1) with c15 | c15
  · exact AcoshTheoremPieces0.piece14 x hx (by have h := le_of 16383 c14; push_cast at h; linarith only [h]) (by have h := ge_of 32767 (Nat.lt_succ_iff.mp c15); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (65534 + 1) with c16 | c16
  · exact AcoshTheoremPieces0.piece15 x hx (by have h := le_of 32768 c15; push_cast at h; linarith only [h]) (by have h := ge_of 65534 (Nat.lt_succ_iff.mp c16); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (131071 + 1) with c17 | c17
  · exact AcoshTheoremPieces0.piece16 x hx (by have h := le_of 65535 c16; push_cast at h; linarith only [h]) (by have h := ge_of 131071 (Nat.lt_succ_iff.mp c17); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (262142 + 1) with c18 | c18
  · exact AcoshTheoremPieces0.piece17 x hx (by have h := le_of 131072 c17; push_cast at h; linarith only [h]) (by have h := ge_of 262142 (Nat.lt_succ_iff.mp c18); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (524287 + 1) with c19 | c19
  · exact AcoshTheoremPieces0.piece18 x hx (by have h := le_of 262143 c18; push_cast at h; linarith only [h]) (by have h := ge_of 524287 (Nat.lt_succ_iff.mp c19); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (1048574 + 1) with c20 | c20
  · exact AcoshTheoremPieces0.piece19 x hx (by have h := le_of 524288 c19; push_cast at h; linarith only [h]) (by have h := ge_of 1048574 (Nat.lt_succ_iff.mp c20); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (2097151 + 1) with c21 | c21
  · exact AcoshTheoremPieces1.piece20 x hx (by have h := le_of 1048575 c20; push_cast at h; linarith only [h]) (by have h := ge_of 2097151 (Nat.lt_succ_iff.mp c21); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (4194302 + 1) with c22 | c22
  · exact AcoshTheoremPieces1.piece21 x hx (by have h := le_of 2097152 c21; push_cast at h; linarith only [h]) (by have h := ge_of 4194302 (Nat.lt_succ_iff.mp c22); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (8388607 + 1) with c23 | c23
  · exact AcoshTheoremPieces1.piece22 x hx (by have h := le_of 4194303 c22; push_cast at h; linarith only [h]) (by have h := ge_of 8388607 (Nat.lt_succ_iff.mp c23); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (16777214 + 1) with c24 | c24
  · exact AcoshTheoremPieces1.piece23 x hx (by have h := le_of 8388608 c23; push_cast at h; linarith only [h]) (by have h := ge_of 16777214 (Nat.lt_succ_iff.mp c24); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (33554431 + 1) with c25 | c25
  · exact AcoshTheoremPieces1.piece24 x hx (by have h := le_of 16777215 c24; push_cast at h; linarith only [h]) (by have h := ge_of 33554431 (Nat.lt_succ_iff.mp c25); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (67108862 + 1) with c26 | c26
  · exact AcoshTheoremPieces1.piece25 x hx (by have h := le_of 33554432 c25; push_cast at h; linarith only [h]) (by have h := ge_of 67108862 (Nat.lt_succ_iff.mp c26); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (134217726 + 1) with c27 | c27
  · exact AcoshTheoremPieces1.piece26 x hx (by have h := le_of 67108863 c26; push_cast at h; linarith only [h]) (by have h := ge_of 134217726 (Nat.lt_succ_iff.mp c27); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (268435447 + 1) with c28 | c28
  · exact AcoshTheoremPieces1.piece27 x hx (by have h := le_of 134217727 c27; push_cast at h; linarith only [h]) (by have h := ge_of 268435447 (Nat.lt_succ_iff.mp c28); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (536870880 + 1) with c29 | c29
  · exact AcoshTheoremPieces1.piece28 x hx (by have h := le_of 268435448 c28; push_cast at h; linarith only [h]) (by have h := ge_of 536870880 (Nat.lt_succ_iff.mp c29); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (1073741695 + 1) with c30 | c30
  · exact AcoshTheoremPieces1.piece29 x hx (by have h := le_of 536870881 c29; push_cast at h; linarith only [h]) (by have h := ge_of 1073741695 (Nat.lt_succ_iff.mp c30); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (2147483136 + 1) with c31 | c31
  · exact AcoshTheoremPieces1.piece30 x hx (by have h := le_of 1073741696 c30; push_cast at h; linarith only [h]) (by have h := ge_of 2147483136 (Nat.lt_succ_iff.mp c31); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (4294965247 + 1) with c32 | c32
  · exact AcoshTheoremPieces1.piece31 x hx (by have h := le_of 2147483137 c31; push_cast at h; linarith only [h]) (by have h := ge_of 4294965247 (Nat.lt_succ_iff.mp c32); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (8589926400 + 1) with c33 | c33
  · exact AcoshTheoremPieces1.piece32 x hx (by have h := le_of 4294965248 c32; push_cast at h; linarith only [h]) (by have h := ge_of 8589926400 (Nat.lt_succ_iff.mp c33); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (17179836415 + 1) with c34 | c34
  · exact AcoshTheoremPieces1.piece33 x hx (by have h := le_of 8589926401 c33; push_cast at h; linarith only [h]) (by have h := ge_of 17179836415 (Nat.lt_succ_iff.mp c34); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (34359607296 + 1) with c35 | c35
  · exact AcoshTheoremPieces1.piece34 x hx (by have h := le_of 17179836416 c34; push_cast at h; linarith only [h]) (by have h := ge_of 34359607296 (Nat.lt_succ_iff.mp c35); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (68718952454 + 1) with c36 | c36
  · exact AcoshTheoremPieces1.piece35 x hx (by have h := le_of 34359607297 c35; push_cast at h; linarith only [h]) (by have h := ge_of 68718952454 (Nat.lt_succ_iff.mp c36); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (137436856383 + 1) with c37 | c37
  · exact AcoshTheoremPieces1.piece36 x hx (by have h := le_of 68718952455 c36; push_cast at h; linarith only [h]) (by have h := ge_of 137436856383 (Nat.lt_succ_iff.mp c37); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (274869518846 + 1) with c38 | c38
  · exact AcoshTheoremPieces1.piece37 x hx (by have h := le_of 137436856384 c37; push_cast at h; linarith only [h]) (by have h := ge_of 274869518846 (Nat.lt_succ_iff.mp c38); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (549722263551 + 1) with c39 | c39
  · exact AcoshTheoremPieces1.piece38 x hx (by have h := le_of 274869518847 c38; push_cast at h; linarith only [h]) (by have h := ge_of 549722263551 (Nat.lt_succ_iff.mp c39); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (1099377442805 + 1) with c40 | c40
  · exact AcoshTheoremPieces1.piece39 x hx (by have h := le_of 549722263552 c39; push_cast at h; linarith only [h]) (by have h := ge_of 1099377442805 (Nat.lt_succ_iff.mp c40); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (2198486646624 + 1) with c41 | c41
  · exact AcoshTheoremPieces2.piece40 x hx (by have h := le_of 1099377442806 c40; push_cast at h; linarith only [h]) (by have h := ge_of 2198486646624 (Nat.lt_succ_iff.mp c41); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (4395901122050 + 1) with c42 | c42
  · exact AcoshTheoremPieces2.piece41 x hx (by have h := le_of 2198486646625 c41; push_cast at h; linarith only [h]) (by have h := ge_of 4395901122050 (Nat.lt_succ_iff.mp c42); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (8787519823983 + 1) with c43 | c43
  · exact AcoshTheoremPieces2.piece42 x hx (by have h := le_of 4395901122051 c42; push_cast at h; linarith only [h]) (by have h := ge_of 8787519823983 (Nat.lt_succ_iff.mp c43); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (17557959871978 + 1) with c44 | c44
  · exact AcoshTheoremPieces2.piece43 x hx (by have h := le_of 8787519823984 c43; push_cast at h; linarith only [h]) (by have h := ge_of 17557959871978 (Nat.lt_succ_iff.mp c44); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (35047996504784 + 1) with c45 | c45
  · exact AcoshTheoremPieces2.piece44 x hx (by have h := le_of 17557959871979 c44; push_cast at h; linarith only [h]) (by have h := ge_of 35047996504784 (Nat.lt_succ_iff.mp c45); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (69827414112266 + 1) with c46 | c46
  · exact AcoshTheoremPieces2.piece45 x hx (by have h := le_of 35047996504785 c45; push_cast at h; linarith only [h]) (by have h := ge_of 69827414112266 (Nat.lt_succ_iff.mp c46); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (104216013263496 + 1) with c47 | c47
  · exact AcoshTheoremPieces2.piece46 x hx (by have h := le_of 69827414112267 c46; push_cast at h; linarith only [h]) (by have h := ge_of 104216013263496 (Nat.lt_succ_iff.mp c47); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (121410312839111 + 1) with c48 | c48
  · exact AcoshTheoremPieces2.piece47 x hx (by have h := le_of 104216013263497 c47; push_cast at h; linarith only [h]) (by have h := ge_of 121410312839111 (Nat.lt_succ_iff.mp c48); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (138604612414726 + 1) with c49 | c49
  · exact AcoshTheoremPieces2.piece48 x hx (by have h := le_of 121410312839112 c48; push_cast at h; linarith only [h]) (by have h := ge_of 138604612414726 (Nat.lt_succ_iff.mp c49); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (142335640995005 + 1) with c50 | c50
  · exact AcoshTheoremPieces2.piece49 x hx (by have h := le_of 138604612414727 c49; push_cast at h; linarith only [h]) (by have h := ge_of 142335640995005 (Nat.lt_succ_iff.mp c50); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (142336529079052 + 1) with c51 | c51
  · exact AcoshTheoremPieces2.piece50 x hx (by have h := le_of 142335640995006 c50; push_cast at h; linarith only [h]) (by have h := ge_of 142336529079052 (Nat.lt_succ_iff.mp c51); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (142337417165222 + 1) with c52 | c52
  · exact AcoshTheoremPieces2.piece51 x hx (by have h := le_of 142336529079053 c51; push_cast at h; linarith only [h]) (by have h := ge_of 142337417165222 (Nat.lt_succ_iff.mp c52); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (273188108091886 + 1) with c53 | c53
  · exact AcoshTheoremPieces2.piece52 x hx (by have h := le_of 142337417165223 c52; push_cast at h; linarith only [h]) (by have h := ge_of 273188108091886 (Nat.lt_succ_iff.mp c53); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (273189127023832 + 1) with c54 | c54
  · exact AcoshTheoremPieces2.piece53 x hx (by have h := le_of 273188108091887 c53; push_cast at h; linarith only [h]) (by have h := ge_of 273189127023832 (Nat.lt_succ_iff.mp c54); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (273189233991148 + 1) with c55 | c55
  · exact AcoshTheoremPieces2.piece54 x hx (by have h := le_of 273189127023833 c54; push_cast at h; linarith only [h]) (by have h := ge_of 273189233991148 (Nat.lt_succ_iff.mp c55); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (273190359892002 + 1) with c56 | c56
  · exact AcoshTheoremPieces2.piece55 x hx (by have h := le_of 273189233991149 c55; push_cast at h; linarith only [h]) (by have h := ge_of 273190359892002 (Nat.lt_succ_iff.mp c56); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (375173624764559 + 1) with c57 | c57
  · exact AcoshTheoremPieces2.piece56 x hx (by have h := le_of 273190359892003 c56; push_cast at h; linarith only [h]) (by have h := ge_of 375173624764559 (Nat.lt_succ_iff.mp c57); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (375174875630335 + 1) with c58 | c58
  · exact AcoshTheoremPieces2.piece57 x hx (by have h := le_of 375173624764560 c57; push_cast at h; linarith only [h]) (by have h := ge_of 375174875630335 (Nat.lt_succ_iff.mp c58); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (375176126497445 + 1) with c59 | c59
  · exact AcoshTheoremPieces2.piece58 x hx (by have h := le_of 375174875630336 c58; push_cast at h; linarith only [h]) (by have h := ge_of 375176126497445 (Nat.lt_succ_iff.mp c59); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (375298717948311 + 1) with c60 | c60
  · exact AcoshTheoremPieces2.piece59 x hx (by have h := le_of 375176126497446 c59; push_cast at h; linarith only [h]) (by have h := ge_of 375298717948311 (Nat.lt_succ_iff.mp c60); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (375299968947540 + 1) with c61 | c61
  · exact AcoshTheoremPieces3.piece60 x hx (by have h := le_of 375298717948312 c60; push_cast at h; linarith only [h]) (by have h := ge_of 375299968947540 (Nat.lt_succ_iff.mp c61); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (375301219948104 + 1) with c62 | c62
  · exact AcoshTheoremPieces3.piece61 x hx (by have h := le_of 375299968947541 c61; push_cast at h; linarith only [h]) (by have h := ge_of 375301219948104 (Nat.lt_succ_iff.mp c62); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (453066178730137 + 1) with c63 | c63
  · exact AcoshTheoremPieces3.piece62 x hx (by have h := le_of 375301219948105 c62; push_cast at h; linarith only [h]) (by have h := ge_of 453066178730137 (Nat.lt_succ_iff.mp c63); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (453067505589356 + 1) with c64 | c64
  · exact AcoshTheoremPieces3.piece63 x hx (by have h := le_of 453066178730138 c63; push_cast at h; linarith only [h]) (by have h := ge_of 453067505589356 (Nat.lt_succ_iff.mp c64); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (453068832449762 + 1) with c65 | c65
  · exact AcoshTheoremPieces3.piece64 x hx (by have h := le_of 453067505589357 c64; push_cast at h; linarith only [h]) (by have h := ge_of 453068832449762 (Nat.lt_succ_iff.mp c65); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (531577827751079 + 1) with c66 | c66
  · exact AcoshTheoremPieces3.piece65 x hx (by have h := le_of 453068832449763 c65; push_cast at h; linarith only [h]) (by have h := ge_of 531577827751079 (Nat.lt_succ_iff.mp c66); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (576453336196390 + 1) with c67 | c67
  · exact AcoshTheoremPieces3.piece66 x hx (by have h := le_of 531577827751080 c66; push_cast at h; linarith only [h]) (by have h := ge_of 576453336196390 (Nat.lt_succ_iff.mp c67); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (576454760788068 + 1) with c68 | c68
  · exact AcoshTheoremPieces3.piece67 x hx (by have h := le_of 576453336196391 c67; push_cast at h; linarith only [h]) (by have h := ge_of 576454760788068 (Nat.lt_succ_iff.mp c68); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (576456185380749 + 1) with c69 | c69
  · exact AcoshTheoremPieces3.piece68 x hx (by have h := le_of 576454760788069 c68; push_cast at h; linarith only [h]) (by have h := ge_of 576456185380749 (Nat.lt_succ_iff.mp c69); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (1012160919052589 + 1) with c70 | c70
  · exact AcoshTheoremPieces3.piece69 x hx (by have h := le_of 576456185380750 c69; push_cast at h; linarith only [h]) (by have h := ge_of 1012160919052589 (Nat.lt_succ_iff.mp c70); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (1125898217993044 + 1) with c71 | c71
  · exact AcoshTheoremPieces3.piece70 x hx (by have h := le_of 1012160919052590 c70; push_cast at h; linarith only [h]) (by have h := ge_of 1125898217993044 (Nat.lt_succ_iff.mp c71); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (1125899906842623 + 1) with c72 | c72
  · exact AcoshTheoremPieces3.piece71 x hx (by have h := le_of 1125898217993045 c71; push_cast at h; linarith only [h]) (by have h := ge_of 1125899906842623 (Nat.lt_succ_iff.mp c72); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (1125901595692764 + 1) with c73 | c73
  · exact AcoshTheoremPieces3.piece72 x hx (by have h := le_of 1125899906842624 c72; push_cast at h; linarith only [h]) (by have h := ge_of 1125901595692764 (Nat.lt_succ_iff.mp c73); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (1865452045155276 + 1) with c74 | c74
  · exact AcoshTheoremPieces3.piece73 x hx (by have h := le_of 1125901595692765 c73; push_cast at h; linarith only [h]) (by have h := ge_of 1865452045155276 (Nat.lt_succ_iff.mp c74); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (3002397749980578 + 1) with c75 | c75
  · exact AcoshTheoremPieces3.piece74 x hx (by have h := le_of 1865452045155277 c74; push_cast at h; linarith only [h]) (by have h := ge_of 3002397749980578 (Nat.lt_succ_iff.mp c75); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (3002399751580329 + 1) with c76 | c76
  · exact AcoshTheoremPieces3.piece75 x hx (by have h := le_of 3002397749980579 c75; push_cast at h; linarith only [h]) (by have h := ge_of 3002399751580329 (Nat.lt_succ_iff.mp c76); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (3002401753180247 + 1) with c77 | c77
  · exact AcoshTheoremPieces3.piece76 x hx (by have h := le_of 3002399751580330 c76; push_cast at h; linarith only [h]) (by have h := ge_of 3002401753180247 (Nat.lt_succ_iff.mp c77); push_cast at h; linarith only [h])
  rcases Nat.lt_or_ge N (3296863744183465 + 1) with c78 | c78
  · exact AcoshTheoremPieces3.piece77 x hx (by have h := le_of 3002401753180248 c77; push_cast at h; linarith only [h]) (by have h := ge_of 3296863744183465 (Nat.lt_succ_iff.mp c78); push_cast at h; linarith only [h])
  exact AcoshTheoremPieces3.piece78 x hx (by have h := le_of 3296863744183466 c78; push_cast at h; linarith only [h]) (by have h := ge_of 4503608634569750 hNmax; push_cast at h; linarith only [h])

#print axioms acosh_small

end Library.Numerics.Float64.Asinh.AcoshTheoremSmallCases
