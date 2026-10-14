import Verified.Examples.LgammaLeaf
import Verified.Examples.LgammaBranches
import Verified.Examples.LgammaSign

/-!
The walk of the fast path's block of `Lgamma.lgammaR` to `FastSpec`, and with it one step for the
code's choice between the fast result and the accurate path (`fast_within`).  The block is read
with `LgammaWalk.walk_step` down to its leaves: `LgammaFastTiny.tiny_spec` below `2^-75`,
`LgammaFastSmall.small_spec` to `2^-5`, and `LgammaFastMid.mid_spec` to `1/2` in magnitude.  From
`1/2` on the code computes the triple `(fh, fl, eps)` at `|x|` before it tests the sign, and
`walk_bridge` reads that triple with the predicate `LgammaLeaf.LeafSpec |x|`, which the pieces
(`leaf_piece`) and Stirling's series (`leaf_stir_a`, `leaf_stir_b`) satisfy, and then the rest of
the block with that predicate as a hypothesis: `pos_leaf` at a positive `x` and `neg_leaf`, the
reflection, at a negative one.  The theorem takes `|x| ≤ 2^800`, the range of `stir_b`.
-/

namespace Verified.Examples.LgammaFastWalk
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Lgamma LgammaBranches LgammaWalk LgammaLeaf
open Verified.Examples.Tgamma (floorF)

set_option exponentiation.threshold 4096
set_option linter.auxLemma false

/-- `S` of a triple `match` from a predicate `P` of the discriminant: `P p`, and `S` of the body at
every triple that satisfies `P`. -/
theorem m3_bridge {β : Type} (S : β → Prop) (P : Float × Float × Float → Prop)
    (p : Float × Float × Float) (f : Float → Float → Float → β) (hp : P p)
    (h : ∀ a b c, P (a, b, c) → S (f a b c)) :
    S (asLgammaAsymAccurate.match_3 (fun _ => β) p f) := by
  obtain ⟨a, b, c⟩ := p
  exact h a b c hp

open Lean Elab Tactic Meta in
/-- `walk_bridge P` takes one step into a goal `S (match p with | (a, b, c) => f a b c)` through
`m3_bridge`, instantiated with the goal's own discriminant and body like `walk_step`: it leaves the
goals `P p` and `∀ a b c, P (a, b, c) → S (f a b c)`. -/
elab "walk_bridge " p:term : tactic => do
  let g ← getMainGoal
  g.withContext do
    let t := (← instantiateMVars (← g.getType)).consumeMData
    unless t.isApp do throwError "walk_bridge: the goal is not `S e`"
    let S := t.appFn!
    let e := t.appArg!.consumeMData
    unless e.isAppOfArity ``asLgammaAsymAccurate.match_3 3 do
      throwError "walk_bridge: no triple matcher"
    let args := e.getAppArgs
    let P ← elabTerm p none
    replaceMainGoal (← g.apply (← mkAppM ``m3_bridge #[S, P, args[1]!, args[2]!]))

/-! ### The tests of the code on the bits of `x` -/

theorem au_nat (w : UInt64) :
    (w <<< 1 >>> 38).toNat = w.toNat % 9223372036854775808 / 137438953472 := by
  rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.reducePow]
  have := w.toNat_lt
  omega

theorem fin_bits (w : UInt64) (hw : Finite w) :
    w.toNat % 9223372036854775808 < 0x7FF0000000000000 := by
  have h1 := F64Admissibility.finite_exponent_bound w hw
  rw [F64Order.exponent_abs, F64Order.absBits_toNat] at h1
  simp only [Nat.reducePow] at h1
  omega

theorem abs_lt_word (w c : UInt64) (r : ℝ) (hc : value c = r) (hcb : c.toNat < 2 ^ 63)
    (hw : w.toNat % 9223372036854775808 < c.toNat) : |value w| < r := by
  rw [← F64UpperWord.value_abs, ← hc]
  exact F64PositiveOrder.value_strict hcb (by rw [F64UpperWord.abs_toNat]; exact hw)

theorem word_le_abs (w c : UInt64) (r : ℝ) (hc : value c = r) (hcb : c.toNat < 2 ^ 63)
    (hw : c.toNat ≤ w.toNat % 9223372036854775808) : r ≤ |value w| := by
  rw [← F64UpperWord.value_abs, ← hc]
  exact (F64PositiveOrder.value_le_iff hcb
    (by rw [F64UpperWord.abs_toNat]; exact Nat.mod_lt _ (by norm_num))).mpr
    (by rw [F64UpperWord.abs_toNat]; exact hw)

theorem w75 : value (0x3B40000000000000 : UInt64) = 1 / 2 ^ 75 := by
  rw [TgammaSpecial.lit_value _ (1 / 2 ^ 75) (by decide +kernel)]; norm_num

theorem w5 : value (0x3FA0000000000000 : UInt64) = 1 / 2 ^ 5 := by
  rw [TgammaSpecial.lit_value _ (1 / 2 ^ 5) (by decide +kernel)]; norm_num

theorem w52 : value (0x4330000000000000 : UInt64) = 2 ^ 52 := by
  rw [TgammaSpecial.lit_value _ (2 ^ 52) (by decide +kernel)]; norm_num

theorem w800 : value (0x71F0000000000000 : UInt64) = 2 ^ 800 := by
  rw [TgammaSpecial.lit_value _ (2 ^ 800) (by decide +kernel)]; norm_num

theorem w100 : value (Float.ofBits 5057542381537067008).toBits = 2 ^ 100 := by
  rw [show (Float.ofBits 5057542381537067008).toBits = 0x4630000000000000 from rfl,
    TgammaSpecial.lit_value _ (2 ^ 100) (by decide +kernel)]; norm_num

theorem w100_finite : Finite (Float.ofBits 5057542381537067008).toBits :=
  TgammaWords.ofBits_finite _ (by decide)

theorem tab19 : mainTable[(19 : UInt64).toNat]! = 0x20104BA := by decide +kernel

/-- `|x|` is not 1 or 2 when `x` is neither 1, 2, nor a negative integer. -/
theorem abs_ne (v : ℝ) (c : ℕ) (hc0 : 0 < c) (hc : v ≠ c) (hint : v < 0 → ∀ n : ℤ, v ≠ n) :
    |v| ≠ c := by
  intro h
  rcases (abs_eq (by positivity : (0 : ℝ) ≤ c)).mp h with h' | h'
  · exact hc h'
  · have hneg : v < 0 := by
      have : (0 : ℝ) < c := by exact_mod_cast hc0
      linarith
    exact hint hneg (-(c : ℤ)) (by rw [h']; push_cast; ring)

/-! ### The walk -/

set_option maxHeartbeats 4000000 in
/-- **One step for the code's choice** at every finite `x` other than the poles, 1, and 2, up to
`2^800` in magnitude, when the accurate path is within one step. -/
theorem fast_within (hF : FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hS : LgammaApprox.SinpiFact) (hPF : LgammaApprox.PieceFact)
    (hSF : LgammaApprox.StirlingFact) (hSm : LgammaApprox.SmallFact) (x : Float)
    (hx : Finite x.toBits) (hv0 : value x.toBits ≠ 0) (hv1 : value x.toBits ≠ 1)
    (hv2 : value x.toBits ≠ 2) (hint : value x.toBits < 0 → ∀ n : ℤ, value x.toBits ≠ n)
    (h800 : |value x.toBits| ≤ 2 ^ 800)
    (h1 : ¬ x.toBits <<< 1 ≥ 0xFEAEA9B24F16A34C)
    (h2 : ¬ (floorF x == x && x ≤ 0.0) = true)
    (h3 : ¬ (floorF x == x && (x == 1.0 || x == 2.0)) = true)
    (hacc : F64SignedRounding.WithinSteps 1 (Real.log (Real.Gamma (value x.toBits)))
      (accurate Tgamma.logdTable logAccurateTable sinpiTable asymTable accurateTable dbTable
        x).toBits) :
    F64SignedRounding.WithinSteps 1 (Real.log (Real.Gamma (value x.toBits)))
      (lgammaR x).1.toBits := by
  obtain ⟨haf, hav⟩ := SinhWords.abs_float x hx
  have hfb := fin_bits _ hx
  have habsN : (x.abs.toBits).toNat = x.toBits.toNat % 9223372036854775808 := by
    rw [F64Bits.toBits_abs, F64UpperWord.abs_toNat]; rfl
  have hsign : (x.toBits >>> 63 == 1) = true ↔ value x.toBits < 0 := by
    constructor
    · intro hn
      rcases lt_or_gt_of_ne hv0 with h | h
      · exact h
      · have hs := F64Exact.sign_of_pos x.toBits h
        simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not] at hs
        exact absurd ((LgammaSpecial.sign_test _).mp hn) hs
    · intro hneg
      by_contra hn
      have hs : Wasm.IEEE64.sign x.toBits = false := by
        simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not]
        intro h; exact hn ((LgammaSpecial.sign_test _).mpr h)
      have := F64TwoSum.value_nonneg_of_sign _ hs
      linarith
  have hv1' := abs_ne _ 1 (by norm_num) (by exact_mod_cast hv1) hint
  have hv2' := abs_ne _ 2 (by norm_num) (by exact_mod_cast hv2) hint
  unfold lgammaR
  rewrite [lgammaWith.eq_1, ite_eq_right h1]
  extract_lets fx au sgn z z2 z4 q0 q2 q4 q6 ax zh zl z2h z4h q0s q2s fls j0 z0
  have h2' : ¬ (fx == x && x ≤ 0.0) = true := h2
  have h3' : ¬ (fx == x && (x == 1.0 || x == 2.0)) = true := h3
  rewrite [ite_eq_right h2', ite_eq_right h3']
  split
  next fh fl eps sign heq =>
  extract_lets ub lb
  refine select_within fh fl eps sign _ _ ?_ hacc
  rw [← heq]
  clear heq
  have hauN : au.toNat = x.toBits.toNat % 9223372036854775808 / 137438953472 := au_nat x.toBits
  walk_step
  · -- below `1/2` in magnitude
    intro hc
    rw [LgammaPieceIdx.tab0, UInt64.lt_iff_toNat_lt] at hc
    simp only [UInt64.reduceToNat] at hc
    walk_step; intro lh ll hlh
    walk_step
    · intro ht
      rw [UInt64.lt_iff_toNat_lt] at ht
      simp only [UInt64.reduceToNat] at ht
      exact LgammaFastTiny.tiny_spec hF hL x hx hv0
        (abs_lt_word _ _ _ w75 (by decide) (by simp only [UInt64.reduceToNat]; omega))
        lh ll hlh sgn
    · intro ht
      rw [UInt64.lt_iff_toNat_lt] at ht
      simp only [UInt64.reduceToNat] at ht
      walk_step
      · intro hs
        rw [UInt64.lt_iff_toNat_lt] at hs
        simp only [UInt64.reduceToNat] at hs
        walk_step; intro p1 p2 hP
        walk_step; intro m1 m2 hM
        walk_step; intro s1 s2 hS'
        exact LgammaFastSmall.small_spec hF hL hSm x hx
          (word_le_abs _ _ _ w75 (by decide) (by simp only [UInt64.reduceToNat]; omega))
          (by have := abs_lt_word x.toBits _ _ w5 (by decide)
                (by simp only [UInt64.reduceToNat]; omega)
              linarith)
          lh ll hlh sgn (p1, p2) (m1, m2) (s1, s2) hP.symm hM.symm hS'.symm
      · intro hs
        rw [UInt64.lt_iff_toNat_lt] at hs
        simp only [UInt64.reduceToNat] at hs
        walk_step; intro t xl htx
        walk_step; intro au2 hau2
        walk_step; intro j hj
        walk_step; intro zz hzz
        walk_step; intro p1 p2 hP
        walk_step; intro q1 q2 hQ
        walk_step; intro e he
        walk_step; intro s1 s2 hS'
        rw [hzz, hj, hau2] at hP
        rw [hj, hau2] at hQ
        rw [he]
        exact LgammaFastMid.mid_spec hF hL hPF x hx
          (by rw [F64Order.absBits_toNat]; simp only [Nat.reducePow]; omega)
          (by rw [F64Order.absBits_toNat]; simp only [Nat.reducePow]; omega)
          lh ll hlh sgn (piece mainTable (t.toBits >>> 37)) (by rw [htx]) (p1, p2) (q1, q2)
          (s1, s2) (by rw [htx]; exact hP.symm) hQ.symm hS'.symm
  · -- from `1/2` on
    intro hc
    rw [LgammaPieceIdx.tab0, UInt64.lt_iff_toNat_lt] at hc
    simp only [UInt64.reduceToNat] at hc
    have hhalf : 1 / 2 ≤ |value x.toBits| := word_le_abs _ (0x3FE0000000000000 : UInt64) _
      LgammaSign.half_word (by decide) (by simp only [UInt64.reduceToNat]; omega)
    have hax : value ax.toBits = |value x.toBits| := hav
    have haxN : ax.toBits.toNat / 137438953472 = au.toNat := by rw [hauN, ← habsN]
    have haxb : ax.toBits.toNat < 0x7FF0000000000000 := by
      have : ax.toBits.toNat = x.toBits.toNat % 9223372036854775808 := habsN
      omega
    walk_bridge (LeafSpec (value ax.toBits))
    · walk_step
      · -- Stirling's series
        intro h19
        rw [tab19, ge_iff_le, UInt64.le_iff_toNat_le] at h19
        simp only [UInt64.reduceToNat] at h19
        have hb19 : (LgammaApprox.border 19 : ℝ) ≤ value ax.toBits :=
          LgammaFastMid.border_le 19 (by norm_num) ax.toBits haxb
            (by rw [haxN, LgammaPieceIdx.tw_ends.2]; exact h19)
        have hb19' := LgammaPiecePoly.qcast_le LgammaStir.border19
        push_cast at hb19'
        walk_step; intro lh ll hL0
        walk_step; intro lh1 hlh1
        subst hlh1
        walk_step; intro m1 m2 hM
        walk_step; intro n1 n2 hN
        walk_step; intro t1 t2 hT
        walk_step; intro r1 r2 hR
        by_cases hbig : au ≥ 35225600
        · -- from `2^52` to `2^800`
          rw [ite_eq_left hbig] at hM
          have hbig' := hbig
          rw [ge_iff_le, UInt64.le_iff_toNat_le] at hbig'
          simp only [UInt64.reduceToNat] at hbig'
          have h52 : 2 ^ 52 ≤ value ax.toBits := by
            rw [hax]
            exact word_le_abs _ _ _ w52 (by decide) (by simp only [UInt64.reduceToNat]; omega)
          have htop : ¬ au ≥ 66763430 := by
            intro h
            rw [ge_iff_le, UInt64.le_iff_toNat_le] at h
            simp only [UInt64.reduceToNat] at h
            have : (2 : ℝ) ^ 800 < |value x.toBits| := by
              rw [← F64UpperWord.value_abs, ← w800]
              exact F64PositiveOrder.value_strict
                (by rw [F64UpperWord.abs_toNat]; exact Nat.mod_lt _ (by norm_num))
                (by rw [F64UpperWord.abs_toNat]; simp only [UInt64.reduceToNat, Nat.reducePow]
                    omega)
            linarith
          rw [ite_eq_right htop] at hM
          dsimp only at hM
          obtain ⟨d1, d2, hd⟩ : ∃ d1 d2, Tgamma.mulDDD ax (lh - 1.0) ll = (d1, d2) :=
            ⟨_, _, rfl⟩
          rw [hd] at hM
          dsimp only at hM
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hM
          have hTspec : Finite t1.toBits ∧ Finite t2.toBits ∧
              |value t1.toBits + value t2.toBits - LgammaStir.Tx (value ax.toBits)| ≤
                1 / 2 ^ 65 ∧
              |value t1.toBits| ≤ 1 / 64 ∧ |value t2.toBits| ≤ 1 / 2 ^ 50 := by
            by_cases h100 : ax < Float.ofBits 5057542381537067008
            · rw [ite_eq_left h100] at hT
              obtain ⟨e1, e2, he⟩ : ∃ e1 e2,
                  Tgamma.fastTwoSum (Tgamma.entry mainTable 399) fls = (e1, e2) := ⟨_, _, rfl⟩
              rw [he] at hT
              dsimp only at hT
              have hlt := (F64UpperWord.float_lt_iff _ _ haf w100_finite).mp h100
              rw [w100] at hlt
              obtain ⟨ht1, ht2, hte, ht1b, ht2b⟩ := LgammaStirSeries.series_spec hF ax haf
                (by linarith [(by norm_num : (33 / 4 : ℝ) ≤ 2 ^ 52)]) hlt.le (e1, e2) (t1, t2)
                he.symm hT.symm
              exact ⟨ht1, ht2, by rw [LgammaStir.Tx]; exact hte, ht1b, ht2b⟩
            · rw [ite_eq_right h100] at hT
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj hT
              have hge : 2 ^ 100 ≤ value ax.toBits := by
                have := (F64UpperWord.float_lt_iff _ _ haf w100_finite).not.mp h100
                rw [w100] at this
                exact le_of_not_gt this
              refine ⟨LgammaSpecial.zero_finite, LgammaSpecial.zero_finite,
                LgammaStir.T_zero _ hge, ?_, ?_⟩ <;>
                rw [TgammaMainRed.zero_value, abs_zero] <;> norm_num
          obtain ⟨hT1, hT2, hTe, hT1b, hT2b⟩ := hTspec
          exact leaf_stir_b hF hL hSF ax haf h52 (by rw [hax]; exact h800) (lh, ll) (d1, d2)
            (n1, n2) (t1, t2) (r1, r2) hL0.symm hd.symm hN.symm hT1 hT2 hTe hT1b hT2b hR.symm
        · -- from 8.29541 to `2^52`
          rw [ite_eq_right hbig] at hM
          have hbig' := hbig
          rw [ge_iff_le, UInt64.le_iff_toNat_le, not_le] at hbig'
          simp only [UInt64.reduceToNat] at hbig'
          have h52 : value ax.toBits < 2 ^ 52 := by
            rw [hax]
            exact abs_lt_word _ _ _ w52 (by decide) (by simp only [UInt64.reduceToNat]; omega)
          have h100 : ax < Float.ofBits 5057542381537067008 := by
            rw [F64UpperWord.float_lt_iff _ _ haf w100_finite, w100]
            linarith [(by norm_num : (2 : ℝ) ^ 52 ≤ 2 ^ 100)]
          rw [ite_eq_left h100] at hT
          obtain ⟨e1, e2, he⟩ : ∃ e1 e2,
              Tgamma.fastTwoSum (Tgamma.entry mainTable 399) fls = (e1, e2) := ⟨_, _, rfl⟩
          rw [he] at hT
          dsimp only at hT
          exact leaf_stir_a hF hL hSF ax haf hb19 h52 (lh, ll) (m1, m2) (n1, n2) (e1, e2)
            (t1, t2) (r1, r2) hL0.symm hM.symm hN.symm he.symm hT.symm hR.symm
      · -- a piece
        intro h19
        rw [tab19, ge_iff_le, UInt64.le_iff_toNat_le, not_le] at h19
        simp only [UInt64.reduceToNat] at h19
        walk_step; intro p1 p2 hP
        walk_step; intro q1 q2 hQ
        walk_step; intro r1 r2 hR
        obtain ⟨k, hk, hkj, hk0, hk1⟩ := LgammaPieceIdx.piece_spec au (by omega) (by omega)
        have hb0 : (LgammaApprox.border k : ℝ) ≤ value ax.toBits :=
          LgammaFastMid.border_le k (by omega) ax.toBits haxb (by rw [haxN]; exact hk0)
        have hb1 : value ax.toBits ≤ (LgammaApprox.border (k + 1) : ℝ) :=
          LgammaFastMid.le_border (k + 1) (by omega) ax.toBits haxb (by rw [haxN]; exact hk1)
        exact leaf_piece hF hPF ax haf k hk j0 hkj hb0 hb1 (by rw [hax]; exact_mod_cast hv1')
          (by rw [hax]; exact_mod_cast hv2') (p1, p2) (q1, q2) (r1, r2) hP.symm hQ.symm hR.symm
    · intro fh fl eps hl
      walk_step
      · intro hn
        have hneg : value x.toBits < 0 := hsign.mp hn
        walk_step; intro sh sl hA
        walk_step; intro sh2 sl2 hB
        walk_step; intro lh ll hC
        walk_step; intro dh dl hD
        have hint' := hint hneg
        have h52 : -2 ^ 52 < value x.toBits := by
          by_contra hn52
          obtain ⟨N, hN⟩ := TgammaFloor.int_of_large x.toBits hx
            (by rw [abs_of_neg hneg]; linarith)
          exact hint' N hN
        rw [hax, abs_of_neg hneg] at hl
        rw [abs_of_neg hneg] at hhalf
        exact neg_leaf hF hL hS x hx (by linarith) h52 hint' (fh, fl, eps) hl (sh, sl) (sh2, sl2)
          (lh, ll) (dh, dl) hA.symm hB.symm hC.symm hD.symm _
      · intro hn
        have hpos : 0 < value x.toBits := by
          rcases lt_or_gt_of_ne hv0 with h | h
          · exact absurd (hsign.mpr h) hn
          · exact h
        rw [hax, abs_of_pos hpos] at hl
        exact pos_leaf x (fh, fl, eps) hl 1.0

#print axioms fast_within

end Verified.Examples.LgammaFastWalk
