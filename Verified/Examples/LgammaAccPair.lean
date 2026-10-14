import Verified.Examples.LgammaAccTail
import Verified.Examples.LgammaAccNorm

/-!
**From a triple to the pair of `LgammaAccTail.AccPair`**, through the renormalization of
`Lgamma.accurate` (`LgammaAccNorm.norm_spec`).  For a triple `a + b + c` within `E` of `L`, with
`|a| ≤ A`, `|b| ≤ B`, `|c| ≤ C`, and `B + C` small against `|a| + 1`, the pair is within
`Et = E + (B + C)/2^52 + (A + B + C)/2^99 + 2^-1070` of `L` (`norm_pair`).  When its high part is
below `3/8`, its low part is below `2^-48`, so `|L| ≤ |fh| + 2^-46`.  The hypothesis `hbud` states
when `Et ≤ |L|/(2^53 + 1)`: for a high part `p1` that is close to `L` when it is below `3/8`, with
`|L| ≥ 1/4` when it is not, and that selects no polynomial about a zero.
-/

namespace Verified.Examples.LgammaAccPair
open CodeLib.IEEE64 LeanExe.ProofKit Tgamma LgammaAccTail

set_option exponentiation.threshold 4096

set_option maxHeartbeats 4000000 in
/-- **The renormalized pair** of a triple. -/
theorem norm_pair (L : ℝ) (sx : Float) (a b c : Float) (ha : Finite a.toBits)
    (hb : Finite b.toBits) (hc : Finite c.toBits) (A E B C : ℝ)
    (hE : |value a.toBits + value b.toBits + value c.toBits - L| ≤ E)
    (haA : |value a.toBits| ≤ A) (hbB : |value b.toBits| ≤ B) (hcC : |value c.toBits| ≤ C)
    (hA : A ≤ 2 ^ 850) (hB : B ≤ 2 ^ 840) (hC : C ≤ 2 ^ 800)
    (hBC : B + C ≤ (|value a.toBits| + 1) / 2 ^ 19)
    (hEs : E + (B + C) / 2 ^ 52 + (A + B + C) / 2 ^ 99 + 1 / 2 ^ 1070 ≤
      1 / 2 ^ 50 + |L| / 2 ^ 50)
    (hbud : ∀ p1 : Float, Finite p1.toBits →
      (|value p1.toBits| < 3 / 8 → |value p1.toBits| ≤ |L| * (1 + 1 / 2 ^ 50) + 1 / 2 ^ 44) →
      (3 / 8 ≤ |value p1.toBits| → 1 / 4 ≤ |L|) →
      (|value p1.toBits| < 3 / 8 → Lgamma.rootRange p1.abs sx = (0, 0, 0, 0.0)) →
      E + (B + C) / 2 ^ 52 + (A + B + C) / 2 ^ 99 + 1 / 2 ^ 1070 ≤ |L| / (2 ^ 53 + 1))
    (h1 l1 : Float) (e1 : fastTwoSum a b = (h1, l1))
    (l2 ll2 : Float) (e2 : fastTwoSum l1 c = (l2, ll2))
    (h3 l3 : Float) (e3 : fastTwoSum h1 l2 = (h3, l3))
    (l4 ll4 : Float) (e4 : fastTwoSum l3 ll2 = (l4, ll4)) (cond : Bool) :
    AccPair L sx (if cond = true then
        (h3, l4 * (1.0 + Lgamma.copySign (Float.ofBits 0x3E50000000000000) l4 *
          Lgamma.copySign (Float.ofBits 0x3E50000000000000) ll4))
      else (h3, l4)) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hbB
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) hcC
  obtain ⟨f1, f2, herr, hr2, -⟩ := LgammaAccNorm.norm_spec a b c ha hb hc B C (haA.trans hA)
    hbB hB hcC hC h1 l1 e1 l2 ll2 e2 h3 l3 e3 l4 ll4 e4 cond
  generalize (if cond = true then
        (h3, l4 * (1.0 + Lgamma.copySign (Float.ofBits 0x3E50000000000000) l4 *
          Lgamma.copySign (Float.ofBits 0x3E50000000000000) ll4))
      else (h3, l4)) = r at f1 f2 herr hr2 ⊢
  set α := |value a.toBits| with hα
  set v1 := value r.1.toBits with hv1
  set v2 := value r.2.toBits with hv2
  set S := value a.toBits + value b.toBits + value c.toBits with hS
  set Et := E + (B + C) / 2 ^ 52 + (A + B + C) / 2 ^ 99 + 1 / 2 ^ 1070 with hEt
  have hα0 : 0 ≤ α := abs_nonneg _
  have hαA : (α + B + C) / 2 ^ 99 ≤ (A + B + C) / 2 ^ 99 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have htot : |L - (v1 + v2)| ≤ Et := by
    have h := abs_add_le (S - L) (v1 + v2 - S)
    rw [show S - L + (v1 + v2 - S) = v1 + v2 - L by ring, abs_sub_comm] at h
    linarith
  have t1 : α ≤ |S| + B + C := by
    have h := abs_add_le S (-(value b.toBits + value c.toBits))
    have h' := abs_add_le (value b.toBits) (value c.toBits)
    rw [abs_neg, show S + -(value b.toBits + value c.toBits) = value a.toBits by
      rw [hS]; ring] at h
    linarith
  have t2 : |S| ≤ |v1| + |v2| + ((B + C) / 2 ^ 52 + (α + B + C) / 2 ^ 99 + 1 / 2 ^ 1070) := by
    have h := abs_sub_abs_le_abs_sub S (v1 + v2)
    rw [abs_sub_comm] at h
    have h' := abs_add_le v1 v2
    linarith
  have hsmall : |v1| < 3 / 8 → |v2| ≤ 1 / 2 ^ 48 := by
    intro h38
    have t3 : α ≤ 1 / 2 := by linarith
    linarith
  have hlarge : |v2| ≤ (|v1| + 1) / 2 ^ 47 := by linarith
  refine ⟨f1, f2, fun h38 => ?_, fun hroot => ?_⟩
  · have h2 := hsmall h38
    have h := abs_sub_abs_le_abs_sub L (v1 + v2)
    have h' := abs_add_le v1 v2
    linarith
  · refine htot.trans (hbud r.1 f1 (fun h38 => ?_) (fun h38 => ?_) hroot)
    have h2 := hsmall h38
    have h := abs_sub_abs_le_abs_sub (v1 + v2) L
    rw [abs_sub_comm] at h
    have h' := abs_add_le v1 v2
    have h'' : |v1| ≤ |v1 + v2| + |v2| := by
      have := abs_add_le (v1 + v2) (-v2)
      rw [abs_neg, show v1 + v2 + -v2 = v1 by ring] at this
      exact this
    linarith
    have h := abs_sub_abs_le_abs_sub (v1 + v2) L
    rw [abs_sub_comm] at h
    have h'' : |v1| ≤ |v1 + v2| + |v2| := by
      have := abs_add_le (v1 + v2) (-v2)
      rw [abs_neg, show v1 + v2 + -v2 = v1 by ring] at this
      exact this
    have h3 := abs_sub_abs_le_abs_sub L (v1 + v2)
    linarith

end Verified.Examples.LgammaAccPair
