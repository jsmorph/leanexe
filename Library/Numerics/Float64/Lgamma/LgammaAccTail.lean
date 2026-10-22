import Library.Numerics.Float64.Lgamma.LgammaAccRoot
import Library.Numerics.Float64.Lgamma.LgammaAccWalk

/-!
**The last two steps of `Lgamma.accurate`**: the polynomials about the negative zeros and the
rounding with the table of hard cases.  `AccPair L sx (fh, fl)` states what the pair before these
steps must satisfy: when `|fh| < 3/8`, `|L| ≤ |fh| + 2^-46`, which bounds `|L|` for the selected
range (`LgammaAccRoot.root_leaf`), and, whenever no range is selected, an error of `fh + fl` within
`|L|/(2^53 + 1)`.  `tail_within` walks the code from that pair to the result and states it within
one step of `L`.  Its statement repeats the code's block with the code's matchers.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaAccTail
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound Tgamma LgammaWalk LgammaAccWalk

set_option exponentiation.threshold 4096

/-- The pair before the polynomials about the zeros. -/
abbrev AccPair (L : ℝ) (sx : Float) (p : Float × Float) : Prop :=
  Finite p.1.toBits ∧ Finite p.2.toBits ∧
    (|value p.1.toBits| < 3 / 8 → |L| ≤ |value p.1.toBits| + 1 / 2 ^ 46) ∧
    ((|value p.1.toBits| < 3 / 8 → Lgamma.rootRange p.1.abs sx = (0, 0, 0, 0.0)) →
      |L - (value p.1.toBits + value p.2.toBits)| ≤ |L| / (2 ^ 53 + 1))

/-- A range with `o = 0` is the empty range. -/
theorem rootRange_zero (afh sx : Float) (haf : Finite afh.toBits) (hsx : Finite sx.toBits)
    (o n k : UInt64) (sc : Float) (hr : Lgamma.rootRange afh sx = (o, n, k, sc))
    (ho : (o == 0) = true) : Lgamma.rootRange afh sx = (0, 0, 0, 0.0) := by
  rcases LgammaRootSel.rootRange_spec afh sx haf hsx _ hr with
      ⟨-, -, -, he⟩ | ⟨-, -, -, he⟩ | ⟨-, -, -, he⟩ | ⟨-, -, -, he⟩ | ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ | ⟨-, -, -, he⟩ | ⟨-, -, -, he⟩ | ⟨-, -, -, he⟩ | ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ | ⟨-, -, -, he⟩ | ⟨-, -, -, he⟩ | ⟨-, -, -, he⟩ | ⟨-, -, -, he⟩ |
      ⟨-, -, -, he⟩ | ⟨-, -, -, he⟩ | ⟨he, -⟩
  all_goals first
    | (simp only [Prod.mk.injEq] at he
       obtain ⟨rfl, -, -, -⟩ := he
       exact absurd ho (by decide))
    | (rw [hr]; exact he)

theorem c38 : Finite (Float.ofBits 4600427019358961664).toBits ∧
    value (Float.ofBits 4600427019358961664).toBits = 3 / 8 := by
  refine ⟨Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_finite _ (by decide), ?_⟩
  rw [Library.Numerics.Float64.Tgamma.TgammaWords.ofBits_value _ (by decide),
    show ratOfWord 4600427019358961664 = 3 / 8 by decide +kernel]
  norm_num

/-- The pair after the step about the zeros. -/
abbrev RelPair (L : ℝ) (p : Float × Float) : Prop :=
  Finite p.1.toBits ∧ Finite p.2.toBits ∧
    |L - (value p.1.toBits + value p.2.toBits)| ≤ |L| / (2 ^ 53 + 1)

theorem rel_of_55 (L : ℝ) (p : Float × Float) (h1 : Finite p.1.toBits) (h2 : Finite p.2.toBits)
    (h : |value p.1.toBits + value p.2.toBits - L| ≤ |L| / 2 ^ 55) : RelPair L p := by
  refine ⟨h1, h2, ?_⟩
  rw [abs_sub_comm]
  exact h.trans (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by norm_num))

set_option maxHeartbeats 4000000 in
/-- **The last two steps** within one step of `log |Γ sx|`. -/
theorem tail_within (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hRF : LgammaApprox.RootFact)
    (hRM : LgammaApprox.RootMinFact) (hDb : LgammaApprox.DbFact) (sx : Float)
    (hsx : Finite sx.toBits)
    (hL1 : 1 / 2 ^ 1000 ≤ |GammaBasic.lgamma (value sx.toBits)|)
    (hL2 : |GammaBasic.lgamma (value sx.toBits)| ≤ 2 ^ 1020)
    (fh fl : Float) (hP : AccPair (GammaBasic.lgamma (value sx.toBits)) sx (fh, fl)) :
    F64SignedRounding.WithinSteps 1 (GammaBasic.lgamma (value sx.toBits))
      (Lgamma.polyDD.match_1 (fun _ => Float)
        (if fh.abs < Float.ofBits 4600427019358961664 then
          Lgamma.accurate.match_1 (fun _ => Float × Float) (Lgamma.rootRange fh.abs sx) fun o n k sc =>
            if (o == 0) = true then (fh, fl)
            else
              Lgamma.polyDD.match_1 (fun _ => Float × Float)
                (fastTwoSum (entry Lgamma.accurateTable o + sx) (entry Lgamma.accurateTable (o + 1)))
                fun zh zl =>
                have zl := zl + entry Lgamma.accurateTable (o + 2)
                have sh := zh * sc
                have sl := zl * sc
                have fl := sh * Lgamma.polyD Lgamma.accurateTable (o + 3 + 2 * (n - k)) k sh
                Lgamma.polyDD.match_1 (fun _ => Float × Float)
                  (Lgamma.polyDD Lgamma.accurateTable (o + 3) (n - k) sh sl fl) fun fh fl => mulDD zh zl fh fl
        else (fh, fl))
        fun fh fl =>
          if fl.toBits + 2 &&& 4294967295 ≤ 2 then Lgamma.database Lgamma.dbTable sx (fh + fl) else fh + fl).toBits := by
  set L := GammaBasic.lgamma (value sx.toBits) with hLdef
  obtain ⟨hf1, hf2, hA, hB⟩ := hP
  simp only at hf1 hf2 hA hB
  obtain ⟨haf, hafv⟩ := Library.Numerics.Float64.Tgamma.TgammaFloor.abs_float fh hf1
  have hlt : fh.abs < Float.ofBits 4600427019358961664 ↔ |value fh.toBits| < 3 / 8 := by
    rw [F64UpperWord.float_lt_iff _ _ haf c38.1, hafv, c38.2]
  refine (?_ : (fun r : Float => F64SignedRounding.WithinSteps 1 L r.toBits) _)
  spec_step (RelPair L)
  · acc_step
    · intro hc
      have hc' := hlt.mp hc
      acc_step
      intro o n k sc hr
      acc_step
      · intro ho
        exact ⟨hf1, hf2, hB fun _ => rootRange_zero _ _ haf hsx o n k sc hr ho⟩
      · intro ho
        acc_step
        intro zh zl hT
        acc_step
        intro zl2 hzl2
        acc_step
        intro sh hsh
        acc_step
        intro sl hsl
        acc_step
        intro fl0 hfl0
        acc_step
        intro gh gl hD
        subst hzl2 hsh hsl hfl0
        obtain ⟨r1, r2, r3⟩ := LgammaAccRoot.root_leaf hF hRF hRM sx hsx fh hf1 (hA hc') o n k sc
          hr ho zh zl hT gh gl hD
        exact rel_of_55 L _ r1 r2 r3
    · intro hc
      have hc' : ¬ |value fh.toBits| < 3 / 8 := fun h => hc (hlt.mpr h)
      exact ⟨hf1, hf2, hB fun h => absurd h hc'⟩
  · intro a b hab
    obtain ⟨ha, hb, herr⟩ := hab
    exact LgammaAccFinal.final_step hDb sx hsx _ a b ha hb hL1 hL2 (1 / (2 ^ 53 + 1))
      (by positivity) le_rfl (by rw [one_div_mul_eq_div]; exact herr)

end Library.Numerics.Float64.Lgamma.LgammaAccTail
