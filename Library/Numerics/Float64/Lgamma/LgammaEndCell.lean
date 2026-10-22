import Library.Numerics.Float64.Lgamma.LgammaWalk

/-!
The rounding test of the fast path of `Lgamma.lgammaWith` when the exact results of both of its
sums lie in the rounding cell of one word.  Let `W` be a finite word with magnitude word `m`, and
let the cell of `W` be the open interval between the midpoint of `m - 1` and `m` and that of `m`
and `m + 1`, with the sign of `W`.  A rounded value of a number in the cell is `W` (`cell_eq`):
any other magnitude lies at least as far as the next word, which is farther than `W` from every
point of the cell.  `test_pass` applies this to `fh + (fl + eps)` and `fh + (fl - eps)` when
`fh + fl` lies within `R` of `L`, `eps ≤ E`, and `|fl| ≤ F`, so that both sums lie within
`M = R + E + (F + E)/2^53` of `L`.  `select_end` gives one step for the code's choice when the cell
of `W` holds the interval of radius `M` around `L`, without a bound on the accurate path.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaEndCell
open CodeLib.IEEE64 LeanExe.ProofKit F64RoundNearest F64Approx

set_option exponentiation.threshold 4096

/-- The value of a word below `2^63` is at most the value of a word with a larger or equal index. -/
theorem value_mono {a b : UInt64} (hb : b.toNat < 2 ^ 63) (h : a.toNat ≤ b.toNat) :
    value a ≤ value b := by
  rcases Nat.lt_or_ge a.toNat b.toNat with hlt | hge
  · exact (F64PositiveOrder.value_strict hb hlt).le
  · have : a = b := UInt64.toNat_inj.mp (le_antisymm h hge)
    rw [this]

/-- **A rounded value of a number in the cell of `W` is `W`.** -/
theorem cell_eq (c W : UInt64) (S : ℝ) (hc : Rounded c S) (hS0 : S ≠ 0)
    (hsg : Wasm.IEEE64.sign W = decide (S < 0)) (hW1 : 1 ≤ W.toNat % 2 ^ 63)
    (hWm : W.toNat % 2 ^ 63 + 1 < 2 ^ 63)
    (hlo : value (UInt64.ofNat (W.toNat % 2 ^ 63 - 1)) + |value W| < 2 * |S|)
    (hhi : 2 * |S| < |value W| + value (UInt64.ofNat (W.toNat % 2 ^ 63 + 1))) : c = W := by
  obtain ⟨-, hneg, hpos, hnear⟩ := hc
  have key := hnear W
  have hcN := F64UpperWord.abs_toNat c
  have hWN := F64UpperWord.abs_toNat W
  have hcv := F64UpperWord.value_abs c
  have hWv := F64UpperWord.value_abs W
  have hc63 : (Wasm.IEEE64.abs c).toNat < 2 ^ 63 := by rw [hcN]; exact Nat.mod_lt _ (by norm_num)
  have hup : (UInt64.ofNat (W.toNat % 2 ^ 63 + 1)).toNat = W.toNat % 2 ^ 63 + 1 :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hdn : (UInt64.ofNat (W.toNat % 2 ^ 63 - 1)).toNat = W.toNat % 2 ^ 63 - 1 :=
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)
  have hWup : |value W| < value (UInt64.ofNat (W.toNat % 2 ^ 63 + 1)) := by
    rw [← hWv]
    exact F64PositiveOrder.value_strict (by rw [hup]; exact hWm) (by rw [hup, hWN]; omega)
  have hWdn : value (UInt64.ofNat (W.toNat % 2 ^ 63 - 1)) < |value W| := by
    rw [← hWv]
    exact F64PositiveOrder.value_strict (by rw [hWN]; exact Nat.mod_lt _ (by norm_num))
      (by rw [hdn, hWN]; omega)
  have hm : c.toNat % 2 ^ 63 = W.toNat % 2 ^ 63 := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have hle : value (Wasm.IEEE64.abs c) ≤ value (UInt64.ofNat (W.toNat % 2 ^ 63 - 1)) :=
        value_mono (by rw [hdn]; omega) (by rw [hdn, hcN]; omega)
      rw [hcv] at hle
      have h1 : |value W| - |S| < |S| - |value c| := by linarith
      have h2 : |S| - |value W| < |S| - |value c| := by linarith
      have h3 : abs (|value W| - |S|) < abs (|value c| - |S|) := by
        rw [abs_sub_comm (|value c|), abs_of_pos (by linarith : 0 < |S| - |value c|)]
        exact abs_lt.mpr ⟨by linarith, h1⟩
      linarith
    · have hle : value (UInt64.ofNat (W.toNat % 2 ^ 63 + 1)) ≤ value (Wasm.IEEE64.abs c) :=
        value_mono hc63 (by rw [hup, hcN]; omega)
      rw [hcv] at hle
      have h1 : |S| - |value W| < |value c| - |S| := by linarith
      have h2 : |value W| - |S| < |value c| - |S| := by linarith
      have h3 : abs (|value W| - |S|) < abs (|value c| - |S|) := by
        rw [abs_of_pos (by linarith : 0 < |value c| - |S|)]
        exact abs_lt.mpr ⟨by linarith, h2⟩
      linarith
  have hs : Wasm.IEEE64.sign c = Wasm.IEEE64.sign W := by
    rw [hsg]
    rcases lt_or_gt_of_ne hS0 with h | h
    · rw [hneg h, decide_eq_true h]
    · rw [hpos h, decide_eq_false (not_lt.mpr h.le)]
  have hcs : (2 ^ 63 ≤ c.toNat ↔ 2 ^ 63 ≤ W.toNat) := by
    simp only [Wasm.IEEE64.sign, decide_eq_decide] at hs
    exact hs
  have hc64 := c.toNat_lt
  have hW64 := W.toNat_lt
  apply UInt64.toNat_inj.mp
  by_cases h : 2 ^ 63 ≤ c.toNat
  · have h' := hcs.mp h
    omega
  · have h' : ¬ 2 ^ 63 ≤ W.toNat := fun hw => h (hcs.mpr hw)
    omega

/-- A number within `M` of `L`, with `M < |L|`, lies in the cell of `W` when the interval of radius
`M` around `L` does, so a rounded value of it is `W`. -/
theorem near_eq (c W : UInt64) (S L M : ℝ) (hc : Rounded c S) (hSL : |S - L| ≤ M)
    (hM : M < |L|) (hsg : Wasm.IEEE64.sign W = decide (L < 0)) (hW1 : 1 ≤ W.toNat % 2 ^ 63)
    (hWm : W.toNat % 2 ^ 63 + 1 < 2 ^ 63)
    (hlo : value (UInt64.ofNat (W.toNat % 2 ^ 63 - 1)) + |value W| < 2 * (|L| - M))
    (hhi : 2 * (|L| + M) < |value W| + value (UInt64.ofNat (W.toNat % 2 ^ 63 + 1))) : c = W := by
  have h1 := abs_sub_abs_le_abs_sub S L
  have h2 := abs_sub_abs_le_abs_sub L S
  rw [abs_sub_comm L S] at h2
  have hS0 : S ≠ 0 := by
    intro h
    rw [h, zero_sub, abs_neg] at hSL
    linarith
  have hsS : decide (S < 0) = decide (L < 0) := by
    have hd1 : L - S ≤ |S - L| := by rw [abs_sub_comm]; exact le_abs_self _
    have hd2 : S - L ≤ |S - L| := le_abs_self _
    rcases lt_or_gt_of_ne hS0 with h | h
    · have hL : L < 0 := by
        by_contra hL
        push Not at hL
        rw [abs_of_nonneg hL] at hM
        linarith
      rw [decide_eq_true h, decide_eq_true hL]
    · have hL : ¬ L < 0 := by
        intro hL
        rw [abs_of_neg hL] at hM
        linarith
      rw [decide_eq_false (not_lt.mpr h.le), decide_eq_false hL]
  exact cell_eq c W S hc hS0 (hsg.trans hsS.symm) hW1 hWm (by linarith) (by linarith)

/-- **The rounding test passes** when the interval of radius `M = R + E + (F + E)/2^53` around `L`
lies in the cell of `W`: both sums of the test are `W`, which lies within one step of `L`. -/
theorem test_pass (fh fl eps : Float) (W : UInt64) (L R E F : ℝ) (hfh : Finite fh.toBits)
    (hfl : Finite fl.toBits) (he : Finite eps.toBits) (he0 : 0 ≤ value eps.toBits)
    (heE : value eps.toBits ≤ E) (hflF : |value fl.toBits| ≤ F)
    (hR : |L - (value fh.toBits + value fl.toBits)| ≤ R) (hFE : F + E ≤ 1)
    (hrel : R + E + (F + E) / 2 ^ 53 ≤ |L| / 2 ^ 54) (hL1 : 1 / 2 ^ 1021 ≤ |L|)
    (hL2 : |L| < 2 ^ 1021) (hsg : Wasm.IEEE64.sign W = decide (L < 0))
    (hW1 : 1 ≤ W.toNat % 2 ^ 63) (hWm : W.toNat % 2 ^ 63 + 1 < 2 ^ 63)
    (hlo : value (UInt64.ofNat (W.toNat % 2 ^ 63 - 1)) + |value W| <
      2 * (|L| - (R + E + (F + E) / 2 ^ 53)))
    (hhi : 2 * (|L| + (R + E + (F + E) / 2 ^ 53)) <
      |value W| + value (UInt64.ofNat (W.toNat % 2 ^ 63 + 1))) :
    (fh + (fl + eps)).toBits = W ∧ (fh + (fl - eps)).toBits = W ∧
      F64SignedRounding.WithinSteps 1 L W := by
  set M := R + E + (F + E) / 2 ^ 53 with hMdef
  have hL0 : 0 < |L| := lt_of_lt_of_le (by positivity) hL1
  have hMt : M < |L| := by
    have : |L| / 2 ^ 54 < |L| := div_lt_self hL0 (by norm_num)
    linarith
  have hE0 : 0 ≤ E := he0.trans heE
  have hF0 : 0 ≤ F := (abs_nonneg _).trans hflF
  have ha := fapprox_add (approx_self _ hfl) (approx_self _ he) (F + E) (by
      rw [add_zero]
      have := abs_add_le (value fl.toBits) (value eps.toBits)
      rw [abs_of_nonneg he0] at this
      linarith) (by linarith [(by norm_num : (1 : ℝ) < 2 ^ 1023)])
  have hs := fapprox_sub (approx_self _ hfl) (approx_self _ he) (F + E) (by
      rw [add_zero]
      have := abs_sub (value fl.toBits) (value eps.toBits)
      rw [abs_of_nonneg he0] at this
      linarith) (by linarith [(by norm_num : (1 : ℝ) < 2 ^ 1023)])
  have hda : |value (fl + eps).toBits - (value fl.toBits + value eps.toBits)| ≤
      (F + E) / 2 ^ 53 := by
    have := ha.2
    simp only [zero_add] at this
    exact this
  have hds : |value (fl - eps).toBits - (value fl.toBits - value eps.toBits)| ≤
      (F + E) / 2 ^ 53 := by
    have := hs.2
    simp only [zero_add] at this
    exact this
  have hSa : |value fh.toBits + value (fl + eps).toBits - L| ≤ M := by
    have : value fh.toBits + value (fl + eps).toBits - L =
        (value (fl + eps).toBits - (value fl.toBits + value eps.toBits)) + value eps.toBits -
          (L - (value fh.toBits + value fl.toBits)) := by ring
    rw [this]
    have h3 := abs_sub (value (fl + eps).toBits - (value fl.toBits + value eps.toBits) +
      value eps.toBits) (L - (value fh.toBits + value fl.toBits))
    have h4 := abs_add_le (value (fl + eps).toBits - (value fl.toBits + value eps.toBits))
      (value eps.toBits)
    rw [abs_of_nonneg he0] at h4
    linarith
  have hSs : |value fh.toBits + value (fl - eps).toBits - L| ≤ M := by
    have : value fh.toBits + value (fl - eps).toBits - L =
        (value (fl - eps).toBits - (value fl.toBits - value eps.toBits)) - value eps.toBits -
          (L - (value fh.toBits + value fl.toBits)) := by ring
    rw [this]
    have h3 := abs_sub (value (fl - eps).toBits - (value fl.toBits - value eps.toBits) -
      value eps.toBits) (L - (value fh.toBits + value fl.toBits))
    have h4 := abs_sub (value (fl - eps).toBits - (value fl.toBits - value eps.toBits))
      (value eps.toBits)
    rw [abs_of_nonneg he0] at h4
    linarith
  have hround (S : ℝ) (hSL : |S - L| ≤ M) : S ≠ 0 ∧ |S| < 2 ^ 1023 := by
    have h1 := abs_sub_abs_le_abs_sub S L
    have h2 := abs_sub_abs_le_abs_sub L S
    rw [abs_sub_comm L S] at h2
    refine ⟨fun h => ?_, by linarith [(by norm_num : (2 : ℝ) ^ 1021 * 2 < 2 ^ 1023)]⟩
    rw [h, zero_sub, abs_neg] at hSL
    linarith
  have hRa := add_rounded fh.toBits (fl + eps).toBits hfh ha.1 (hround _ hSa).1 (hround _ hSa).2
  have hRs := add_rounded fh.toBits (fl - eps).toBits hfh hs.1 (hround _ hSs).1 (hround _ hSs).2
  rw [← F64Bits.toBits_add] at hRa hRs
  have hua := near_eq _ W _ L M hRa hSa hMt hsg hW1 hWm hlo hhi
  have hus := near_eq _ W _ L M hRs hSs hMt hsg hW1 hWm hlo hhi
  refine ⟨hua, hus, ?_⟩
  rw [hua] at hRa
  exact within_one_of_rounded_rel W _ L hRa (1 / 2 ^ 54) (by positivity) (by norm_num)
    (by rw [one_div_mul_eq_div]; exact hSa.trans hrel) hL1
    (by linarith [(by norm_num : (2 : ℝ) ^ 1021 < 2 ^ 1022)])

/-- **One step for the code's choice** when both sums of the rounding test are a finite word that
lies within one step of `L`: the test passes, and the code returns the fast result. -/
theorem select_end (fh fl eps sign acc : Float) (W : UInt64) (L : ℝ) (hW : Finite W)
    (hub : (fh + (fl + eps)).toBits = W) (hlb : (fh + (fl - eps)).toBits = W)
    (hin : F64SignedRounding.WithinSteps 1 L W) :
    F64SignedRounding.WithinSteps 1 L
      (if (fh + (fl + eps) != fh + (fl - eps)) = true then (acc, sign)
        else (fh + (fl + eps), sign)).1.toBits := by
  have hnan : Wasm.IEEE64.isNaN W = false := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at hW
    simp [Wasm.IEEE64.isNaN, hW]
  have ht : ¬ (fh + (fl + eps) != fh + (fl - eps)) = true := by
    rw [bne, F64Bits.beq_eq, hub, hlb]
    simp [Wasm.IEEE64.eq, hnan]
  rw [ite_eq_right ht, hub]
  exact hin

#print axioms cell_eq
#print axioms near_eq
#print axioms test_pass
#print axioms select_end

end Library.Numerics.Float64.Lgamma.LgammaEndCell
