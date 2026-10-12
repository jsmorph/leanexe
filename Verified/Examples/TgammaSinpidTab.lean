import Verified.Examples.TgammaLogdParts
import Verified.Examples.TgammaApprox

/-!
The word checks of the tables of `Tgamma.asSinpid`.  `sinTabOK` checks, for each row
`k ≤ 64`, that the high part `hi k` is finite in `[0, 1]` and the low part `lo k` finite below
`2^-53 hi k`; that `hi (64 - k) ≤ 100 hi k` and `hi k ≥ 2^-60` from `k = 1` on; that
`2^53 |lo (64 - k)| + 0.1535 hi k ≤ 6.9 hi (64 - k)` up to `k = 63`; that row 0 is zero; and
that the kernel coefficients at 130 to 137 are the words of `Tgamma.sinpidTable`, which
`Lgamma.sinpiTable` repeats.  The kernel evaluates the check for `Tgamma.sinpidTable`.  `Ks` and
`Kc` are the kernels with the code's corrections `s0` and `c0`, equal to `TgammaApprox.sinPoly`
and `TgammaApprox.cosPoly` (`sinPoly_eq`, `cosPoly_eq`), and `coef_bounds` bounds the
coefficients.
-/

namespace Verified.Examples.TgammaSinpidTab
open CodeLib.IEEE64 LeanExe.ProofKit TgammaLogdTab

set_option exponentiation.threshold 4096

/-- A finite word. -/
def finW (w : UInt64) : Bool := decide (w.toNat % 2 ^ 63 < 0x7FF0000000000000)

/-- Row `ky` and its relations with row `64 - ky`. -/
def kyOK (tab : Array UInt64) (ky : ℕ) : Bool :=
  finW tab[2 * ky + 1]! && finW tab[2 * ky]! && decide (0 ≤ sv tab[2 * ky + 1]!) &&
    decide (sv tab[2 * ky + 1]! ≤ 2 ^ 1074) &&
    decide (|sv tab[2 * ky]!| * 2 ^ 53 ≤ sv tab[2 * ky + 1]!) &&
    (ky == 64 || decide (2 ^ 53 * |sv tab[2 * (64 - ky)]!| * 10000 + 1535 * sv tab[2 * ky + 1]! ≤
      69000 * sv tab[2 * (64 - ky) + 1]!)) &&
    (ky == 0 || (decide (sv tab[2 * (64 - ky) + 1]! ≤ 100 * sv tab[2 * ky + 1]!) &&
      decide (2 ^ 1014 ≤ sv tab[2 * ky + 1]!)))

def coefOK (tab : Array UInt64) : Bool :=
  tab[130]! == 0xBF33BD3CC9BE45DE && tab[131]! == 0x3E503C1F081B5AC4 &&
    tab[132]! == 0xBD555D3C7E3BD8BF && tab[133]! == 0x3C4E1F4826790653 &&
    tab[134]! == 0x3F9921FB54442D18 && tab[135]! == 0xBEC4ABBCE625BE53 &&
    tab[136]! == 0x3DD466BC67748EFC && tab[137]! == 0xBCD32D26E446373A

def sinTabOK (tab : Array UInt64) : Bool :=
  (List.range 65).all (kyOK tab) && tab[0]! == 0 && tab[1]! == 0 && coefOK tab

theorem sinTabOK_tgamma : sinTabOK Tgamma.sinpidTable = true := by decide +kernel

/-! ### The rows -/

theorem finW_spec (w : UInt64) (h : finW w = true) : Finite w := by
  unfold finW at h
  simp only [decide_eq_true_eq] at h
  exact TgammaLogdParts.finite_of_lt w h

theorem value_le_iff (w : UInt64) (c : ℤ) (q : ℝ) (hq : q = (c : ℝ) / 2 ^ 1074) :
    (sv w ≤ c) → value w ≤ q := by
  intro h
  rw [value_eq, hq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast h

/-- **A row of a checked table.** -/
theorem row_spec (tab : Array UInt64) (h : sinTabOK tab = true) (ky : ℕ) (hky : ky ≤ 64) :
    Finite tab[2 * ky + 1]! ∧ Finite tab[2 * ky]! ∧ 0 ≤ value tab[2 * ky + 1]! ∧
      value tab[2 * ky + 1]! ≤ 1 ∧ |value tab[2 * ky]!| ≤ value tab[2 * ky + 1]! / 2 ^ 53 ∧
      (ky ≤ 63 → 2 ^ 53 * |value tab[2 * (64 - ky)]!| + value tab[2 * ky + 1]! * (1535 / 10 ^ 4) ≤
        value tab[2 * (64 - ky) + 1]! * (69 / 10)) ∧
      (1 ≤ ky → value tab[2 * (64 - ky) + 1]! ≤ 100 * value tab[2 * ky + 1]! ∧
        1 / 2 ^ 60 ≤ value tab[2 * ky + 1]!) := by
  unfold sinTabOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have hk := h.1.1.1 ky (by omega)
  unfold kyOK at hk
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hk
  obtain ⟨⟨⟨⟨⟨⟨hf1, hf0⟩, h0⟩, h1⟩, hlo⟩, h63⟩, h1k⟩ := hk
  have hpos : (0 : ℝ) < 2 ^ 1074 := by positivity
  have cast_le : ∀ a b : ℤ, a ≤ b → (a : ℝ) / 2 ^ 1074 ≤ (b : ℝ) / 2 ^ 1074 := fun a b hab =>
    div_le_div_of_nonneg_right (by exact_mod_cast hab) hpos.le
  refine ⟨finW_spec _ hf1, finW_spec _ hf0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [value_eq]; exact div_nonneg (by exact_mod_cast h0) hpos.le
  · rw [value_eq]; have := cast_le _ _ h1; rw [Int.cast_pow, Int.cast_ofNat, div_self hpos.ne'] at this
    exact this
  · rw [value_eq, value_eq, abs_div, abs_of_pos hpos, div_div, mul_comm (2 ^ 1074 : ℝ) (2 ^ 53),
      ← div_div, div_le_div_iff_of_pos_right hpos, le_div_iff₀ (by positivity), ← Int.cast_abs]
    exact_mod_cast hlo
  · intro h63'
    rcases h63 with h | h
    · omega
    · have h' : ((2 ^ 53 * |sv tab[2 * (64 - ky)]!| * 10000 + 1535 * sv tab[2 * ky + 1]! : ℤ) : ℝ) ≤
          ((69000 * sv tab[2 * (64 - ky) + 1]! : ℤ) : ℝ) := by exact_mod_cast h
      push_cast at h'
      rw [value_eq, value_eq, value_eq, abs_div, abs_of_pos hpos]
      have e1 : (2 : ℝ) ^ 53 * (|(sv tab[2 * (64 - ky)]! : ℝ)| / 2 ^ 1074) +
          (sv tab[2 * ky + 1]! : ℝ) / 2 ^ 1074 * (1535 / 10 ^ 4) =
          (2 ^ 53 * |(sv tab[2 * (64 - ky)]! : ℝ)| * 10000 + 1535 * (sv tab[2 * ky + 1]! : ℝ)) /
            (10000 * 2 ^ 1074) := by ring
      have e2 : (sv tab[2 * (64 - ky) + 1]! : ℝ) / 2 ^ 1074 * (69 / 10) =
          69000 * (sv tab[2 * (64 - ky) + 1]! : ℝ) / (10000 * 2 ^ 1074) := by ring
      rw [e1, e2]
      apply div_le_div_of_nonneg_right _ (by positivity)
      norm_num at h' ⊢
      linarith
  · intro h1'
    rcases h1k with h | ⟨ha, hb⟩
    · omega
    · constructor
      · have h' : ((sv tab[2 * (64 - ky) + 1]! : ℤ) : ℝ) ≤ ((100 * sv tab[2 * ky + 1]! : ℤ) : ℝ) := by
          exact_mod_cast ha
        push_cast at h'
        rw [value_eq, value_eq, mul_div_assoc']
        exact div_le_div_of_nonneg_right h' hpos.le
      · rw [value_eq, le_div_iff₀ hpos]
        have : ((2 ^ 1014 : ℤ) : ℝ) ≤ (sv tab[2 * ky + 1]! : ℝ) := by exact_mod_cast hb
        have e : ((2 ^ 1014 : ℤ) : ℝ) = 1 / 2 ^ 60 * (2 : ℝ) ^ 1074 := by norm_num
        rw [e] at this
        exact this

theorem row_zero (tab : Array UInt64) (h : sinTabOK tab = true) :
    tab[0]! = 0 ∧ tab[1]! = 0 := by
  unfold sinTabOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.2, h.1.2⟩

theorem coef_words (tab : Array UInt64) (h : sinTabOK tab = true) :
    tab[130]! = 0xBF33BD3CC9BE45DE ∧ tab[131]! = 0x3E503C1F081B5AC4 ∧
      tab[132]! = 0xBD555D3C7E3BD8BF ∧ tab[133]! = 0x3C4E1F4826790653 ∧
      tab[134]! = 0x3F9921FB54442D18 ∧ tab[135]! = 0xBEC4ABBCE625BE53 ∧
      tab[136]! = 0x3DD466BC67748EFC ∧ tab[137]! = 0xBCD32D26E446373A := by
  unfold sinTabOK coefOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨-, ⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

/-! ### The kernels -/

/-- The sine kernel with the correction `s0`. -/
noncomputable def Ks (u : ℝ) : ℝ :=
  value (0x3F9921FB54442D18 : UInt64) + value (0x3C31A624B88C9448 : UInt64) +
    u * (value (0xBEC4ABBCE625BE53 : UInt64) + u * (value (0x3DD466BC67748EFC : UInt64) +
      u * value (0xBCD32D26E446373A : UInt64)))

/-- The cosine kernel with the correction `c0`. -/
noncomputable def Kc (u : ℝ) : ℝ :=
  value (0xBF33BD3CC9BE45DE : UInt64) + value (0xBBD692B66E3CF6E8 : UInt64) +
    u * (value (0x3E503C1F081B5AC4 : UInt64) + u * (value (0xBD555D3C7E3BD8BF : UInt64) +
      u * value (0x3C4E1F4826790653 : UInt64)))

theorem sinPoly_eq (u : ℝ) : TgammaApprox.sinPoly u = Ks u := by
  obtain ⟨-, -, -, -, h4, h5, h6, h7⟩ := coef_words _ sinTabOK_tgamma
  have hc : TgammaApprox.coeffs Tgamma.sinpidTable 135 1 3 = [TgammaApprox.q Tgamma.sinpidTable 135,
      TgammaApprox.q Tgamma.sinpidTable 136, TgammaApprox.q Tgamma.sinpidTable 137] := rfl
  rw [TgammaApprox.sinPoly, hc, Ks]
  simp only [PolyBound.eval_cons, PolyBound.eval_nil, mul_zero, add_zero, TgammaApprox.q,
    Rat.cast_add, PolyBound.ratOfWord_cast, h4, h5, h6, h7]

theorem cosPoly_eq (u : ℝ) : TgammaApprox.cosPoly u = Kc u := by
  obtain ⟨h0, h1, h2, h3, -, -, -, -⟩ := coef_words _ sinTabOK_tgamma
  have hc : TgammaApprox.coeffs Tgamma.sinpidTable 131 1 3 = [TgammaApprox.q Tgamma.sinpidTable 131,
      TgammaApprox.q Tgamma.sinpidTable 132, TgammaApprox.q Tgamma.sinpidTable 133] := rfl
  rw [TgammaApprox.cosPoly, hc, Kc]
  simp only [PolyBound.eval_cons, PolyBound.eval_nil, mul_zero, add_zero, TgammaApprox.q,
    Rat.cast_add, PolyBound.ratOfWord_cast, h0, h1, h2, h3]

/-- Bounds of a word's value from bounds of its rational value. -/
theorem word_bounds (w : UInt64) (a b : ℚ) (h : a ≤ PolyBound.ratOfWord w ∧ PolyBound.ratOfWord w ≤ b) :
    (a : ℝ) ≤ value w ∧ value w ≤ b := by
  rw [← PolyBound.ratOfWord_cast]
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

theorem lit_finite (w : UInt64) (h : finW w = true) : Finite w := finW_spec w h

/-- **The coefficient bounds.** -/
theorem coef_bounds :
    (1 / 4000 ≤ |value (0xBF33BD3CC9BE45DE : UInt64)| ∧
      |value (0xBF33BD3CC9BE45DE : UInt64)| ≤ 1 / 3300) ∧
    |value (0x3E503C1F081B5AC4 : UInt64)| ≤ 1 / 2 ^ 25 ∧
    |value (0xBD555D3C7E3BD8BF : UInt64)| ≤ 1 / 2 ^ 41 ∧
    |value (0x3C4E1F4826790653 : UInt64)| ≤ 1 / 2 ^ 58 ∧
    (2454 / 10 ^ 5 ≤ value (0x3F9921FB54442D18 : UInt64) ∧
      value (0x3F9921FB54442D18 : UInt64) ≤ 2455 / 10 ^ 5) ∧
    |value (0xBEC4ABBCE625BE53 : UInt64)| ≤ 2465 / 10 ^ 9 ∧
    |value (0x3DD466BC67748EFC : UInt64)| ≤ 1 / 2 ^ 33 ∧
    |value (0xBCD32D26E446373A : UInt64)| ≤ 1 / 2 ^ 49 ∧
    |value (0xBBD692B66E3CF6E8 : UInt64)| ≤ 1 / 2 ^ 65 ∧
    |value (0x3C31A624B88C9448 : UInt64)| ≤ 957 / 10 ^ 21 := by
  have b130 := word_bounds 0xBF33BD3CC9BE45DE (-1 / 3300) (-1 / 4000) (by decide +kernel)
  have b131 := word_bounds 0x3E503C1F081B5AC4 (-1 / 2 ^ 25) (1 / 2 ^ 25) (by decide +kernel)
  have b132 := word_bounds 0xBD555D3C7E3BD8BF (-1 / 2 ^ 41) (1 / 2 ^ 41) (by decide +kernel)
  have b133 := word_bounds 0x3C4E1F4826790653 (-1 / 2 ^ 58) (1 / 2 ^ 58) (by decide +kernel)
  have b134 := word_bounds 0x3F9921FB54442D18 (2454 / 10 ^ 5) (2455 / 10 ^ 5) (by decide +kernel)
  have b135 := word_bounds 0xBEC4ABBCE625BE53 (-2465 / 10 ^ 9) (2465 / 10 ^ 9) (by decide +kernel)
  have b136 := word_bounds 0x3DD466BC67748EFC (-1 / 2 ^ 33) (1 / 2 ^ 33) (by decide +kernel)
  have b137 := word_bounds 0xBCD32D26E446373A (-1 / 2 ^ 49) (1 / 2 ^ 49) (by decide +kernel)
  have bc0 := word_bounds 0xBBD692B66E3CF6E8 (-1 / 2 ^ 65) (1 / 2 ^ 65) (by decide +kernel)
  have bs0 := word_bounds 0x3C31A624B88C9448 (-957 / 10 ^ 21) (957 / 10 ^ 21) (by decide +kernel)
  push_cast at b130 b131 b132 b133 b134 b135 b136 b137 bc0 bs0
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ⟨b134.1, b134.2⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
    first
    | (rw [abs_of_neg (by linarith)]; linarith)
    | (rw [abs_le]; constructor <;> linarith)

theorem coef_finite : Finite (0xBF33BD3CC9BE45DE : UInt64) ∧ Finite (0x3E503C1F081B5AC4 : UInt64) ∧
    Finite (0xBD555D3C7E3BD8BF : UInt64) ∧ Finite (0x3C4E1F4826790653 : UInt64) ∧
    Finite (0x3F9921FB54442D18 : UInt64) ∧ Finite (0xBEC4ABBCE625BE53 : UInt64) ∧
    Finite (0x3DD466BC67748EFC : UInt64) ∧ Finite (0xBCD32D26E446373A : UInt64) ∧
    Finite (0xBBD692B66E3CF6E8 : UInt64) ∧ Finite (0x3C31A624B88C9448 : UInt64) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact lit_finite _ (by decide)

#print axioms sinTabOK_tgamma
#print axioms row_spec
#print axioms sinPoly_eq
#print axioms cosPoly_eq
#print axioms coef_bounds

end Verified.Examples.TgammaSinpidTab
