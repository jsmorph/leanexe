import Verified.Examples.PowLogSum

/-!
The evaluation of `p` in `Pow.powLog`: `ar2 = r ar`, `ar3 = r ar2`, and
`p = ar3 (A1 + r A2 + ar2 (A3 + r A4 + ar2 (A5 + r A6)))`, every operation rounded, against
`PowLogTable.poly r`.  With `|r| ≤ ρ ≤ 23/4000`, every intermediate error is a multiple of a
power of `ρ` times the unit roundoff, plus multiples of the underflow allowance `μ` of a
product, and `p` lies within `(7/4) u ρ ^ 3 + 5 μ` of `poly r`.
-/

namespace Verified.Examples.PowLogPoly
open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack

set_option exponentiation.threshold 4096

/-- `p` on words, for the words `r` and `ar = A0 r`. -/
def pWord (r ar : UInt64) : UInt64 :=
  let ar2 := Wasm.IEEE64.mul r ar
  let ar3 := Wasm.IEEE64.mul r ar2
  Wasm.IEEE64.mul ar3
    (Wasm.IEEE64.add (Wasm.IEEE64.add 0xBFE5555555555560 (Wasm.IEEE64.mul r 0x3FE0000000000006))
      (Wasm.IEEE64.mul ar2
        (Wasm.IEEE64.add
          (Wasm.IEEE64.add 0x3FE999999959554E (Wasm.IEEE64.mul r 0xBFE555555529A47A))
          (Wasm.IEEE64.mul ar2
            (Wasm.IEEE64.add 0xBFF2495B9B4845E9 (Wasm.IEEE64.mul r 0x3FF0002B8B263FC3))))))

theorem coefficients :
    Finite 0xBFE5555555555560 ∧ Finite 0x3FE0000000000006 ∧ Finite 0x3FE999999959554E ∧
    Finite 0xBFE555555529A47A ∧ Finite 0xBFF2495B9B4845E9 ∧ Finite 0x3FF0002B8B263FC3 ∧
    |value 0xBFE5555555555560| ≤ 67 / 100 ∧ |value 0x3FE0000000000006| ≤ 51 / 100 ∧
    |value 0x3FE999999959554E| ≤ 81 / 100 ∧ |value 0xBFE555555529A47A| ≤ 67 / 100 ∧
    |value 0xBFF2495B9B4845E9| ≤ 115 / 100 ∧ |value 0x3FF0002B8B263FC3| ≤ 101 / 100 := by
  have h : PolyBound.qabs (PolyBound.ratOfWord 0xBFE5555555555560) ≤ 67 / 100 ∧
      PolyBound.qabs (PolyBound.ratOfWord 0x3FE0000000000006) ≤ 51 / 100 ∧
      PolyBound.qabs (PolyBound.ratOfWord 0x3FE999999959554E) ≤ 81 / 100 ∧
      PolyBound.qabs (PolyBound.ratOfWord 0xBFE555555529A47A) ≤ 67 / 100 ∧
      PolyBound.qabs (PolyBound.ratOfWord 0xBFF2495B9B4845E9) ≤ 115 / 100 ∧
      PolyBound.qabs (PolyBound.ratOfWord 0x3FF0002B8B263FC3) ≤ 101 / 100 := by decide +kernel
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have cast := fun {w : UInt64} {q : ℚ} (hq : PolyBound.qabs (PolyBound.ratOfWord w) ≤ q) =>
    show |value w| ≤ (q : ℝ) by
      have := PowLogTable.rat_le hq
      rwa [PolyBound.qabs_cast, PolyBound.ratOfWord_cast] at this
  refine ⟨by unfold CodeLib.IEEE64.Finite; decide, by unfold CodeLib.IEEE64.Finite; decide,
    by unfold CodeLib.IEEE64.Finite; decide, by unfold CodeLib.IEEE64.Finite; decide,
    by unfold CodeLib.IEEE64.Finite; decide, by unfold CodeLib.IEEE64.Finite; decide,
    (cast h1).trans (by norm_num), (cast h2).trans (by norm_num), (cast h3).trans (by norm_num),
    (cast h4).trans (by norm_num), (cast h5).trans (by norm_num), (cast h6).trans (by norm_num)⟩

/-- The facts about `ρ` and `μ` that the bounds below combine. -/
structure Facts (ρ μ : ℝ) : Prop where
  ρ0 : 0 ≤ ρ
  ρ1 : ρ ≤ 23 / 4000
  μ0 : 0 ≤ μ
  μ1 : μ ≤ 1 / 2 ^ 1000
  ρ2 : 0 ≤ ρ ^ 2
  ρ3 : 0 ≤ ρ ^ 3
  ρs : ρ ^ 2 ≤ 23 / 4000 * ρ
  ρs3 : ρ ^ 3 ≤ 23 / 4000 * ρ ^ 2
  ρμ : ρ * μ ≤ 23 / 4000 * μ
  ρ2μ : ρ ^ 2 * μ ≤ μ
  ρ3μ : ρ ^ 3 * μ ≤ μ
  μμ : μ * μ ≤ μ / 2 ^ 1000

theorem facts (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 23 / 4000) :
    Facts ρ multiplicationUnderflowEpsilon := by
  have hμ0 : 0 ≤ multiplicationUnderflowEpsilon := by norm_num [multiplicationUnderflowEpsilon]
  have hμ1 : multiplicationUnderflowEpsilon ≤ 1 / 2 ^ 1000 := by
    norm_num [multiplicationUnderflowEpsilon]
  have hρ2 := pow_nonneg hρ0 2
  have hρ3 := pow_nonneg hρ0 3
  have hρs : ρ ^ 2 ≤ 23 / 4000 * ρ := by nlinarith
  have hρs3 : ρ ^ 3 ≤ 23 / 4000 * ρ ^ 2 := by nlinarith
  exact ⟨hρ0, hρ1, hμ0, hμ1, hρ2, hρ3, hρs, hρs3, mul_le_mul_of_nonneg_right hρ1 hμ0,
    by nlinarith, by nlinarith, by nlinarith⟩

/-- `ar2 = r ar` and `ar3 = r ar2`. -/
theorem powers (r ar : UInt64) (ρ : ℝ) (hrf : Finite r) (haf : Finite ar)
    (har : value ar = value 0xBFE0000000000000 * value r) (hρ : |value r| ≤ ρ)
    (hF : Facts ρ multiplicationUnderflowEpsilon) :
    Approx (Wasm.IEEE64.mul r ar) (value r * (value 0xBFE0000000000000 * value r))
      (1 / 2 ^ 53 * ρ ^ 2 / 2 + multiplicationUnderflowEpsilon) ∧
    |value r * (value 0xBFE0000000000000 * value r)| ≤ ρ ^ 2 / 2 ∧
    Approx (Wasm.IEEE64.mul r (Wasm.IEEE64.mul r ar))
      (value r * (value r * (value 0xBFE0000000000000 * value r)))
      (101 / 100 * (1 / 2 ^ 53) * ρ ^ 3 + 2 * multiplicationUnderflowEpsilon) ∧
    |value r * (value r * (value 0xBFE0000000000000 * value r))| ≤ ρ ^ 3 / 2 := by
  obtain ⟨hρ0, hρ1, hμ0, hμ1, hρ2, hρ3, hρs, hρs3, hρμ, hρ2μ, hρ3μ, hμμ⟩ := hF
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  set μ := multiplicationUnderflowEpsilon
  set R := value r
  have hA0 := PowLogTable.a0_value
  have hR := approx_self r hrf
  have hAR : Approx ar (value 0xBFE0000000000000 * R) 0 := ⟨haf, by rw [har]; simp⟩
  have hARb : |value 0xBFE0000000000000 * R| ≤ ρ / 2 := by
    rw [hA0, abs_mul]
    norm_num
    linarith
  have e2 := (mul_approx hR hAR ρ (ρ / 2) hρ hARb (by nlinarith)).mono
    (e' := 1 / 2 ^ 53 * ρ ^ 2 / 2 + μ) (by rw [hu]; nlinarith)
  have b2' : |R * (value 0xBFE0000000000000 * R)| ≤ ρ ^ 2 / 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg R]
  have e3 := (mul_approx hR e2 ρ (ρ ^ 2 / 2) hρ b2' (by nlinarith)).mono
    (e' := 101 / 100 * (1 / 2 ^ 53) * ρ ^ 3 + 2 * μ) (by rw [hu]; nlinarith)
  have b3' : |R * (R * (value 0xBFE0000000000000 * R))| ≤ ρ ^ 3 / 2 := by
    rw [abs_mul]
    nlinarith [abs_nonneg R]
  exact ⟨e2, b2', e3, b3'⟩

/-- `c0 + r c1` for coefficients with `|c0| ≤ a` and `|c1| ≤ b`. -/
theorem affine (r c0 c1 : UInt64) (ρ a b : ℝ) (hrf : Finite r) (h0 : Finite c0)
    (h1 : Finite c1) (hb0 : |value c0| ≤ a) (hb1 : |value c1| ≤ b) (hb : 0 ≤ b) (hb2 : b ≤ 2)
    (ha : a + b * (23 / 4000) + 1 / 2 ^ 55 ≤ 3) (hρ : |value r| ≤ ρ)
    (hF : Facts ρ multiplicationUnderflowEpsilon) :
    Approx (Wasm.IEEE64.add c0 (Wasm.IEEE64.mul r c1)) (value c0 + value r * value c1)
      ((a + b * (23 / 4000) + 1 / 2 ^ 55 + b * (23 / 4000)) * (1 / 2 ^ 53) +
        multiplicationUnderflowEpsilon) ∧
    |value c0 + value r * value c1| ≤ a + b * (23 / 4000) := by
  obtain ⟨hρ0, hρ1, hμ0, hμ1, hρ2, hρ3, hρs, hρs3, hρμ, hρ2μ, hρ3μ, hμμ⟩ := hF
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  set μ := multiplicationUnderflowEpsilon
  have hR := approx_self r hrf
  have hrb : |value r * value c1| ≤ b * (23 / 4000) := by
    rw [abs_mul]
    nlinarith [abs_nonneg (value r), abs_nonneg (value c1)]
  have hm := (mul_approx hR (approx_self _ h1) ρ b hρ hb1 (by nlinarith)).mono
    (e' := b * (23 / 4000) * (1 / 2 ^ 53) + μ) (by rw [hu]; nlinarith)
  have hsum : |value c0 + value r * value c1| ≤ a + b * (23 / 4000) := by
    have := abs_add_le (value c0) (value r * value c1)
    linarith
  have hs := (add_approx (approx_self _ h0) hm (a + b * (23 / 4000) + 1 / 2 ^ 55)
    (by nlinarith) (by norm_num; linarith)).mono
    (e' := (a + b * (23 / 4000) + 1 / 2 ^ 55 + b * (23 / 4000)) * (1 / 2 ^ 53) + μ)
    (by rw [hu]; nlinarith)
  exact ⟨hs, hsum⟩

/-- A product `ar2 · c` for `|ar2| ≤ ρ ^ 2 / 2` and a bracket `c` within `γ u + 5 μ` of `C`,
with `|C| ≤ m ≤ 6/5`. -/
theorem scaled (ar2 c : UInt64) (ρ X2 C γ m : ℝ)
    (e2 : Approx ar2 X2 (1 / 2 ^ 53 * ρ ^ 2 / 2 + multiplicationUnderflowEpsilon))
    (b2 : |X2| ≤ ρ ^ 2 / 2) (ec : Approx c C (γ * (1 / 2 ^ 53) + 5 * multiplicationUnderflowEpsilon))
    (hC : |C| ≤ m) (hm0 : 0 ≤ m) (hm : m ≤ 6 / 5) (hγ0 : 0 ≤ γ) (hγ : γ ≤ 2)
    (hF : Facts ρ multiplicationUnderflowEpsilon) :
    Approx (Wasm.IEEE64.mul ar2 c) (X2 * C)
      ((γ / 2 + m / 2 + m / 2 + 1 / 2 ^ 40) * (1 / 2 ^ 53) * ρ ^ 2 +
        (m + 2) * multiplicationUnderflowEpsilon) ∧
      |X2 * C| ≤ m / 2 * ρ ^ 2 := by
  obtain ⟨hρ0, hρ1, hμ0, hμ1, hρ2, hρ3, hρs, hρs3, hρμ, hρ2μ, hρ3μ, hμμ⟩ := hF
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  set μ := multiplicationUnderflowEpsilon
  refine ⟨(mul_approx e2 ec (ρ ^ 2 / 2) m b2 hC (by nlinarith)).mono ?_, ?_⟩
  · rw [hu]
    have h1 : 0 ≤ γ * ρ ^ 2 := mul_nonneg hγ0 hρ2
    have h2 : 0 ≤ m * ρ ^ 2 := mul_nonneg hm0 hρ2
    have h3 : γ * ρ ^ 2 ≤ 2 * ρ ^ 2 := mul_le_mul_of_nonneg_right hγ hρ2
    have h4 : m * μ ≤ 6 / 5 * μ := mul_le_mul_of_nonneg_right hm hμ0
    have h5 : γ * μ ≤ 2 * μ := mul_le_mul_of_nonneg_right hγ hμ0
    have h6 : 0 ≤ m * μ := mul_nonneg hm0 hμ0
    have h7 : 0 ≤ γ * μ := mul_nonneg hγ0 hμ0
    nlinarith [mul_nonneg h1 hμ0, mul_nonneg h2 hμ0, mul_le_mul_of_nonneg_right h3 hμ0]
  · rw [abs_mul]
    nlinarith [abs_nonneg X2, abs_nonneg C]

/-- The last product `p = ar3 · B`. -/
theorem p_final (r ar : UInt64) (ρ : ℝ)
    (e3 : Approx (Wasm.IEEE64.mul r (Wasm.IEEE64.mul r ar))
      (value r * (value r * (value 0xBFE0000000000000 * value r)))
      (101 / 100 * (1 / 2 ^ 53) * ρ ^ 3 + 2 * multiplicationUnderflowEpsilon))
    (b3 : |value r * (value r * (value 0xBFE0000000000000 * value r))| ≤ ρ ^ 3 / 2)
    (hB : Approx
      (Wasm.IEEE64.add (Wasm.IEEE64.add 0xBFE5555555555560 (Wasm.IEEE64.mul r 0x3FE0000000000006))
        (Wasm.IEEE64.mul (Wasm.IEEE64.mul r ar)
          (Wasm.IEEE64.add
            (Wasm.IEEE64.add 0x3FE999999959554E (Wasm.IEEE64.mul r 0xBFE555555529A47A))
            (Wasm.IEEE64.mul (Wasm.IEEE64.mul r ar)
              (Wasm.IEEE64.add 0xBFF2495B9B4845E9 (Wasm.IEEE64.mul r 0x3FF0002B8B263FC3))))))
      (value 0xBFE5555555555560 + value r * value 0x3FE0000000000006 +
        value r * (value 0xBFE0000000000000 * value r) *
          (value 0x3FE999999959554E + value r * value 0xBFE555555529A47A +
            value r * (value 0xBFE0000000000000 * value r) *
              (value 0xBFF2495B9B4845E9 + value r * value 0x3FF0002B8B263FC3)))
      (7 / 5 * (1 / 2 ^ 53) + 4 * multiplicationUnderflowEpsilon))
    (bB : |value 0xBFE5555555555560 + value r * value 0x3FE0000000000006 +
        value r * (value 0xBFE0000000000000 * value r) *
          (value 0x3FE999999959554E + value r * value 0xBFE555555529A47A +
            value r * (value 0xBFE0000000000000 * value r) *
              (value 0xBFF2495B9B4845E9 + value r * value 0x3FF0002B8B263FC3))| ≤ 674 / 1000)
    (hF : Facts ρ multiplicationUnderflowEpsilon) :
    Finite (pWord r ar) ∧
      |value (pWord r ar) - PowLogTable.poly (value r)| ≤
        7 / 4 / 2 ^ 53 * ρ ^ 3 + 5 * multiplicationUnderflowEpsilon ∧
      |value (pWord r ar)| ≤ 35 / 100 * ρ ^ 3 + 5 * multiplicationUnderflowEpsilon := by
  obtain ⟨hρ0, hρ1, hμ0, hμ1, hρ2, hρ3, hρs, hρs3, hρμ, hρ2μ, hρ3μ, hμμ⟩ := hF
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  set μ := multiplicationUnderflowEpsilon
  have hp := (mul_approx e3 hB (ρ ^ 3 / 2) (674 / 1000) b3 bB (by nlinarith)).mono
    (e' := 7 / 4 / 2 ^ 53 * ρ ^ 3 + 5 * μ) (by rw [hu]; nlinarith)
  have hpoly : value r * (value r * (value 0xBFE0000000000000 * value r)) *
      (value 0xBFE5555555555560 + value r * value 0x3FE0000000000006 +
        value r * (value 0xBFE0000000000000 * value r) *
          (value 0x3FE999999959554E + value r * value 0xBFE555555529A47A +
            value r * (value 0xBFE0000000000000 * value r) *
              (value 0xBFF2495B9B4845E9 + value r * value 0x3FF0002B8B263FC3))) =
      PowLogTable.poly (value r) := by
    simp only [PowLogTable.poly]
  have hp' : Approx (pWord r ar) (PowLogTable.poly (value r)) (7 / 4 / 2 ^ 53 * ρ ^ 3 + 5 * μ) :=
    hp.congr hpoly
  refine ⟨hp'.1, hp'.2, ?_⟩
  have hpb : |PowLogTable.poly (value r)| ≤ ρ ^ 3 / 2 * (674 / 1000) := by
    rw [← hpoly, abs_mul]
    exact mul_le_mul b3 bB (abs_nonneg _) (by positivity)
  have := hp'.abs_le hpb
  nlinarith

theorem p_error (r ar : UInt64) (ρ : ℝ) (hrf : Finite r) (haf : Finite ar)
    (har : value ar = value 0xBFE0000000000000 * value r) (hρ : |value r| ≤ ρ)
    (hρ1 : ρ ≤ 23 / 4000) :
    Finite (pWord r ar) ∧
      |value (pWord r ar) - PowLogTable.poly (value r)| ≤
        7 / 4 / 2 ^ 53 * ρ ^ 3 + 5 * multiplicationUnderflowEpsilon ∧
      |value (pWord r ar)| ≤ 35 / 100 * ρ ^ 3 + 5 * multiplicationUnderflowEpsilon := by
  obtain ⟨f1, f2, f3, f4, f5, f6, b1, b2, b3, b4, b5, b6⟩ := coefficients
  have hρ0 : 0 ≤ ρ := (abs_nonneg _).trans hρ
  have hF := facts ρ hρ0 hρ1
  obtain ⟨e2, b2', e3, b3'⟩ := powers r ar ρ hrf haf har hρ hF
  set μ := multiplicationUnderflowEpsilon
  set R := value r
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  -- the three affine brackets
  obtain ⟨c56, bc56⟩ := affine r _ _ ρ (115 / 100) (101 / 100) hrf f5 f6 b5 b6 (by norm_num)
    (by norm_num) (by norm_num) hρ hF
  obtain ⟨c34, bc34⟩ := affine r _ _ ρ (81 / 100) (67 / 100) hrf f3 f4 b3 b4 (by norm_num)
    (by norm_num) (by norm_num) hρ hF
  obtain ⟨c12, bc12⟩ := affine r _ _ ρ (67 / 100) (51 / 100) hrf f1 f2 b1 b2 (by norm_num)
    (by norm_num) (by norm_num) hρ hF
  -- `ar2 (A5 + r A6)`
  obtain ⟨m56, bm56⟩ := scaled _ _ ρ _ _ (117 / 100) (116 / 100) e2 b2'
    (c56.mono (by
      have h := hF.μ0
      have hn : (115 / 100 + 101 / 100 * (23 / 4000) + 1 / 2 ^ 55 + 101 / 100 * (23 / 4000) :
          ℝ) * (1 / 2 ^ 53) ≤ 117 / 100 * (1 / 2 ^ 53) := by norm_num
      linarith)) (bc56.trans (by norm_num)) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hF
  -- `A3 + r A4 + ar2 (A5 + r A6)`
  obtain ⟨hρ0', hρ1', hμ0, hμ1, hρ2, hρ3, hρs, hρs3, hρμ, hρ2μ, hρ3μ, hμμ⟩ := hF
  have bs := abs_add_le (value 0x3FE999999959554E + R * value 0xBFE555555529A47A)
    (R * (value 0xBFE0000000000000 * R) *
      (value 0xBFF2495B9B4845E9 + R * value 0x3FF0002B8B263FC3))
  have s3456 := (add_approx c34 m56 (83 / 100) (by nlinarith) (by norm_num)).mono
    (e' := 17 / 10 * (1 / 2 ^ 53) + 5 * μ) (by rw [hu]; nlinarith)
  have bs3456 : |value 0x3FE999999959554E + R * value 0xBFE555555529A47A +
      R * (value 0xBFE0000000000000 * R) *
        (value 0xBFF2495B9B4845E9 + R * value 0x3FF0002B8B263FC3)| ≤ 82 / 100 := by
    nlinarith
  obtain ⟨m3456, bm3456⟩ := scaled _ _ ρ _ _ (17 / 10) (82 / 100) e2 b2' s3456 bs3456
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (facts ρ hρ0 hρ1)
  -- the bracket
  have bB := abs_add_le (value 0xBFE5555555555560 + R * value 0x3FE0000000000006)
    (R * (value 0xBFE0000000000000 * R) *
      (value 0x3FE999999959554E + R * value 0xBFE555555529A47A +
        R * (value 0xBFE0000000000000 * R) *
          (value 0xBFF2495B9B4845E9 + R * value 0x3FF0002B8B263FC3)))
  have hB := (add_approx c12 m3456 (68 / 100) (by nlinarith) (by norm_num)).mono
    (e' := 7 / 5 * (1 / 2 ^ 53) + 4 * μ) (by rw [hu]; nlinarith)
  have bB' : |value 0xBFE5555555555560 + R * value 0x3FE0000000000006 +
      R * (value 0xBFE0000000000000 * R) *
        (value 0x3FE999999959554E + R * value 0xBFE555555529A47A +
          R * (value 0xBFE0000000000000 * R) *
            (value 0xBFF2495B9B4845E9 + R * value 0x3FF0002B8B263FC3))| ≤ 674 / 1000 := by
    nlinarith
  exact p_final r ar ρ e3 b3' hB bB' (facts ρ hρ0 hρ1)

#print axioms coefficients
#print axioms facts
#print axioms powers
#print axioms affine
#print axioms scaled
#print axioms p_final
#print axioms p_error

end Verified.Examples.PowLogPoly
