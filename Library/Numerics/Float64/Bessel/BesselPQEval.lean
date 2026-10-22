import Library.Numerics.Float64.Bessel.BesselRatioEval
import Library.Numerics.Float64.Bessel.BesselCS
import LeanExe.ProofKit.BesselRatio

/-!
The evaluation of fdlibm's rational functions in `z = 1/x²` for `x ≥ 2`, as `Bessel.pAsym` and
`Bessel.qRatio` compute them.  `recip_sq` puts the computed `ẑ = 1/(x x)` within
`(2 + 2^-40) u / x²` of `1/x²`, with `u = 2 ^ -53`, for `2 ≤ x ≤ 2 ^ 130`.  `ratio_float` turns
`BesselRatioEval.pieces_cover` into a statement on the `Float` expression `hornerF R ẑ / hornerF S ẑ`
that the code evaluates.  `boundsOk` checks `|R/S| ≤ ρ` on pieces of the real `z`, and `eval_nonneg`
and `eval_nonpos` give the sign of a polynomial whose coefficients share one sign, as fdlibm's
numerators do.
-/

namespace Library.Numerics.Float64.Bessel.BesselPQEval
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound F64Approx F64Horner BesselRatioEval BesselCS

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

theorem one_bits : (1.0 : Float).toBits = 0x3FF0000000000000 := rfl

theorem value_one : value (0x3FF0000000000000 : UInt64) = 1 := by
  rw [← ratOfWord_cast]
  have : ratOfWord 0x3FF0000000000000 = 1 := by decide +kernel
  rw [this]
  norm_num

theorem fapprox_one : FApprox 1.0 1 0 := by
  unfold FApprox Approx
  rw [one_bits, value_one]
  exact ⟨by unfold CodeLib.IEEE64.Finite; decide, by simp⟩

theorem fapprox_exact (x : Float) (hxf : Finite x.toBits) : FApprox x (value x.toBits) 0 :=
  ⟨hxf, by simp⟩

theorem fmono {f : Float} {v e e' : ℝ} (h : FApprox f v e) (he : e ≤ e') : FApprox f v e' :=
  ⟨h.1, h.2.trans he⟩

/-- `1/(x x)` for `2 ≤ x ≤ 2 ^ 130`. -/
theorem recip_sq (x : Float) (hxf : Finite x.toBits) (h2 : 2 ≤ value x.toBits)
    (hb : value x.toBits ≤ 2 ^ 130) :
    FApprox (1.0 / (x * x)) (1 / value x.toBits ^ 2)
      ((2 + 1 / 2 ^ 40) * 𝐮 / value x.toBits ^ 2) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : 0 < 𝐮 := by rw [hu]; positivity
  set v := value x.toBits with hv
  have hv0 : 0 < v := by linarith
  have hx := fapprox_exact x hxf
  have ht4 : 4 ≤ v * v := by nlinarith
  have htb : v * v ≤ 2 ^ 260 := by
    have := mul_le_mul hb hb hv0.le (by positivity)
    rw [← pow_add] at this
    exact this
  have hm := fapprox_mul hx hx v v (by rw [abs_of_pos hv0]) (by rw [abs_of_pos hv0]) (v * v)
    (by simp) (by linarith [show (2 : ℝ) ^ 260 < 2 ^ 1022 by norm_num])
  simp only [zero_mul, mul_zero, add_zero, zero_add] at hm
  set t := v * v with ht
  set em := t / 2 ^ 53 + 1 / 2 ^ 1075 with hem
  have hη : (1 : ℝ) / 2 ^ 1075 ≤ t * 𝐮 / 2 ^ 1000 := by
    rw [hu]
    have : (1 : ℝ) / 2 ^ 1075 ≤ 4 * (1 / 2 ^ 53) / 2 ^ 1000 := by norm_num
    have h2 : 4 * (1 / 2 ^ 53 : ℝ) / 2 ^ 1000 ≤ t * (1 / 2 ^ 53) / 2 ^ 1000 := by gcongr
    linarith
  have hem' : em = t * 𝐮 + 1 / 2 ^ 1075 := by rw [hem, hu]; ring
  have hden : t * (1 - 2 * 𝐮) ≤ t - em := by
    rw [hem, hu]
    have : (1 : ℝ) / 2 ^ 1075 ≤ t / 2 ^ 53 := by
      rw [le_div_iff₀ (by positivity)]
      have : (1 : ℝ) / 2 ^ 1075 * 2 ^ 53 ≤ 4 := by norm_num
      linarith
    linarith
  have h12 : 0 < 1 - 2 * 𝐮 := by rw [hu]; norm_num
  have hdpos : 0 < t * (1 - 2 * 𝐮) := mul_pos (by linarith) h12
  have hd1 : 1 ≤ t - em := by
    have : 1 ≤ t * (1 - 2 * 𝐮) := by rw [hu]; nlinarith
    linarith
  have hemt : em < t := by linarith
  have hd := fapprox_div fapprox_one hm 1 t (by norm_num) (by rw [abs_of_pos (by linarith)])
    hemt ((1 + 0) / (t - em)) le_rfl (by
      rw [add_zero, div_lt_iff₀ (by linarith)]
      nlinarith [show (1 : ℝ) < 2 ^ 1022 by norm_num])
  have hval : (1 : ℝ) / t = 1 / v ^ 2 := by rw [ht, sq]
  refine fmono (fcongr hd hval) ?_
  have ht0 : 0 < t := by linarith
  have hut : 0 < 𝐮 / t := by positivity
  have k1 : (0 + 1 * em / t) / (t - em) ≤ 𝐮 / t * ((1 + 1 / 2 ^ 1000) / (1 - 2 * 𝐮)) := by
    have hnum : 0 + 1 * em / t ≤ 𝐮 * (1 + 1 / 2 ^ 1000) := by
      rw [zero_add, one_mul, hem', div_le_iff₀ ht0]
      linarith
    calc (0 + 1 * em / t) / (t - em) ≤ (𝐮 * (1 + 1 / 2 ^ 1000)) / (t * (1 - 2 * 𝐮)) :=
          div_le_div₀ (by positivity) hnum hdpos hden
      _ = 𝐮 / t * ((1 + 1 / 2 ^ 1000) / (1 - 2 * 𝐮)) := mul_div_mul_comm _ _ _ _
  have k2 : (1 + 0) / (t - em) / 2 ^ 53 ≤ 𝐮 / t * (1 / (1 - 2 * 𝐮)) := by
    calc (1 + 0) / (t - em) / 2 ^ 53 = 𝐮 / (t - em) := by rw [hu]; ring
      _ ≤ 𝐮 / (t * (1 - 2 * 𝐮)) := div_le_div_of_nonneg_left hu0.le hdpos hden
      _ = 𝐮 / t * (1 / (1 - 2 * 𝐮)) := by
          rw [← mul_div_mul_comm, mul_one]
  have k3 : (1 : ℝ) / 2 ^ 1075 ≤ 𝐮 / t * (1 / 2 ^ 700) := by
    rw [← mul_div_mul_comm, mul_one, hu, div_div, le_div_iff₀ (by positivity)]
    have : (1 : ℝ) / 2 ^ 1075 * (2 ^ 53 * (t * 2 ^ 700)) ≤
        1 / 2 ^ 1075 * (2 ^ 53 * (2 ^ 260 * 2 ^ 700)) := by gcongr
    have h2 : (1 : ℝ) / 2 ^ 1075 * (2 ^ 53 * (2 ^ 260 * 2 ^ 700)) ≤ 1 := by norm_num
    linarith
  have hK : (1 + 1 / 2 ^ 1000) / (1 - 2 * 𝐮) + 1 / (1 - 2 * 𝐮) + 1 / 2 ^ 700 ≤
      2 + 1 / 2 ^ 40 := by
    rw [hu]; norm_num
  have hfin : 𝐮 / t * ((1 + 1 / 2 ^ 1000) / (1 - 2 * 𝐮) + 1 / (1 - 2 * 𝐮) + 1 / 2 ^ 700) ≤
      𝐮 / t * (2 + 1 / 2 ^ 40) := mul_le_mul_of_nonneg_left hK hut.le
  have hgoal : (2 + 1 / 2 ^ 40) * 𝐮 / v ^ 2 = 𝐮 / t * (2 + 1 / 2 ^ 40) := by
    rw [sq, ← ht]; ring
  rw [hgoal]
  have hsplit : 𝐮 / t * ((1 + 1 / 2 ^ 1000) / (1 - 2 * 𝐮) + 1 / (1 - 2 * 𝐮) + 1 / 2 ^ 700) =
      𝐮 / t * ((1 + 1 / 2 ^ 1000) / (1 - 2 * 𝐮)) + 𝐮 / t * (1 / (1 - 2 * 𝐮)) +
        𝐮 / t * (1 / 2 ^ 700) := by ring
  linarith

theorem map_bits (ws : List UInt64) (h : ∀ w ∈ ws, Wasm.IEEE64.isNaN w = false) :
    (ws.map Float.ofBits).map Float.toBits = ws := by
  induction ws with
  | nil => rfl
  | cons w rest ih =>
    simp only [List.map_cons, F64Bits.toBits_ofBits, h w (by simp), Bool.false_eq_true, ite_false]
    rw [ih (fun w hw => h w (by simp [hw]))]

/-- The rounded quotient of two Horner evaluations, as the code writes them. -/
theorem ratio_float (rf sf : List Float) (wr ws : List UInt64) (R S : List ℚ)
    (hrf : rf.map Float.toBits = wr) (hsf : sf.map Float.toBits = ws)
    (hwr : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ)) wr R)
    (hws : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ)) ws S)
    (hR : R ≠ []) (hS : S ≠ []) (zf : Float) (hzf : Finite zf.toBits) (z : ℝ) (δ E a b : ℚ)
    (rest : List ℚ) (hck : piecesOk R S δ E a (b :: rest) = true)
    (hz : |value zf.toBits - z| ≤ δ) (hlo : (a : ℝ) ≤ value zf.toBits)
    (hhi : value zf.toBits ≤ lastD a (b :: rest)) :
    FApprox (hornerF rf zf / hornerF sf zf) (eval R z / eval S z) E := by
  unfold FApprox
  rw [F64Bits.toBits_div, hornerF_bits, hornerF_bits, hrf, hsf]
  exact pieces_cover R S δ E wr ws hwr hws hR hS zf.toBits hzf z hz a b rest hck hlo hhi

/-- `|R/S| ≤ ρ` with `S > 0` on one piece. -/
def boundOk (R S : List ℚ) (ρ lo hi : ℚ) : Bool :=
  decide (0 < lowBound S lo hi) && decide (magBound R lo hi ≤ ρ * lowBound S lo hi)

def boundsOk (R S : List ℚ) (ρ : ℚ) (a : ℚ) : List ℚ → Bool
  | [] => true
  | b :: rest => boundOk R S ρ a b && boundsOk R S ρ b rest

theorem bound_piece (R S : List ℚ) (ρ lo hi : ℚ) (h : boundOk R S ρ lo hi = true) (z : ℝ)
    (hlo : (lo : ℝ) ≤ z) (hhi : z ≤ hi) : 0 < eval S z ∧ |eval R z| ≤ ρ * eval S z := by
  simp only [boundOk, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 := lowBound_sound S lo hi z hlo hhi
  have h2 := magBound_sound R lo hi z hlo hhi
  have h3 : ((magBound R lo hi : ℚ) : ℝ) ≤ (ρ : ℝ) * (lowBound S lo hi : ℚ) := by exact_mod_cast h.2
  have h4 : (0 : ℝ) < lowBound S lo hi := by exact_mod_cast h.1
  have hρ : (0 : ℝ) ≤ ρ := by
    have h5 : (0 : ℝ) ≤ ρ * (lowBound S lo hi : ℚ) := ((abs_nonneg _).trans h2).trans h3
    exact nonneg_of_mul_nonneg_left h5 h4
  refine ⟨lt_of_lt_of_le h4 h1, ?_⟩
  calc |eval R z| ≤ magBound R lo hi := h2
    _ ≤ ρ * (lowBound S lo hi : ℚ) := h3
    _ ≤ ρ * eval S z := mul_le_mul_of_nonneg_left h1 hρ

theorem bounds_sound (R S : List ℚ) (ρ : ℚ) (z : ℝ) :
    ∀ (a : ℚ) (bs : List ℚ), bs ≠ [] → boundsOk R S ρ a bs = true → (a : ℝ) ≤ z →
      z ≤ lastD a bs → 0 < eval S z ∧ |eval R z| ≤ ρ * eval S z := by
  intro a bs
  induction bs generalizing a with
  | nil => intro h; exact absurd rfl h
  | cons b rest ih =>
    intro _ h hlo hhi
    simp only [boundsOk, Bool.and_eq_true] at h
    by_cases hb : z ≤ b
    · exact bound_piece R S ρ a b h.1 z hlo hb
    · push Not at hb
      cases rest with
      | nil =>
        simp only [lastD] at hhi
        linarith
      | cons c rest' => exact ih b (by simp) h.2 hb.le hhi

theorem ratio_abs (R S : List ℚ) (ρ : ℝ) (z : ℝ) (h : 0 < eval S z ∧ |eval R z| ≤ ρ * eval S z) :
    |eval R z / eval S z| ≤ ρ := by
  rw [abs_div, abs_of_pos h.1, div_le_iff₀ h.1]
  exact h.2

theorem eval_nonneg (p : List ℚ) (hp : ∀ c ∈ p, 0 ≤ c) (z : ℝ) (hz : 0 ≤ z) : 0 ≤ eval p z := by
  induction p with
  | nil => simp [eval]
  | cons a q ih =>
    rw [eval_cons]
    have ha : (0 : ℝ) ≤ a := by exact_mod_cast hp a (by simp)
    have hq := ih (fun c hc => hp c (by simp [hc]))
    positivity

theorem eval_nonpos (p : List ℚ) (hp : ∀ c ∈ p, c ≤ 0) (z : ℝ) (hz : 0 ≤ z) : eval p z ≤ 0 := by
  induction p with
  | nil => simp [eval]
  | cons a q ih =>
    rw [eval_cons]
    have ha : (a : ℝ) ≤ 0 := by exact_mod_cast hp a (by simp)
    have hq := ih (fun c hc => hp c (by simp [hc]))
    nlinarith

#print axioms recip_sq
#print axioms map_bits
#print axioms ratio_float
#print axioms bounds_sound
#print axioms ratio_abs
#print axioms eval_nonneg
#print axioms eval_nonpos

end Library.Numerics.Float64.Bessel.BesselPQEval
