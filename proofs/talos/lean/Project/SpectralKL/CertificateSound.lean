import Project.SpectralKL.CertificateBounds

namespace Project.SpectralKL.Certificate
open Matrix Samples Residual MeasureTheory Set intervalIntegral
open scoped Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem realVec_add (x y : n → ℚ) : realVec (x+y) = realVec x+realVec y := by
  ext i; simp [realVec]
theorem realVec_sub (x y : n → ℚ) : realVec (x-y) = realVec x-realVec y := by
  ext i; simp [realVec]
theorem realVec_smul (a : ℚ) (x : n → ℚ) : realVec (a•x) = (a:ℝ)•realVec x := by
  ext i; simp [realVec]

theorem cell_cast (p q : List (n → ℚ)) (eta a b : ℚ) (x : n → ℚ) :
    ((cell p q eta a b x).lower : ℝ) =
      (cell (realRows p) (realRows q) (eta:ℝ) (a:ℝ) (b:ℝ) (realVec x)).lower ∧
    ((cell p q eta a b x).upper : ℝ) =
      (cell (realRows p) (realRows q) (eta:ℝ) (a:ℝ) (b:ℝ) (realVec x)).upper := by
  constructor <;>
    simp only [cell, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one, dot_cast, realVec_add,
      realVec_sub, realVec_smul, mean_cast, action_cast]

theorem enclose_sound (p q : List (n → ℚ)) (eta : ℚ) (he : 0 < eta)
    (cells : List (ℚ × (n → ℚ))) (a : ℚ) (bound : Bounds ℚ)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (h : enclose p q eta a cells = some bound) :
    (bound.lower:ℝ) ≤ (∫ r in (a:ℝ)..1, integrand (realRows p) (realRows q) (eta:ℝ) r) ∧
      (∫ r in (a:ℝ)..1, integrand (realRows p) (realRows q) (eta:ℝ) r) ≤ (bound.upper:ℝ) := by
  have heR : (0:ℝ) < (eta:ℝ) := by exact_mod_cast he
  induction cells generalizing a bound with
  | nil =>
    simp only [enclose] at h
    split at h
    · rename_i heq
      subst a
      simp only [Option.some.injEq] at h
      subst bound
      simp
    · simp at h
  | cons c cs ih =>
    rcases c with ⟨b,x⟩
    simp only [enclose] at h
    split at h
    · rename_i hg
      cases ht : enclose p q eta b cs with
      | none => simp [ht] at h
      | some rest =>
        simp only [ht, Option.some.injEq] at h
        subst bound
        have hrest := ih b rest (hg.1.trans hg.2.1) hg.2.2 ht
        have haR : (0:ℝ) ≤ (a:ℝ) := by exact_mod_cast hg.1
        have habR : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hg.2.1
        have hbR : (b:ℝ) ≤ 1 := by exact_mod_cast hg.2.2
        have hcell := cell_sound (realRows p) (realRows q) (eta:ℝ) (a:ℝ) (b:ℝ)
          (realVec x) heR haR habR hbR
        rw [← (cell_cast p q eta a b x).1, ← (cell_cast p q eta a b x).2] at hcell
        have hs := integral_add_adjacent_intervals
          (integrand_integrable (realRows p) (realRows q) (eta:ℝ) heR haR habR hbR)
          (integrand_integrable (realRows p) (realRows q) (eta:ℝ) heR
            (haR.trans habR) hbR le_rfl)
        simp only [add, Rat.cast_add]
        rw [← hs]
        exact ⟨add_le_add hcell.1 hrest.1, add_le_add hcell.2 hrest.2⟩
    · simp at h

/-- Universal theorem about the actual executable acceptance function.
Any accepted score, from either backend, approximates the exact sample-based
regularized inverse-matrix integral within the requested tolerance. -/
theorem accepts_sound (p q : List (n → ℚ)) (eta score tolerance : ℚ)
    (cells : List (ℚ × (n → ℚ))) (h : accepts p q eta score tolerance cells = true) :
    |(score:ℝ)-target (realRows p) (realRows q) (eta:ℝ)| ≤ (tolerance:ℝ) := by
  unfold accepts at h
  split at h
  · simp at h
  · rename_i hg
    have he : 0 < eta := lt_of_not_ge (by intro hn; simp [hn] at hg)
    cases hb : enclose p q eta 0 cells with
    | none => simp [hb] at h
    | some bound =>
      simp only [hb, decide_eq_true_eq] at h
      have hs := enclose_sound p q eta he cells 0 bound le_rfl (by norm_num) hb
      have hl : (score:ℝ)-(tolerance:ℝ) ≤ (bound.lower:ℝ) := by exact_mod_cast h.1
      have hu : (bound.upper:ℝ) ≤ (score:ℝ)+(tolerance:ℝ) := by exact_mod_cast h.2
      simp only [Rat.cast_zero] at hs
      unfold target
      apply abs_le.mpr
      constructor <;> linarith [hs.1, hs.2]

#print axioms enclose_sound
#print axioms accepts_sound

/-- A successful checker result carries the mathematical guarantee in its
type. This is the function called by the command-line checker. -/
structure VerifiedScore (p q : List (n → ℚ)) (eta tolerance : ℚ) where
  score : ℚ
  accuracy : |(score:ℝ)-target (realRows p) (realRows q) (eta:ℝ)| ≤ (tolerance:ℝ)

def certify (p q : List (n → ℚ)) (eta score tolerance : ℚ)
    (cells : List (ℚ × (n → ℚ))) : Option (VerifiedScore p q eta tolerance) :=
  if h : accepts p q eta score tolerance cells = true then
    some ⟨score,accepts_sound p q eta score tolerance cells h⟩
  else none

theorem certify_score (p q : List (n → ℚ)) (eta score tolerance : ℚ)
    (cells : List (ℚ × (n → ℚ))) (result : VerifiedScore p q eta tolerance)
    (h : certify p q eta score tolerance cells = some result) : result.score = score := by
  unfold certify at h
  split at h
  · cases Option.some.inj h
    rfl
  · simp at h

#print axioms certify
end Project.SpectralKL.Certificate
