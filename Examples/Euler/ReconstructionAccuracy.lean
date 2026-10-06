import Examples.Euler.RealState
import Examples.Euler.ReconstructedProgram
import Examples.Euler.Equations.Minmod
import LeanExe.ProofKit.F64SymmetricFaces
import LeanExe.ProofKit.F64Halving

/-! The accuracy of the reconstructed solver's rounded reconstruction against the exact minmod
reconstruction of `Equations.Minmod`.  The rounded slope differs from the exact slope of the
three input states by at most the larger rounding radius of its two differences.  The returned
faces differ from `center ∓ factor · slope` by the rounding of the offset and of each face plus the
factor times the slope error, and they average to the center up to their own rounding.  When the
stencil is linear, its subtractions are exact, and the limiter accepts the first factor 1/2, the
faces are exactly `center ∓ slope / 2`. -/

namespace Examples.Euler

open LeanExe.ProofKit
open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit.F64RoundingResidual (radius)
open LeanExe.ProofKit.F64SymmetricFaces (Certificate)

/-- A state's components as words. -/
def componentWords (q : Conserved) : Fin 4 → UInt64 :=
  ![q.density.toBits, q.mx.toBits, q.my.toBits, q.energy.toBits]

theorem vec_eq_value (q : Conserved) (i : Fin 4) : vec q i = value (componentWords q i) := by
  fin_cases i <;> rfl

theorem finite_iff (x : Float) : finite x = true ↔ Finite x.toBits :=
  F64Order.finiteBits_iff x.toBits

theorem finiteState_iff (q : Conserved) :
    finiteState q = true ↔ ∀ i, Finite (componentWords q i) := by
  simp only [finiteState, Bool.and_eq_true, finite_iff]
  constructor
  · rintro ⟨⟨⟨hr, hx⟩, hy⟩, he⟩ i
    fin_cases i <;> assumption
  · intro h
    exact ⟨⟨⟨h 0, h 1⟩, h 2⟩, h 3⟩

theorem admissibleState_finite {q : Conserved} (h : admissibleState q = true) :
    finiteState q = true := by
  have key : ∀ x : Float, decide (0 < x.toBits) = true →
      decide (x.toBits < 0x7FF0000000000000) = true → finite x = true :=
    fun x h1 h2 => finite_of_positive (by simp only [positive, h1, h2, Bool.and_self])
  simp only [admissibleState, stateGuard, narrowGuard, energyGuard, Bool.or_eq_true,
    Bool.and_eq_true] at h
  simp only [finiteState, Bool.and_eq_true]
  rcases h with h | h
  · exact ⟨⟨⟨key _ h.1.1.1.1.1.1.1 h.1.1.1.1.1.1.2, h.1.1.1.1.1.2⟩, h.1.1.1.1.2⟩,
      key _ h.1.1.1.2.1 h.1.1.1.2.2⟩
  · exact ⟨⟨⟨key _ h.1.1.1.1.1.1 h.1.1.1.1.1.2, h.1.1.1.1.2⟩, h.1.1.1.2⟩,
      key _ h.1.1.2.1 h.1.1.2.2⟩

/-! The rounded minmod is the exact minmod of the inputs' values. -/

theorem value_nonnegative (word : UInt64) (h : word < 0x8000000000000000) : 0 ≤ value word := by
  rw [F64Adjacent.unsigned_word_value word (UInt64.lt_iff_toNat_lt.mp h)]
  positivity

theorem value_nonpositive (word : UInt64) (h : ¬word < 0x8000000000000000) : value word ≤ 0 := by
  have hn : 2^63 ≤ word.toNat := by
    have hn : ¬word.toNat < 2^63 := UInt64.lt_iff_toNat_lt.not.mp h
    exact Nat.le_of_not_gt hn
  rw [F64Adjacent.negative_word_value word hn]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity)

theorem real_minmod (a b : Float) :
    real (minmod a b) = Equations.Minmod.minmod (real a) (real b) := by
  have hzero : value (0 : UInt64) = 0 := by
    norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]
  have horder : ¬absBits a.toBits ≤ absBits b.toBits → absBits b.toBits ≤ absBits a.toBits := by
    intro h
    rw [UInt64.le_iff_toNat_le] at h ⊢
    omega
  have hmono : ∀ x y : UInt64, absBits x ≤ absBits y → |value x| ≤ |value y| :=
    fun x y h => F64Order.abs_value_mono x y h
  simp only [real, minmod]
  by_cases ha : a.toBits < 0x8000000000000000 <;> by_cases hb : b.toBits < 0x8000000000000000
  · have hva := value_nonnegative _ ha
    have hvb := value_nonnegative _ hb
    simp only [ha, hb, decide_true, beq_self_eq_true, ite_true]
    split_ifs with hab
    · have hv := hmono _ _ hab
      rw [abs_of_nonneg hva, abs_of_nonneg hvb] at hv
      simp [Equations.Minmod.minmod, min_eq_left hv, max_eq_right hv, hva, hvb]
    · have hv := hmono _ _ (horder hab)
      rw [abs_of_nonneg hvb, abs_of_nonneg hva] at hv
      simp [Equations.Minmod.minmod, min_eq_right hv, max_eq_left hv, hva, hvb]
  · have hva := value_nonnegative _ ha
    have hvb := value_nonpositive _ hb
    simp [ha, hb, zero_toBits, hzero, Equations.Minmod.minmod, min_eq_right (hvb.trans hva),
      max_eq_left (hvb.trans hva), hva, hvb]
  · have hva := value_nonpositive _ ha
    have hvb := value_nonnegative _ hb
    simp [ha, hb, zero_toBits, hzero, Equations.Minmod.minmod, min_eq_left (hva.trans hvb),
      max_eq_right (hva.trans hvb), hva, hvb]
  · have hva := value_nonpositive _ ha
    have hvb := value_nonpositive _ hb
    simp only [ha, hb, decide_false, beq_self_eq_true, ite_true]
    split_ifs with hab
    · have hv := hmono _ _ hab
      rw [abs_of_nonpos hva, abs_of_nonpos hvb] at hv
      have hba : value b.toBits ≤ value a.toBits := by linarith
      simp [Equations.Minmod.minmod, min_eq_right hba, max_eq_left hba, hva, hvb]
    · have hv := hmono _ _ (horder hab)
      rw [abs_of_nonpos hvb, abs_of_nonpos hva] at hv
      have hab : value a.toBits ≤ value b.toBits := by linarith
      simp [Equations.Minmod.minmod, min_eq_left hab, max_eq_right hab, hva, hvb]

/-! The slope. -/

/-- The componentwise difference that `slope` computes. -/
def difference (a b : Conserved) : Conserved :=
  ⟨a.density - b.density, a.mx - b.mx, a.my - b.my, a.energy - b.energy⟩

theorem componentWords_difference (a b : Conserved) (i : Fin 4) :
    componentWords (difference a b) i =
      Wasm.IEEE64.sub (componentWords a i) (componentWords b i) := by
  fin_cases i <;> simp [componentWords, difference, F64Bits.toBits_sub]

/-- The componentwise minmod that `slope` computes. -/
def minmodState (a b : Conserved) : Conserved :=
  ⟨minmod a.density b.density, minmod a.mx b.mx, minmod a.my b.my, minmod a.energy b.energy⟩

theorem value_minmodState (a b : Conserved) (i : Fin 4) :
    value (componentWords (minmodState a b) i) =
      Equations.Minmod.minmod (value (componentWords a i)) (value (componentWords b i)) := by
  fin_cases i <;> exact real_minmod _ _

theorem slope_accepted (left center right : Conserved)
    (h : (slope left center right).status = 0) :
    (slope left center right).state =
        minmodState (difference center left) (difference right center) ∧
      finiteState (difference center left) = true ∧
      finiteState (difference right center) = true := by
  unfold slope at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hg
  · simp only [Bool.and_eq_true] at hg
    exact ⟨rfl, by simpa [finiteState, difference] using hg.1,
      by simpa [finiteState, difference] using hg.2⟩
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

theorem slope_value (left center right : Conserved) (h : (slope left center right).status = 0)
    (i : Fin 4) :
    value (componentWords (slope left center right).state i) = Equations.Minmod.minmod
      (value (Wasm.IEEE64.sub (componentWords center i) (componentWords left i)))
      (value (Wasm.IEEE64.sub (componentWords right i) (componentWords center i))) := by
  rw [(slope_accepted left center right h).1, value_minmodState, componentWords_difference,
    componentWords_difference]

/-- The exact minmod slope of the three states' values. -/
noncomputable def exactSlope (left center right : Conserved) : Fin 4 → ℝ :=
  Equations.Minmod.slope (vec left) (vec center) (vec right)

/-- The larger rounding radius of the two differences of component `i`. -/
noncomputable def slopeRadius (left center right : Conserved) (i : Fin 4) : ℝ :=
  max (radius (Wasm.IEEE64.sub (componentWords center i) (componentWords left i)))
    (radius (Wasm.IEEE64.sub (componentWords right i) (componentWords center i)))

theorem minmod_finite {a b : Float} (ha : finite a = true) (hb : finite b = true) :
    finite (minmod a b) = true := by
  have hZero : finite (0 : Float) = true := by
    simp only [finite, zero_toBits, absBits]; decide
  unfold minmod
  split_ifs <;> assumption

theorem slope_finite (left center right : Conserved) (h : (slope left center right).status = 0) :
    finiteState (slope left center right).state = true := by
  have hs := slope_accepted left center right h
  rw [hs.1]
  have hb := hs.2.1
  have hf := hs.2.2
  simp only [finiteState, Bool.and_eq_true] at hb hf ⊢
  exact ⟨⟨⟨minmod_finite hb.1.1.1 hf.1.1.1, minmod_finite hb.1.1.2 hf.1.1.2⟩,
    minmod_finite hb.1.2 hf.1.2⟩, minmod_finite hb.2 hf.2⟩

/-- The rounded slope differs from the exact slope by at most the larger rounding radius of its
two differences. -/
theorem slope_error (left center right : Conserved) (hl : finiteState left = true)
    (hc : finiteState center = true) (hr : finiteState right = true)
    (hs : (slope left center right).status = 0) (i : Fin 4) :
    |value (componentWords (slope left center right).state i) - exactSlope left center right i| ≤
      slopeRadius left center right i := by
  have hd := slope_accepted left center right hs
  have hb := (finiteState_iff _).mp hd.2.1 i
  have hf := (finiteState_iff _).mp hd.2.2 i
  rw [componentWords_difference] at hb hf
  have heLeft := F64RoundingResidual.sub_error (componentWords center i) (componentWords left i)
    ((finiteState_iff _).mp hc i) ((finiteState_iff _).mp hl i) hb
  have heRight := F64RoundingResidual.sub_error (componentWords right i) (componentWords center i)
    ((finiteState_iff _).mp hr i) ((finiteState_iff _).mp hc i) hf
  rw [slope_value left center right hs i]
  unfold exactSlope Equations.Minmod.slope slopeRadius
  rw [vec_eq_value, vec_eq_value, vec_eq_value]
  exact (Equations.Minmod.minmod_error _ _ _ _).trans (max_le_max heLeft heRight)

/-! The faces of one factor. -/

/-- The offset `factor · delta` that `candidate` computes. -/
def offset (factor : Float) (delta : Conserved) : Conserved :=
  ⟨factor * delta.density, factor * delta.mx, factor * delta.my, factor * delta.energy⟩

def sumState (a b : Conserved) : Conserved :=
  ⟨a.density + b.density, a.mx + b.mx, a.my + b.my, a.energy + b.energy⟩

theorem componentWords_offset (factor : Float) (delta : Conserved) (i : Fin 4) :
    componentWords (offset factor delta) i = Wasm.IEEE64.mul factor.toBits (componentWords delta i) := by
  fin_cases i <;> simp [componentWords, offset, F64Bits.toBits_mul]

theorem componentWords_sumState (a b : Conserved) (i : Fin 4) :
    componentWords (sumState a b) i = Wasm.IEEE64.add (componentWords a i) (componentWords b i) := by
  fin_cases i <;> simp [componentWords, sumState, F64Bits.toBits_add]

theorem candidate_accepted (center delta : Conserved) (factor : Float)
    (h : (candidate center delta factor).status = 0) :
    candidate center delta factor =
        ⟨0, difference center (offset factor delta), sumState center (offset factor delta),
          factor⟩ ∧
      finite factor = true ∧ finiteState (offset factor delta) = true ∧
      admissibleState (difference center (offset factor delta)) = true ∧
      admissibleState (sumState center (offset factor delta)) = true := by
  unfold candidate at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hg
  · simp only [Bool.and_eq_true] at hg
    exact ⟨rfl, hg.1.1.1, by simpa [finiteState, offset] using hg.1.1.2,
      by simpa [admissibleState, difference, offset] using hg.1.2,
      by simpa [admissibleState, sumState, offset] using hg.2⟩
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

/-- The faces of an accepted factor satisfy the rounding certificate of `F64SymmetricFaces`. -/
theorem candidate_certificate (center delta : Conserved) (factor : Float)
    (hc : finiteState center = true) (hd : finiteState delta = true)
    (h : (candidate center delta factor).status = 0) (i : Fin 4) :
    Certificate factor.toBits (componentWords center i) (componentWords delta i)
      (componentWords (candidate center delta factor).left i)
      (componentWords (candidate center delta factor).right i) := by
  have hg := candidate_accepted center delta factor h
  have hf := (finite_iff factor).mp hg.2.1
  have ho := (finiteState_iff _).mp hg.2.2.1 i
  have hl := (finiteState_iff _).mp (admissibleState_finite hg.2.2.2.1) i
  have hr := (finiteState_iff _).mp (admissibleState_finite hg.2.2.2.2) i
  rw [componentWords_offset] at ho
  rw [componentWords_difference, componentWords_offset] at hl
  rw [componentWords_sumState, componentWords_offset] at hr
  rw [hg.1]
  simp only [componentWords_difference, componentWords_sumState, componentWords_offset]
  exact F64SymmetricFaces.rounded_faces factor.toBits (componentWords center i)
    (componentWords delta i) hf ((finiteState_iff center).mp hc i)
    ((finiteState_iff delta).mp hd i) ho hl hr

/-! The limiter. -/

/-- The factor after `steps` halvings. -/
def factorAfter : Nat → Float → Float
  | 0, factor => factor
  | steps + 1, factor => factorAfter steps (0.5 * factor)

/-- Once a try accepts, the loop of `limitFactor` stops. -/
theorem limitFactor_go_stop (center delta : Conserved) (fuel : Nat) (factor : Float) :
    LeanExe.repeatWhile.go (fun x : UInt64 × Float => x.1 != 0)
      (fun x => tryFactor center delta x.2) fuel ((0 : UInt64), factor) = (0, factor) := by
  cases fuel <;> simp [LeanExe.repeatWhile.go]

/-- The loop of `limitFactor` from the state `(1, factor)`: either it ends without acceptance, or
it ends at status 0 with the factor after some number of halvings below its fuel, whose faces
pass. -/
theorem limitFactor_go (center delta : Conserved) (fuel : Nat) (factor : Float) :
    (LeanExe.repeatWhile.go (fun x : UInt64 × Float => x.1 != 0)
        (fun x => tryFactor center delta x.2) fuel ((1 : UInt64), factor)).1 ≠ 0 ∨
      ∃ steps < fuel,
        LeanExe.repeatWhile.go (fun x : UInt64 × Float => x.1 != 0)
            (fun x => tryFactor center delta x.2) fuel ((1 : UInt64), factor) =
          (0, factorAfter steps factor) ∧
        (candidate center delta (factorAfter steps factor)).status = 0 := by
  induction fuel generalizing factor with
  | zero => exact Or.inl (by simp [LeanExe.repeatWhile.go])
  | succ fuel ih =>
      have hStep : LeanExe.repeatWhile.go (fun x : UInt64 × Float => x.1 != 0)
          (fun x => tryFactor center delta x.2) (fuel + 1) ((1 : UInt64), factor) =
          LeanExe.repeatWhile.go (fun x : UInt64 × Float => x.1 != 0)
            (fun x => tryFactor center delta x.2) fuel (tryFactor center delta factor) := by
        simp [LeanExe.repeatWhile.go]
      rw [hStep]
      by_cases hAccept : (candidate center delta factor).status = 0
      · have hTry : tryFactor center delta factor = (0, factor) := by simp [tryFactor, hAccept]
        rw [hTry, limitFactor_go_stop]
        exact Or.inr ⟨0, Nat.zero_lt_succ fuel, rfl, hAccept⟩
      · have hTry : tryFactor center delta factor = (1, 0.5 * factor) := by
          simp [tryFactor, hAccept]
        rw [hTry]
        rcases ih (0.5 * factor) with h | ⟨steps, hs, hf, ha⟩
        · exact Or.inl h
        · exact Or.inr ⟨steps + 1, Nat.succ_lt_succ hs, by rw [hf]; rfl, ha⟩

/-- The limiter returns the cell average, or the faces of the factor after some number of
halvings of 1/2, below the number of trials, whose faces pass. -/
theorem limit_selected (trials : UInt64) (center delta : Conserved) :
    limit trials center delta = ⟨0, center, center, 0⟩ ∨
      ∃ steps < trials.toNat,
        limit trials center delta = candidate center delta (factorAfter steps 0.5) ∧
        (candidate center delta (factorAfter steps 0.5)).status = 0 := by
  have hDef : limitFactor trials center delta =
      LeanExe.repeatWhile.go (fun x : UInt64 × Float => x.1 != 0)
        (fun x => tryFactor center delta x.2) trials.toNat ((1 : UInt64), (0.5 : Float)) := rfl
  rcases limitFactor_go center delta trials.toNat 0.5 with h | ⟨steps, hs, hf, ha⟩
  · left
    rw [← hDef] at h
    unfold limit
    generalize limitFactor trials center delta = r at h ⊢
    obtain ⟨status, factor⟩ := r
    have hs : status ≠ 0 := h
    simp [hs]
  · right
    rw [← hDef] at hf
    refine ⟨steps, hs, ?_, ha⟩
    unfold limit
    rw [hf]
    simp

/-! The reconstruction. -/

theorem reconstruct_accepted (trials : UInt64) (left center right : Conserved)
    (h : (reconstruct trials left center right).status = 0) :
    admissibleState left = true ∧ admissibleState center = true ∧
      admissibleState right = true ∧ (slope left center right).status = 0 ∧
      reconstruct trials left center right = limit trials center (slope left center right).state := by
  unfold reconstruct at h ⊢
  dsimp only at h ⊢
  split_ifs at h ⊢ with hg
  · simp only [Bool.and_eq_true, beq_iff_eq] at hg
    exact ⟨hg.1.1.1, hg.1.1.2, hg.1.2, hg.2, rfl⟩
  · exact False.elim ((by decide : (1 : UInt64) ≠ 0) h)

/-- Face errors from a certificate and an error bound on the slope. -/
theorem face_errors_of_slope {factor center delta left right : UInt64}
    (h : Certificate factor center delta left right) (reference error : ℝ)
    (hd : |value delta - reference| ≤ error) :
    |value left - (value center - value factor * reference)| ≤
        radius (Wasm.IEEE64.mul factor delta) + radius left + |value factor| * error ∧
      |value right - (value center + value factor * reference)| ≤
        radius (Wasm.IEEE64.mul factor delta) + radius right + |value factor| * error := by
  have hf := F64SymmetricFaces.face_errors h
  have hp : |value factor * value delta - value factor * reference| ≤ |value factor| * error := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hd (abs_nonneg _)
  have hll := (abs_le.mp hf.1).1
  have hlu := (abs_le.mp hf.1).2
  have hrl := (abs_le.mp hf.2).1
  have hru := (abs_le.mp hf.2).2
  have hpl := (abs_le.mp hp).1
  have hpu := (abs_le.mp hp).2
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith

/-- The accuracy of an accepted reconstruction.  It returns the cell average, or the faces of the
factor after some number of halvings of 1/2 below the number of trials.  Each such face differs
from `center ∓ factor · exactSlope` by the rounding radius of the offset and of the face plus the
factor times the slope's error bound, and the two faces average to the center up to half the sum
of their rounding radii. -/
theorem reconstruct_accuracy (trials : UInt64) (left center right : Conserved)
    (h : (reconstruct trials left center right).status = 0) :
    reconstruct trials left center right = ⟨0, center, center, 0⟩ ∨
      ∃ steps < trials.toNat,
        (reconstruct trials left center right).factor = factorAfter steps 0.5 ∧
        ∀ i : Fin 4,
          let out := reconstruct trials left center right
          let delta := componentWords (slope left center right).state i
          let offsetRadius := radius (Wasm.IEEE64.mul out.factor.toBits delta)
          (|vec out.left i - (vec center i - real out.factor * exactSlope left center right i)| ≤
              offsetRadius + radius (componentWords out.left i) +
                |real out.factor| * slopeRadius left center right i ∧
            |vec out.right i - (vec center i + real out.factor * exactSlope left center right i)| ≤
              offsetRadius + radius (componentWords out.right i) +
                |real out.factor| * slopeRadius left center right i) ∧
          |(vec out.left i + vec out.right i) / 2 - vec center i| ≤
            (radius (componentWords out.left i) + radius (componentWords out.right i)) / 2 := by
  have hi := reconstruct_accepted trials left center right h
  rw [hi.2.2.2.2]
  rcases limit_selected trials center (slope left center right).state with hz | ⟨steps, hs, heq, ha⟩
  · exact Or.inl hz
  · have hc := candidate_accepted center (slope left center right).state
      (factorAfter steps 0.5) ha
    have hfactor : (candidate center (slope left center right).state
        (factorAfter steps 0.5)).factor = factorAfter steps 0.5 := by rw [hc.1]
    refine Or.inr ⟨steps, hs, by rw [heq, hfactor], ?_⟩
    intro i
    rw [heq]
    have hcert := candidate_certificate center (slope left center right).state
      (factorAfter steps 0.5) (admissibleState_finite hi.2.1)
      (slope_finite left center right hi.2.2.2.1)
      ha i
    have he := slope_error left center right (admissibleState_finite hi.1)
      (admissibleState_finite hi.2.1) (admissibleState_finite hi.2.2.1) hi.2.2.2.1 i
    dsimp only
    rw [hfactor]
    simp only [vec_eq_value, real]
    exact ⟨face_errors_of_slope hcert _ _ he, F64SymmetricFaces.average_error hcert⟩

/-! The factor. -/

theorem factorAfter_bounded (steps : Nat) (factor : Float)
    (h : F64Halving.Bounded factor.toBits) :
    F64Halving.Bounded (factorAfter steps factor).toBits ∧
      Wasm.IEEE64.scaledMagnitude (factorAfter steps factor).toBits ≤
        Wasm.IEEE64.scaledMagnitude factor.toBits := by
  induction steps generalizing factor with
  | zero => exact ⟨h, le_rfl⟩
  | succ steps ih =>
      have hh : F64Halving.Bounded (0.5 * factor).toBits ∧
          Wasm.IEEE64.scaledMagnitude (0.5 * factor).toBits ≤
            Wasm.IEEE64.scaledMagnitude factor.toBits := by
        rw [F64Bits.toBits_mul, half_toBits]
        exact F64Halving.half_preserves h
      have hi := ih _ hh.1
      exact ⟨hi.1, hi.2.trans hh.2⟩

/-- Every factor the limiter tries is finite and in `[0, 1/2]`. -/
theorem factorAfter_value (steps : Nat) :
    Finite (factorAfter steps 0.5).toBits ∧ 0 ≤ real (factorAfter steps 0.5) ∧
      real (factorAfter steps 0.5) ≤ 1 / 2 := by
  have h := (factorAfter_bounded steps 0.5 (by rw [half_toBits]; exact F64Halving.half_bounded)).1
  exact ⟨h.1, F64Halving.bounded_value h⟩

/-- Halving never increases the factor. -/
theorem factorAfter_nonincreasing (steps : Nat) (factor : Float)
    (h : F64Halving.Bounded factor.toBits) : real (factorAfter steps factor) ≤ real factor := by
  have hs := factorAfter_bounded steps factor h
  simp only [real, value, Wasm.IEEE64.scaledValue, hs.1.2.1, h.2.1, Bool.false_eq_true, ite_false,
    Int.cast_natCast]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hs.2) (by positivity)

/-- The factor of every reconstruction is finite and in `[0, 1/2]`. -/
theorem reconstruct_factor (trials : UInt64) (left center right : Conserved) :
    Finite (reconstruct trials left center right).factor.toBits ∧
      0 ≤ real (reconstruct trials left center right).factor ∧
      real (reconstruct trials left center right).factor ≤ 1 / 2 := by
  have hZero : Finite (0 : Float).toBits ∧ 0 ≤ real 0 ∧ real 0 ≤ 1 / 2 := by
    have h := F64Halving.zero_bounded
    rw [← zero_toBits] at h
    exact ⟨h.1, F64Halving.bounded_value h⟩
  by_cases hs : (reconstruct trials left center right).status = 0
  · have hi := reconstruct_accepted trials left center right hs
    rw [hi.2.2.2.2]
    rcases limit_selected trials center (slope left center right).state with hz | ⟨steps, _, heq, ha⟩
    · rw [hz]; exact hZero
    · rw [heq, (candidate_accepted _ _ _ ha).1]
      exact factorAfter_value steps
  · have hRejected : reconstruct trials left center right = rejectedFaces := by
      unfold reconstruct at hs ⊢
      dsimp only at hs ⊢
      split_ifs at hs ⊢ with hg
      · simp only [Bool.and_eq_true, beq_iff_eq] at hg
        exfalso
        apply hs
        rcases limit_selected trials center (slope left center right).state with hz | ⟨_, _, heq, ha⟩
        · rw [hz]
        · rw [heq]; exact ha
      · rfl
    rw [hRejected]
    exact hZero

/-! A linear profile. -/

/-- The three states lie on a line with offset `delta` in every component, and both
subtractions of the slope are exact. -/
def ExactLinearStencil (left center right : Conserved) (delta : Fin 4 → ℝ) : Prop :=
  ∀ i : Fin 4,
    vec left i = vec center i - delta i ∧ vec right i = vec center i + delta i ∧
      value (Wasm.IEEE64.sub (componentWords center i) (componentWords left i)) =
        vec center i - vec left i ∧
      value (Wasm.IEEE64.sub (componentWords right i) (componentWords center i)) =
        vec right i - vec center i

/-- The halving of the slope and the two face operations at factor 1/2 are exact. -/
def ExactFaceArithmetic (center delta : Conserved) : Prop :=
  ∀ i : Fin 4,
    value (componentWords (offset 0.5 delta) i) = vec delta i / 2 ∧
      value (componentWords (difference center (offset 0.5 delta)) i) =
        vec center i - value (componentWords (offset 0.5 delta) i) ∧
      value (componentWords (sumState center (offset 0.5 delta)) i) =
        vec center i + value (componentWords (offset 0.5 delta) i)

theorem slope_linear_exact (left center right : Conserved) (delta : Fin 4 → ℝ)
    (hs : (slope left center right).status = 0) (h : ExactLinearStencil left center right delta) :
    vec (slope left center right).state = delta := by
  funext i
  have hi := h i
  rw [vec_eq_value, slope_value left center right hs i, hi.2.2.1, hi.2.2.2, hi.1, hi.2.1]
  rw [show vec center i - (vec center i - delta i) = delta i by ring,
    show vec center i + delta i - vec center i = delta i by ring]
  exact Equations.Minmod.minmod_self _

/-- With at least one trial, when the limiter accepts factor 1/2, the faces are those of 1/2. -/
theorem limit_unrestricted (trials : UInt64) (center delta : Conserved)
    (hTrials : 0 < trials.toNat) (hf : (candidate center delta 0.5).status = 0) :
    limit trials center delta = candidate center delta 0.5 := by
  have hDef : limitFactor trials center delta =
      LeanExe.repeatWhile.go (fun x : UInt64 × Float => x.1 != 0)
        (fun x => tryFactor center delta x.2) trials.toNat ((1 : UInt64), (0.5 : Float)) := rfl
  obtain ⟨k, hk⟩ : ∃ k, trials.toNat = k + 1 := ⟨trials.toNat - 1, by omega⟩
  have hTry : tryFactor center delta 0.5 = (0, 0.5) := by simp [tryFactor, hf]
  have hRun : limitFactor trials center delta = (0, 0.5) := by
    rw [hDef, hk]
    simp only [LeanExe.repeatWhile.go, bne_iff_ne, ne_eq, one_ne_zero, not_false_eq_true,
      decide_true, if_true, hTry]
    exact limitFactor_go_stop center delta k 0.5
  unfold limit
  rw [hRun]
  simp

/-- When the stencil is linear with exact subtractions, the limiter accepts factor 1/2, and the
face arithmetic at 1/2 is exact, the reconstruction returns the exact faces `center ∓ delta / 2`.
-/
theorem reconstruct_linear (trials : UInt64) (left center right : Conserved) (delta : Fin 4 → ℝ)
    (hTrials : 0 < trials.toNat) (hl : admissibleState left = true)
    (hc : admissibleState center = true) (hr : admissibleState right = true)
    (hs : (slope left center right).status = 0)
    (hf : (candidate center (slope left center right).state 0.5).status = 0)
    (hLinear : ExactLinearStencil left center right delta)
    (hExact : ExactFaceArithmetic center (slope left center right).state) :
    ∀ i : Fin 4,
      vec (reconstruct trials left center right).left i = vec center i - delta i / 2 ∧
        vec (reconstruct trials left center right).right i = vec center i + delta i / 2 := by
  have hRecon : reconstruct trials left center right =
      limit trials center (slope left center right).state := by
    unfold reconstruct
    simp [hl, hc, hr, hs]
  rw [hRecon, limit_unrestricted trials center _ hTrials hf,
    (candidate_accepted center (slope left center right).state 0.5 hf).1]
  intro i
  have hDelta := congrFun (slope_linear_exact left center right delta hs hLinear) i
  have he := hExact i
  simp only [vec_eq_value]
  rw [he.2.1, he.2.2, he.1, ← vec_eq_value, hDelta]
  exact ⟨rfl, rfl⟩

end Examples.Euler
