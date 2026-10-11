import LeanExe.ProofKit.F64ErrorTrack
import LeanExe.ProofKit.PolyBound
import LeanExe.ProofKit.F64Bits

/-!
A verified error bound for Horner evaluation in binary64.  `hornerF [a₀, ..., aₙ] s` is
`a₀ + s * (a₁ + s * (... + s * aₙ))` as Lean's `Float` evaluates it, and `hornerW` is the same on
words.  For an argument whose value lies in `[lo, hi]`, `hornerErr cs lo hi` bounds the distance
of the computed value from the exact polynomial `eval cs`, where `cs` are the coefficients' values.
Each step applies `F64ErrorTrack.mul_approx` and `add_approx`, with the magnitude of each exact
partial polynomial bounded by `magBound`, the sum of the absolute coefficients shifted to the middle
of `[lo, hi]` and weighted by powers of its half-width, as `PolyBound.check` bounds a polynomial.
`hornerOK` checks that every bound stays far below the overflow threshold.  `lowBound` is the lower
bound on a polynomial over `[lo, hi]` that its shifted constant term and `magBound`'s terms give.
-/

namespace LeanExe.ProofKit.F64Horner
open CodeLib.IEEE64 PolyBound F64ErrorTrack

set_option exponentiation.threshold 4096

/-- Horner evaluation in `Float`. -/
def hornerF : List Float → Float → Float
  | [], _ => 0.0
  | [a], _ => a
  | a :: p, s => a + s * hornerF p s

/-- Horner evaluation on words. -/
def hornerW : List UInt64 → UInt64 → UInt64
  | [], _ => 0
  | [a], _ => a
  | a :: p, s => Wasm.IEEE64.add a (Wasm.IEEE64.mul s (hornerW p s))

theorem hornerF_bits (cs : List Float) (s : Float) :
    (hornerF cs s).toBits = hornerW (cs.map Float.toBits) s.toBits := by
  induction cs with
  | nil => rfl
  | cons a p ih =>
    cases p with
    | nil => rfl
    | cons b q =>
      simp only [hornerF, hornerW, List.map_cons] at ih ⊢
      rw [F64Bits.toBits_add, F64Bits.toBits_mul, ih]

/-- A bound on `|eval p x|` for `x` in `[lo, hi]`. -/
def magBound (p : List ℚ) (lo hi : ℚ) : ℚ := absSum ((hi - lo) / 2) (shift ((lo + hi) / 2) p)

theorem magBound_sound (p : List ℚ) (lo hi : ℚ) (x : ℝ) (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi) :
    |eval p x| ≤ magBound p lo hi := by
  have hle : (lo : ℝ) ≤ hi := hlo.trans hhi
  have hh : (0 : ℚ) ≤ (hi - lo) / 2 := by
    have : lo ≤ hi := by exact_mod_cast hle
    linarith
  have ht : |x - (((lo + hi) / 2 : ℚ) : ℝ)| ≤ (((hi - lo) / 2 : ℚ) : ℝ) := by
    push_cast
    rw [abs_le]
    constructor <;> linarith
  have he := abs_eval_le ((hi - lo) / 2) hh (shift ((lo + hi) / 2) p) _ ht
  rw [eval_shift, add_sub_cancel] at he
  exact he

/-- `max |lo| |hi|`. -/
def absMax (lo hi : ℚ) : ℚ := max |lo| |hi|

/-- The unit roundoff and the underflow term, as rationals. -/
def uQ : ℚ := 1 / 2 ^ 53
def etaQ : ℚ := 1 / 2 ^ 1075

/-- The error bound of Horner evaluation. -/
def hornerErr : List ℚ → ℚ → ℚ → ℚ
  | [], _, _ => 0
  | [_], _, _ => 0
  | a :: b :: p, lo, hi =>
    let e' := hornerErr (b :: p) lo hi
    let M' := magBound (b :: p) lo hi
    let S := absMax lo hi
    let ep := S * e' + uQ * (S * (M' + e')) + etaQ
    ep + uQ * (magBound (a :: b :: p) lo hi + ep)

/-- The bounds of every step stay far below the overflow threshold. -/
def hornerOK : List ℚ → ℚ → ℚ → Bool
  | [], _, _ => true
  | [_], _, _ => true
  | a :: b :: p, lo, hi =>
    let e' := hornerErr (b :: p) lo hi
    let M' := magBound (b :: p) lo hi
    let S := absMax lo hi
    let ep := S * e' + uQ * (S * (M' + e')) + etaQ
    hornerOK (b :: p) lo hi && decide (S * (M' + e') < 2 ^ 1000) &&
      decide (magBound (a :: b :: p) lo hi + ep < 2 ^ 1000)

theorem uQ_eq : ((uQ : ℚ) : ℝ) = unitRoundoff64 := by
  simp [uQ, unitRoundoff64]

theorem etaQ_eq : ((etaQ : ℚ) : ℝ) = multiplicationUnderflowEpsilon := by
  simp [etaQ, multiplicationUnderflowEpsilon, unitRoundoff64, minNormal64]

theorem magBound_nonneg (p : List ℚ) (lo hi : ℚ) (x : ℝ) (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi) :
    (0 : ℝ) ≤ magBound p lo hi :=
  (abs_nonneg _).trans (magBound_sound p lo hi x hlo hhi)

theorem absMax_bound (lo hi : ℚ) (x : ℝ) (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi) :
    |x| ≤ ((absMax lo hi : ℚ) : ℝ) := by
  simp only [absMax, Rat.cast_max, Rat.cast_abs]
  rw [abs_le]
  constructor
  · have := neg_abs_le (lo : ℝ)
    have := le_max_left |(lo : ℝ)| |(hi : ℝ)|
    linarith
  · have := le_abs_self (hi : ℝ)
    have := le_max_right |(lo : ℝ)| |(hi : ℝ)|
    linarith

theorem hornerErr_cons (a b : ℚ) (q : List ℚ) (lo hi : ℚ) :
    hornerErr (a :: b :: q) lo hi =
      (absMax lo hi * hornerErr (b :: q) lo hi +
          uQ * (absMax lo hi * (magBound (b :: q) lo hi + hornerErr (b :: q) lo hi)) + etaQ) +
        uQ * (magBound (a :: b :: q) lo hi +
          (absMax lo hi * hornerErr (b :: q) lo hi +
            uQ * (absMax lo hi * (magBound (b :: q) lo hi + hornerErr (b :: q) lo hi)) + etaQ)) :=
  rfl

theorem hornerErr_nonneg (cs : List ℚ) (lo hi : ℚ) (x : ℝ) (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi) :
    (0 : ℝ) ≤ hornerErr cs lo hi := by
  have hS : (0 : ℚ) ≤ absMax lo hi := le_trans (abs_nonneg lo) (le_max_left _ _)
  have hu : (0 : ℚ) ≤ uQ := by simp [uQ]
  have he : (0 : ℚ) ≤ etaQ := by simp [etaQ]
  have hM (p : List ℚ) : (0 : ℚ) ≤ magBound p lo hi := by
    exact_mod_cast magBound_nonneg p lo hi x hlo hhi
  suffices h : (0 : ℚ) ≤ hornerErr cs lo hi by exact_mod_cast h
  induction cs with
  | nil => simp [hornerErr]
  | cons a p ih =>
    cases p with
    | nil => simp [hornerErr]
    | cons b q =>
      rw [hornerErr_cons]
      have h1 := mul_nonneg hS ih
      have h2 := mul_nonneg hu (mul_nonneg hS (add_nonneg (hM (b :: q)) ih))
      have h3 : (0 : ℚ) ≤ absMax lo hi * hornerErr (b :: q) lo hi +
          uQ * (absMax lo hi * (magBound (b :: q) lo hi + hornerErr (b :: q) lo hi)) + etaQ := by
        linarith
      exact add_nonneg h3 (mul_nonneg hu (add_nonneg (hM _) h3))

/-- The computed Horner value of words with values `cs` at an argument in `[lo, hi]` lies within
`hornerErr cs lo hi` of `eval cs`. -/
theorem hornerW_approx (cs : List ℚ) (ws : List UInt64)
    (hrel : List.Forall₂ (fun (w : UInt64) (c : ℚ) => CodeLib.IEEE64.Finite w ∧ value w = (c : ℝ))
      ws cs) (hne : cs ≠ [])
    (lo hi : ℚ) (s : UInt64) (hs : CodeLib.IEEE64.Finite s) (hlo : (lo : ℝ) ≤ value s) (hhi : value s ≤ hi)
    (hok : hornerOK cs lo hi = true) :
    Approx (hornerW ws s) (eval cs (value s)) (hornerErr cs lo hi) := by
  induction hrel with
  | nil => exact absurd rfl hne
  | @cons w c ws' cs' hwc hrest ih =>
    cases hrest with
    | nil =>
      refine ⟨hwc.1, ?_⟩
      simp only [hornerW, eval_cons, eval_nil, mul_zero, add_zero, hornerErr, Rat.cast_zero]
      rw [hwc.2, sub_self, abs_zero]
    | @cons w' c' ws'' cs'' hwc' hrest' =>
      simp only [hornerOK, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨hok', hm1⟩, hm2⟩ := hok
      have hq := ih (by simp) hok'
      set e' := hornerErr (c' :: cs'') lo hi
      set M' := magBound (c' :: cs'') lo hi
      set S := absMax lo hi
      have hS := absMax_bound lo hi (value s) hlo hhi
      have hM' := magBound_sound (c' :: cs'') lo hi (value s) hlo hhi
      have he'0 := hornerErr_nonneg (c' :: cs'') lo hi (value s) hlo hhi
      have hm1' : ((S : ℚ) : ℝ) * (M' + e') < 2 ^ 1022 := by
        have : ((S * (M' + e') : ℚ) : ℝ) < 2 ^ 1000 := by exact_mod_cast hm1
        push_cast at this
        linarith [show (2 : ℝ) ^ 1000 ≤ 2 ^ 1022 by norm_num]
      have hp := mul_approx (approx_self s hs) hq (S : ℝ) (M' : ℝ) hS hM'
        (by rw [add_zero]; exact hm1')
      rw [zero_mul, add_zero, add_zero] at hp
      set ep : ℝ := (S : ℝ) * e' + unitRoundoff64 * ((S : ℝ) * (M' + e')) +
        multiplicationUnderflowEpsilon
      have hfull := magBound_sound (c :: c' :: cs'') lo hi (value s) hlo hhi
      rw [eval_cons] at hfull
      have hsum := add_approx (⟨hwc.1, by rw [hwc.2, sub_self, abs_zero]⟩ : Approx w c 0) hp
        ((magBound (c :: c' :: cs'') lo hi : ℝ) + ep) (by linarith) (by
          have : ((magBound (c :: c' :: cs'') lo hi +
              (S * e' + uQ * (S * (M' + e')) + etaQ) : ℚ) : ℝ) < 2 ^ 1000 := by exact_mod_cast hm2
          push_cast [uQ_eq, etaQ_eq] at this
          linarith [show (2 : ℝ) ^ 1000 ≤ 2 ^ 1023 by norm_num])
      refine hsum.congr (by simp only [eval_cons]) |>.mono (le_of_eq ?_)
      simp only [hornerErr]
      push_cast [uQ_eq, etaQ_eq]
      ring

/-- A lower bound on `eval p x` for `x` in `[lo, hi]`. -/
def lowBound (p : List ℚ) (lo hi : ℚ) : ℚ :=
  match shift ((lo + hi) / 2) p with
  | [] => 0
  | a :: q => a - (hi - lo) / 2 * absSum ((hi - lo) / 2) q

theorem lowBound_sound (p : List ℚ) (lo hi : ℚ) (x : ℝ) (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ hi) :
    ((lowBound p lo hi : ℚ) : ℝ) ≤ eval p x := by
  have hle : (lo : ℝ) ≤ hi := hlo.trans hhi
  have hh : (0 : ℚ) ≤ (hi - lo) / 2 := by
    have : lo ≤ hi := by exact_mod_cast hle
    linarith
  have ht : |x - (((lo + hi) / 2 : ℚ) : ℝ)| ≤ (((hi - lo) / 2 : ℚ) : ℝ) := by
    push_cast
    rw [abs_le]
    constructor <;> linarith
  have he : eval p x = eval (shift ((lo + hi) / 2) p) (x - (((lo + hi) / 2 : ℚ) : ℝ)) := by
    rw [eval_shift, add_sub_cancel]
  rw [he]
  unfold lowBound
  split
  · rename_i h
    rw [h]
    simp
  · rename_i a q h
    rw [h, eval_cons]
    have hq := abs_eval_le ((hi - lo) / 2) hh q _ ht
    have hm : |(x - (((lo + hi) / 2 : ℚ) : ℝ)) * eval q (x - (((lo + hi) / 2 : ℚ) : ℝ))| ≤
        (((hi - lo) / 2 : ℚ) : ℝ) * ((absSum ((hi - lo) / 2) q : ℚ) : ℝ) := by
      rw [abs_mul]
      exact mul_le_mul ht hq (abs_nonneg _) (by exact_mod_cast hh)
    have := (abs_le.mp hm).1
    push_cast at this ⊢
    linarith

#print axioms hornerF_bits
#print axioms magBound_sound
#print axioms hornerW_approx
#print axioms lowBound_sound

end LeanExe.ProofKit.F64Horner
