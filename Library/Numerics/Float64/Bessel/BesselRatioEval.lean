import LeanExe.ProofKit.F64Horner
import LeanExe.ProofKit.F64DivApprox
import LeanExe.ProofKit.PolyChecks
import LeanExe.ProofKit.PolyCalculus

/-!
The rounded quotient `R(ẑ)/S(ẑ)` of two Horner evaluations, as a distance from `R(z)/S(z)` for a
real `z` within `δ` of the computed argument `ẑ`.  On a piece `[lo, hi]` that contains `ẑ`,
`F64Horner.hornerW_approx` bounds the errors of both evaluations, `magBound` and `lowBound` bound
`|R|` above and `S` below, and `F64DivApprox.div_approx` bounds the rounded quotient.  The change
from `ẑ` to `z` is at most `L δ` by `F64DivApprox.ratio_lipschitz`, with
`L = magBound (R' S - R S') / (lowBound S)²` on `[lo - δ, hi + δ]`.  `ratioErr` is the sum, and
`pieceOk` asks the kernel to check it against a bound `E` together with the side conditions;
`piecesOk` runs the check on consecutive pieces of a list of breakpoints, so that `pieces_sound`
covers every `ẑ` from the first breakpoint to the last.
-/

namespace Library.Numerics.Float64.Bessel.BesselRatioEval
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound PolyChecks PolyCalculus F64Horner F64ErrorTrack

set_option exponentiation.threshold 2048

/-- `R' S - R S'`. -/
def dP (R S : List ℚ) : List ℚ := subP (mulP (derivP R) S) (mulP R (derivP S))

theorem eval_dP (R S : List ℚ) (t : ℝ) :
    eval (dP R S) t = eval (derivP R) t * eval S t - eval R t * eval (derivP S) t := by
  rw [dP, eval_subP, eval_mulP, eval_mulP]

/-- The bound on the distance of the rounded quotient from `R(z)/S(z)`. -/
def ratioErr (R S : List ℚ) (lo hi δ : ℚ) : ℚ :=
  hornerErr R lo hi / (lowBound S lo hi - hornerErr S lo hi) +
    magBound R lo hi * hornerErr S lo hi /
      ((lowBound S lo hi - hornerErr S lo hi) * lowBound S lo hi) +
    uQ * ((magBound R lo hi + hornerErr R lo hi) / (lowBound S lo hi - hornerErr S lo hi)) + etaQ +
    magBound (dP R S) (lo - δ) (hi + δ) / lowBound S (lo - δ) (hi + δ) ^ 2 * δ

/-- The check on one piece. -/
def pieceOk (R S : List ℚ) (lo hi δ E : ℚ) : Bool :=
  hornerOK R lo hi && hornerOK S lo hi && decide (0 < lowBound S (lo - δ) (hi + δ)) &&
    decide (hornerErr S lo hi < lowBound S lo hi) &&
    decide ((magBound R lo hi + hornerErr R lo hi) / (lowBound S lo hi - hornerErr S lo hi) <
      2 ^ 1000) &&
    decide (ratioErr R S lo hi δ ≤ E)

theorem piece_sound (R S : List ℚ) (lo hi δ E : ℚ) (h : pieceOk R S lo hi δ E = true)
    (wr ws : List UInt64)
    (hwr : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ)) wr R)
    (hws : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ)) ws S)
    (hR : R ≠ []) (hS : S ≠ []) (zw : UInt64) (hzf : Finite zw)
    (hlo : (lo : ℝ) ≤ value zw) (hhi : value zw ≤ hi) (z : ℝ) (hz : |value zw - z| ≤ δ) :
    Approx (Wasm.IEEE64.div (hornerW wr zw) (hornerW ws zw)) (eval R z / eval S z) E := by
  simp only [pieceOk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hokR, hokS⟩, hpos'⟩, hpos⟩, hmax⟩, hE⟩ := h
  have hδ : (0 : ℝ) ≤ δ := (abs_nonneg _).trans hz
  have aR := hornerW_approx R wr hwr hR lo hi zw hzf hlo hhi hokR
  have aS := hornerW_approx S ws hws hS lo hi zw hzf hlo hhi hokS
  have hMA := magBound_sound R lo hi (value zw) hlo hhi
  have hmB := lowBound_sound S lo hi (value zw) hlo hhi
  have hpos_r : ((hornerErr S lo hi : ℚ) : ℝ) < lowBound S lo hi := by exact_mod_cast hpos
  have hmax_r : (((magBound R lo hi : ℚ) : ℝ) + hornerErr R lo hi) /
      (((lowBound S lo hi : ℚ) : ℝ) - hornerErr S lo hi) < 2 ^ 1022 := by
    have : ((((magBound R lo hi + hornerErr R lo hi) / (lowBound S lo hi - hornerErr S lo hi) :
        ℚ)) : ℝ) < 2 ^ 1000 := by exact_mod_cast hmax
    push_cast at this
    linarith [show (2 : ℝ) ^ 1000 ≤ 2 ^ 1022 by norm_num]
  have hd := F64DivApprox.div_approx aR aS _ _ hMA hmB hpos_r hmax_r
  -- the change from `ẑ` to `z`
  set lo' : ℚ := lo - δ
  set hi' : ℚ := hi + δ
  have hmB'pos : (0 : ℝ) < lowBound S lo' hi' := by exact_mod_cast hpos'
  have hzlo : (lo' : ℝ) ≤ value zw := by simp only [lo']; push_cast; linarith
  have hzhi : value zw ≤ (hi' : ℝ) := by simp only [hi']; push_cast; linarith
  have hz' := abs_le.mp hz
  have hzlo' : (lo' : ℝ) ≤ z := by simp only [lo']; push_cast; linarith
  have hzhi' : z ≤ (hi' : ℝ) := by simp only [hi']; push_cast; linarith
  set L : ℝ := ((magBound (dP R S) lo' hi' : ℚ) : ℝ) / ((lowBound S lo' hi' : ℚ) : ℝ) ^ 2
  have hQ : ∀ t ∈ Set.Icc (lo' : ℝ) hi', 0 < eval S t := fun t ht =>
    lt_of_lt_of_le hmB'pos (lowBound_sound S lo' hi' t ht.1 ht.2)
  have hdd : ∀ t ∈ Set.Icc (lo' : ℝ) hi',
      |eval (derivP R) t * eval S t - eval R t * eval (derivP S) t| ≤ L * eval S t ^ 2 := by
    intro t ht
    rw [← eval_dP]
    have h1 := magBound_sound (dP R S) lo' hi' t ht.1 ht.2
    have h2 := lowBound_sound S lo' hi' t ht.1 ht.2
    have h3 : ((lowBound S lo' hi' : ℚ) : ℝ) ^ 2 ≤ eval S t ^ 2 :=
      pow_le_pow_left₀ hmB'pos.le h2 2
    have hM0 : (0 : ℝ) ≤ ((magBound (dP R S) lo' hi' : ℚ) : ℝ) := (abs_nonneg _).trans h1
    have hL : L * ((lowBound S lo' hi' : ℚ) : ℝ) ^ 2 =
        ((magBound (dP R S) lo' hi' : ℚ) : ℝ) := by
      simp only [L]
      field_simp
    have hL0 : 0 ≤ L := div_nonneg hM0 (by positivity)
    calc _ ≤ ((magBound (dP R S) lo' hi' : ℚ) : ℝ) := h1
      _ = L * ((lowBound S lo' hi' : ℚ) : ℝ) ^ 2 := hL.symm
      _ ≤ L * eval S t ^ 2 := mul_le_mul_of_nonneg_left h3 hL0
  have hlip := F64DivApprox.ratio_lipschitz R S lo' hi' L hQ hdd ⟨hzlo, hzhi⟩ ⟨hzlo', hzhi'⟩
  refine ⟨hd.1, ?_⟩
  have hE' : ((ratioErr R S lo hi δ : ℚ) : ℝ) ≤ E := by exact_mod_cast hE
  have hEeq : ((ratioErr R S lo hi δ : ℚ) : ℝ) =
      ((hornerErr R lo hi : ℚ) : ℝ) / ((lowBound S lo hi : ℚ) - (hornerErr S lo hi : ℚ) : ℝ) +
        ((magBound R lo hi : ℚ) : ℝ) * ((hornerErr S lo hi : ℚ) : ℝ) /
          (((lowBound S lo hi : ℚ) - (hornerErr S lo hi : ℚ) : ℝ) * ((lowBound S lo hi : ℚ) : ℝ)) +
        unitRoundoff64 * ((((magBound R lo hi : ℚ) : ℝ) + ((hornerErr R lo hi : ℚ) : ℝ)) /
          ((lowBound S lo hi : ℚ) - (hornerErr S lo hi : ℚ) : ℝ)) +
        multiplicationUnderflowEpsilon + L * δ := by
    simp only [ratioErr, L]
    push_cast [uQ_eq, etaQ_eq]
    ring
  have hLd : L * |value zw - z| ≤ L * δ := by
    have hL0 : 0 ≤ L := by
      have h1 := magBound_sound (dP R S) lo' hi' z hzlo' hzhi'
      exact div_nonneg ((abs_nonneg _).trans h1) (by positivity)
    exact mul_le_mul_of_nonneg_left hz hL0
  have htri := abs_sub_le (value (Wasm.IEEE64.div (hornerW wr zw) (hornerW ws zw)))
    (eval R (value zw) / eval S (value zw)) (eval R z / eval S z)
  have hd2 := hd.2
  linarith

/-- The checks on consecutive pieces `[a, b₁], [b₁, b₂], ...`. -/
def piecesOk (R S : List ℚ) (δ E : ℚ) (a : ℚ) : List ℚ → Bool
  | [] => true
  | b :: rest => pieceOk R S a b δ E && piecesOk R S δ E b rest

/-- The last breakpoint. -/
def lastD (a : ℚ) : List ℚ → ℚ
  | [] => a
  | b :: rest => lastD b rest

theorem pieces_sound (R S : List ℚ) (δ E : ℚ)
    (wr ws : List UInt64)
    (hwr : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ)) wr R)
    (hws : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ)) ws S)
    (hR : R ≠ []) (hS : S ≠ []) (zw : UInt64) (hzf : Finite zw) (z : ℝ)
    (hz : |value zw - z| ≤ δ) :
    ∀ (a : ℚ) (bs : List ℚ), piecesOk R S δ E a bs = true → (a : ℝ) ≤ value zw →
      value zw ≤ lastD a bs →
      Approx (Wasm.IEEE64.div (hornerW wr zw) (hornerW ws zw)) (eval R z / eval S z) E ∨
        value zw = a := by
  intro a bs
  induction bs generalizing a with
  | nil =>
    intro _ hlo hhi
    right
    simp only [lastD] at hhi
    linarith
  | cons b rest ih =>
    intro h hlo hhi
    simp only [piecesOk, Bool.and_eq_true] at h
    by_cases hb : value zw ≤ b
    · exact Or.inl (piece_sound R S a b δ E h.1 wr ws hwr hws hR hS zw hzf hlo hb z hz)
    · push Not at hb
      rcases ih b h.2 hb.le hhi with h1 | h1
      · exact Or.inl h1
      · exact absurd h1 (ne_of_gt hb)

/-- The cover of `[a, lastD a bs]` when the first piece also starts at `a`. -/
theorem pieces_cover (R S : List ℚ) (δ E : ℚ)
    (wr ws : List UInt64)
    (hwr : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ)) wr R)
    (hws : List.Forall₂ (fun (w : UInt64) (c : ℚ) => Finite w ∧ value w = (c : ℝ)) ws S)
    (hR : R ≠ []) (hS : S ≠ []) (zw : UInt64) (hzf : Finite zw) (z : ℝ)
    (hz : |value zw - z| ≤ δ) (a b : ℚ) (rest : List ℚ)
    (h : piecesOk R S δ E a (b :: rest) = true) (hlo : (a : ℝ) ≤ value zw)
    (hhi : value zw ≤ lastD a (b :: rest)) :
    Approx (Wasm.IEEE64.div (hornerW wr zw) (hornerW ws zw)) (eval R z / eval S z) E := by
  by_cases hb : value zw ≤ b
  · simp only [piecesOk, Bool.and_eq_true] at h
    exact piece_sound R S a b δ E h.1 wr ws hwr hws hR hS zw hzf hlo hb z hz
  · push Not at hb
    simp only [piecesOk, Bool.and_eq_true] at h
    rcases pieces_sound R S δ E wr ws hwr hws hR hS zw hzf z hz b rest h.2 hb.le hhi with h1 | h1
    · exact h1
    · exact absurd h1 (ne_of_gt hb)

#print axioms eval_dP
#print axioms piece_sound
#print axioms pieces_sound
#print axioms pieces_cover

end Library.Numerics.Float64.Bessel.BesselRatioEval
