import Verified.Examples.TgammaDD

/-!
Error bounds for straight-line double arithmetic in one variable.  `FE` is an expression over a
variable, constant words, and `+`, `-`, `*`; `evalF` evaluates it in `Float` and `evalR` over `ℝ`
with the exact values of the words.  `bnd e X` computes, in `ℚ`, a bound `M` on `|evalR e x|` and an
error bound `E` for `|x| ≤ X`, charging each operation the rounding `F64Approx` gives it, and
`ok e X` checks that the constants are finite and the magnitudes stay below `2 ^ 1000`.  When `ok`
holds, the computed `Float` lies within `E` of the exact value (`evalF_approx`).  The kernel computes
`bnd` and `ok` for a concrete expression, so a chain of `Tgamma`'s code gets its bound by
`decide +kernel` and `norm_num`.
-/

namespace Verified.Examples.TgammaExpr
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx TgammaDD

set_option exponentiation.threshold 4096

inductive FE where
  | var : FE
  | const : UInt64 → FE
  | add : FE → FE → FE
  | sub : FE → FE → FE
  | mul : FE → FE → FE

def evalF : FE → Float → Float
  | .var, x => x
  | .const w, _ => Float.ofBits w
  | .add a b, x => evalF a x + evalF b x
  | .sub a b, x => evalF a x - evalF b x
  | .mul a b, x => evalF a x * evalF b x

noncomputable def evalR : FE → ℝ → ℝ
  | .var, x => x
  | .const w, _ => (PolyBound.ratOfWord w : ℝ)
  | .add a b, x => evalR a x + evalR b x
  | .sub a b, x => evalR a x - evalR b x
  | .mul a b, x => evalR a x * evalR b x

/-- The bound `(M, E)` on the magnitude and the error of an expression for `|x| ≤ X`. -/
def bnd : FE → ℚ → ℚ × ℚ
  | .var, X => (X, 0)
  | .const w, _ => (PolyBound.qabs (PolyBound.ratOfWord w), 0)
  | .add a b, X =>
    let (Ma, Ea) := bnd a X
    let (Mb, Eb) := bnd b X
    (Ma + Mb, Ea + Eb + (Ma + Mb + (Ea + Eb)) / 2 ^ 53)
  | .sub a b, X =>
    let (Ma, Ea) := bnd a X
    let (Mb, Eb) := bnd b X
    (Ma + Mb, Ea + Eb + (Ma + Mb + (Ea + Eb)) / 2 ^ 53)
  | .mul a b, X =>
    let (Ma, Ea) := bnd a X
    let (Mb, Eb) := bnd b X
    (Ma * Mb, Ea * Mb + Ma * Eb + Ea * Eb + (Ma + Ea) * (Mb + Eb) / 2 ^ 53 + 1 / 2 ^ 1075)

/-- The constants are finite and every magnitude with its error stays below `2 ^ 1000`. -/
def ok : FE → ℚ → Bool
  | .var, X => decide (X < 2 ^ 1000)
  | .const w, _ => Wasm.IEEE64.isFinite w && decide (PolyBound.qabs (PolyBound.ratOfWord w) < 2 ^ 1000)
  | .add a b, X => ok a X && ok b X &&
      decide ((bnd a X).1 + (bnd b X).1 + ((bnd a X).2 + (bnd b X).2) < 2 ^ 1000)
  | .sub a b, X => ok a X && ok b X &&
      decide ((bnd a X).1 + (bnd b X).1 + ((bnd a X).2 + (bnd b X).2) < 2 ^ 1000)
  | .mul a b, X => ok a X && ok b X &&
      decide (((bnd a X).1 + (bnd a X).2) * ((bnd b X).1 + (bnd b X).2) < 2 ^ 1000)

theorem bnd_nonneg (e : FE) (X : ℚ) (hX : 0 ≤ X) : 0 ≤ (bnd e X).1 ∧ 0 ≤ (bnd e X).2 := by
  induction e with
  | var => exact ⟨hX, le_rfl⟩
  | const w =>
    refine ⟨?_, le_rfl⟩
    simp only [bnd, PolyBound.qabs]
    split <;> linarith
  | add a b iha ihb =>
    simp only [bnd]
    constructor <;> nlinarith [iha.1, iha.2, ihb.1, ihb.2]
  | sub a b iha ihb =>
    simp only [bnd]
    constructor <;> nlinarith [iha.1, iha.2, ihb.1, ihb.2]
  | mul a b iha ihb =>
    simp only [bnd]
    constructor
    · exact mul_nonneg iha.1 ihb.1
    · have h1 := mul_nonneg iha.2 ihb.1
      have h2 := mul_nonneg iha.1 ihb.2
      have h3 := mul_nonneg iha.2 ihb.2
      have h4 := mul_nonneg (add_nonneg iha.1 iha.2) (add_nonneg ihb.1 ihb.2)
      positivity

theorem qabs_cast (q : ℚ) : ((PolyBound.qabs q : ℚ) : ℝ) = |(q : ℝ)| := by
  simp only [PolyBound.qabs]
  split
  · rename_i h
    rw [abs_of_neg (by exact_mod_cast h)]
    push_cast
    ring
  · rename_i h
    rw [abs_of_nonneg (by exact_mod_cast (not_lt.mp h))]

/-- **The bound is sound.** -/
theorem evalF_approx (e : FE) (X : ℚ) (x : Float) (hx : Finite x.toBits)
    (hX : |value x.toBits| ≤ X) (hok : ok e X = true) :
    FApprox (evalF e x) (evalR e (value x.toBits)) (bnd e X).2 ∧
      |evalR e (value x.toBits)| ≤ (bnd e X).1 := by
  have hX0 : (0 : ℚ) ≤ X := by
    have : (0 : ℝ) ≤ X := (abs_nonneg _).trans hX
    exact_mod_cast this
  induction e with
  | var =>
    refine ⟨?_, by simpa [evalR, bnd] using hX⟩
    simp only [evalF, evalR, bnd, Rat.cast_zero]
    exact fapprox_self x hx
  | const w =>
    simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    have hw : Finite w := hok.1
    refine ⟨?_, ?_⟩
    · simp only [evalF, evalR, bnd]
      have := fapprox_ofBits w hw
      rw [← PolyBound.ratOfWord_cast] at this
      simpa using this
    · simp only [evalR, bnd, qabs_cast]
      exact le_rfl
  | add a b iha ihb =>
    simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hoka, hokb⟩, hsz⟩ := hok
    obtain ⟨ha, hMa⟩ := iha hoka
    obtain ⟨hb, hMb⟩ := ihb hokb
    have hsz' : (((bnd a X).1 + (bnd b X).1 + ((bnd a X).2 + (bnd b X).2) : ℚ) : ℝ) < 2 ^ 1000 := by
      exact_mod_cast hsz
    push_cast at hsz'
    have h := fapprox_add ha hb ((bnd a X).1 + (bnd b X).1 + ((bnd a X).2 + (bnd b X).2))
      (by linarith [abs_add_le (evalR a (value x.toBits)) (evalR b (value x.toBits))])
      (by linarith [(by norm_num : (2 : ℝ) ^ 1000 < 2 ^ 1023)])
    simp only [evalF, evalR, bnd]
    refine ⟨?_, ?_⟩
    · push_cast at h ⊢
      exact h
    · push_cast
      linarith [abs_add_le (evalR a (value x.toBits)) (evalR b (value x.toBits))]
  | sub a b iha ihb =>
    simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hoka, hokb⟩, hsz⟩ := hok
    obtain ⟨ha, hMa⟩ := iha hoka
    obtain ⟨hb, hMb⟩ := ihb hokb
    have hsz' : (((bnd a X).1 + (bnd b X).1 + ((bnd a X).2 + (bnd b X).2) : ℚ) : ℝ) < 2 ^ 1000 := by
      exact_mod_cast hsz
    push_cast at hsz'
    have h := fapprox_sub ha hb ((bnd a X).1 + (bnd b X).1 + ((bnd a X).2 + (bnd b X).2))
      (by linarith [abs_sub (evalR a (value x.toBits)) (evalR b (value x.toBits))])
      (by linarith [(by norm_num : (2 : ℝ) ^ 1000 < 2 ^ 1023)])
    simp only [evalF, evalR, bnd]
    refine ⟨?_, ?_⟩
    · push_cast at h ⊢
      exact h
    · push_cast
      linarith [abs_sub (evalR a (value x.toBits)) (evalR b (value x.toBits))]
  | mul a b iha ihb =>
    simp only [ok, Bool.and_eq_true, decide_eq_true_eq] at hok
    obtain ⟨⟨hoka, hokb⟩, hsz⟩ := hok
    obtain ⟨ha, hMa⟩ := iha hoka
    obtain ⟨hb, hMb⟩ := ihb hokb
    have hsz' : ((((bnd a X).1 + (bnd a X).2) * ((bnd b X).1 + (bnd b X).2) : ℚ) : ℝ) <
        2 ^ 1000 := by
      exact_mod_cast hsz
    push_cast at hsz'
    have h := fapprox_mul ha hb ((bnd a X).1 : ℝ) ((bnd b X).1 : ℝ) hMa hMb
      ((((bnd a X).1 + (bnd a X).2) * ((bnd b X).1 + (bnd b X).2) : ℚ) : ℝ)
      (by push_cast; exact le_rfl)
      (by push_cast; linarith [(by norm_num : (2 : ℝ) ^ 1000 < 2 ^ 1022)])
    simp only [evalF, evalR, bnd]
    refine ⟨?_, ?_⟩
    · push_cast at h ⊢
      exact h
    · rw [abs_mul]
      push_cast
      exact mul_le_mul hMa hMb (abs_nonneg _) ((abs_nonneg _).trans hMa)

#print axioms evalF_approx

end Verified.Examples.TgammaExpr
