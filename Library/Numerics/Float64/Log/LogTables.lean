import Library.Numerics.Float64.Log.Compiled
import LeanExe.ProofKit.TaylorRemainder

/-!
Facts about each of the 128 entries of Arm's tables in `Log.lean`, checked by the kernel over the
rationals.  Entry `i` describes the center `c = chi + clo` of subinterval `i` of
`[0x1.6p-1, 0x1.6p0)`: `c invc` is within `2 ^ -100` of 1, the reduced argument
`(z - c) invc` stays within `39/10000` in magnitude for `z` in the subinterval, `chi` lies on the
grid of `2 ^ -53` between `1/2` and `3/2`, `|clo| ≤ 2 ^ -50`, `logc` lies on the grid of `2 ^ -43`,
and `logc` is
within `2 ^ -64` of `log c`.  The last fact comes from bracketing `c` between exponentials of
`logc ∓ 2 ^ -64`, each a Taylor polynomial of degree 19 plus its remainder bound.
-/

namespace Library.Numerics.Float64.Log.LogTables
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound TaylorRemainder

/-- Horner evaluation over the rationals. -/
def evalQ : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: p, x => a + x * evalQ p x

theorem evalQ_cast (p : List ℚ) (x : ℚ) : ((evalQ p x : ℚ) : ℝ) = eval p (x : ℝ) := by
  induction p with
  | nil => simp [evalQ]
  | cons a p ih => simp [evalQ, ih]

def invcQ (i : Nat) : ℚ := ratOfWord Log.logTable[2 * i]!
def logcQ (i : Nat) : ℚ := ratOfWord Log.logTable[2 * i + 1]!
def chiQ (i : Nat) : ℚ := ratOfWord Log.logTable2[2 * i]!
def cloQ (i : Nat) : ℚ := ratOfWord Log.logTable2[2 * i + 1]!
def centerQ (i : Nat) : ℚ := chiQ i + cloQ i

/-- The lower end of subinterval `i`. -/
def lowQ (i : Nat) : ℚ := if i < 80 then ((176 + i : Nat) : ℚ) / 256 else ((48 + i : Nat) : ℚ) / 128

/-- The upper end of subinterval `i`. -/
def highQ (i : Nat) : ℚ := if i < 80 then ((177 + i : Nat) : ℚ) / 256 else ((49 + i : Nat) : ℚ) / 128

def tolerance : ℚ := 1 / 2 ^ 64

/-- The Taylor remainder bound of degree 20 for arguments of magnitude at most `2/5`. -/
def expRemainder : ℚ := (2 / 5) ^ 20 * ((20 + 1) / ((Nat.factorial 20 : ℚ) * 20))

theorem checked_entries : ∀ i : Fin 128,
    Finite Log.logTable[2 * i.val]! ∧ Finite Log.logTable[2 * i.val + 1]! ∧
    Finite Log.logTable2[2 * i.val]! ∧ Finite Log.logTable2[2 * i.val + 1]! ∧
    0 < invcQ i.val ∧ invcQ i.val ≤ 3 / 2 ∧
    qabs (centerQ i.val * invcQ i.val - 1) ≤ 1 / 2 ^ 100 ∧
    -(39 / 10000) ≤ (lowQ i.val - centerQ i.val) * invcQ i.val ∧
    (highQ i.val - centerQ i.val) * invcQ i.val ≤ 39 / 10000 ∧
    1 / 2 ≤ chiQ i.val ∧ chiQ i.val ≤ 3 / 2 ∧
    Wasm.IEEE64.scaledValue Log.logTable2[2 * i.val]! % 2 ^ 1021 = 0 ∧
    Wasm.IEEE64.scaledValue Log.logTable[2 * i.val + 1]! % 2 ^ 1031 = 0 ∧
    qabs (cloQ i.val) ≤ 1 / 2 ^ 50 ∧
    qabs (logcQ i.val) ≤ 3 / 8 := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

theorem checked_logs : ∀ i : Fin 128,
    evalQ (expCoeffs 20) (logcQ i.val - tolerance) + expRemainder ≤ centerQ i.val ∧
    centerQ i.val ≤ evalQ (expCoeffs 20) (logcQ i.val + tolerance) - expRemainder := by
  decide +kernel

theorem exp_near (x : ℝ) (hx : |x| ≤ 2 / 5) :
    |Real.exp x - eval (expCoeffs 20) x| ≤ (expRemainder : ℝ) := by
  have h := exp_remainder x (hx.trans (by norm_num)) 20 (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hrem : (expRemainder : ℝ) = (2 / 5) ^ 20 * ((20 + 1) / ((Nat.factorial 20 : ℝ) * 20)) := by
    rw [expRemainder]
    push_cast
    ring
  rw [hrem]
  calc _ ≤ |x| ^ 20 * ((20 + 1) / ((Nat.factorial 20 : ℝ) * 20)) := h
    _ ≤ (2 / 5) ^ 20 * ((20 + 1) / ((Nat.factorial 20 : ℝ) * 20)) := by gcongr

/-- `logc` is within `2 ^ -64` of `log c`. -/
theorem log_center (i : Fin 128) :
    0 < (centerQ i.val : ℝ) ∧
      |Real.log (centerQ i.val : ℝ) - (logcQ i.val : ℝ)| ≤ 1 / 2 ^ 64 := by
  obtain ⟨hlo, hhi⟩ := checked_logs i
  have hl := (checked_entries i).2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hl' : |(logcQ i.val : ℝ)| ≤ 3 / 8 := by
    have h : ((qabs (logcQ i.val) : ℚ) : ℝ) ≤ ((3 / 8 : ℚ) : ℝ) := Rat.cast_le.mpr hl
    rw [qabs_cast] at h
    exact h.trans (by norm_num)
  have htol : ((tolerance : ℚ) : ℝ) = 1 / 2 ^ 64 := by norm_num [tolerance]
  have hx1 : |(logcQ i.val : ℝ) - 1 / 2 ^ 64| ≤ 2 / 5 := by
    rw [abs_le] at hl' ⊢
    constructor <;> linarith [hl'.1, hl'.2, (by norm_num : (0 : ℝ) < 1 / 2 ^ 64),
      (by norm_num : (1 : ℝ) / 2 ^ 64 < 1 / 40)]
  have hx2 : |(logcQ i.val : ℝ) + 1 / 2 ^ 64| ≤ 2 / 5 := by
    rw [abs_le] at hl' ⊢
    constructor <;> linarith [hl'.1, hl'.2, (by norm_num : (0 : ℝ) < 1 / 2 ^ 64),
      (by norm_num : (1 : ℝ) / 2 ^ 64 < 1 / 40)]
  have hdown := abs_le.mp (exp_near _ hx1)
  have hup := abs_le.mp (exp_near _ hx2)
  have hlo' : ((evalQ (expCoeffs 20) (logcQ i.val - tolerance) + expRemainder : ℚ) : ℝ) ≤
      (centerQ i.val : ℝ) := Rat.cast_le.mpr hlo
  have hhi' : (centerQ i.val : ℝ) ≤
      ((evalQ (expCoeffs 20) (logcQ i.val + tolerance) - expRemainder : ℚ) : ℝ) :=
    Rat.cast_le.mpr hhi
  rw [Rat.cast_add, evalQ_cast, Rat.cast_sub, htol] at hlo'
  rw [Rat.cast_sub, evalQ_cast, Rat.cast_add, htol] at hhi'
  have hc0 : 0 < (centerQ i.val : ℝ) := by
    have := Real.exp_pos ((logcQ i.val : ℝ) - 1 / 2 ^ 64)
    linarith [hdown.2]
  refine ⟨hc0, abs_le.mpr ⟨?_, ?_⟩⟩
  · have h : Real.exp ((logcQ i.val : ℝ) - 1 / 2 ^ 64) ≤ (centerQ i.val : ℝ) := by
      linarith [hdown.2]
    have := (Real.le_log_iff_exp_le hc0).mpr h
    linarith
  · have h : (centerQ i.val : ℝ) ≤ Real.exp ((logcQ i.val : ℝ) + 1 / 2 ^ 64) := by
      linarith [hup.1]
    have := (Real.log_le_iff_le_exp hc0).mpr h
    linarith

#print axioms evalQ_cast
#print axioms checked_entries
#print axioms checked_logs
#print axioms exp_near
#print axioms log_center

end Library.Numerics.Float64.Log.LogTables
