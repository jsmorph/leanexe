import Verified.Examples.Pow
import Verified.Examples.LogTables
import Verified.Examples.ExpReductionBounds

/-!
Facts about the 128 entries of `Pow.powLogTable`, checked by the kernel over the rationals, and
the polynomial of `Pow.powLog`.  Subinterval `i` holds the `z` of exponent field 1022 whose
fraction field lies in `[0x6955500000000 + i 2 ^ 45, 0x6955500000000 + (i + 1) 2 ^ 45)`, for
`i ≤ 75`, and the `z` of exponent field 1023 with `2 ^ 52 + f` in that range, for `i ≥ 75`.
For `z` in the subinterval, `r = z invc - 1` stays within `23/4000`; `invc` lies on the grid of
`2 ^ -7` for `i ≤ 75` and of `2 ^ -8` for `i ≥ 75`, so that `r` lies on the grid of `2 ^ -60`;
`logc` lies on the grid of `2 ^ -43`; and `logc + logctail` is within `2 ^ -97` of
`-log invc`, by bracketing `1/invc` between exponentials of `logc + logctail ∓ 2 ^ -97`.  For
`logc ≠ 0`, `logc + r` keeps the sign of `logc` and exceeds `|r|` by `1/10000` and `1/450` in
magnitude; the entries with `logc = 0` are 74 and 75, with `invc = 1`.  The polynomial
`r - r ^ 2 / 2 + p` of `powLog` is within `6 · 2 ^ -70 |r|` of `log (1 + r)` for
`|r| ≤ 23/4000`.
-/

namespace Verified.Examples.PowLogTable
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound TaylorRemainder LogTables

def invcQ (i : Nat) : ℚ := ratOfWord Pow.powLogTable[4 * i]!
def logcQ (i : Nat) : ℚ := ratOfWord Pow.powLogTable[4 * i + 2]!
def tailQ (i : Nat) : ℚ := ratOfWord Pow.powLogTable[4 * i + 3]!

/-- The least `z` of exponent field 1022 in subinterval `i`. -/
def lowU (i : Nat) : ℚ := ((2 ^ 52 + 1853042165022720 + i * 2 ^ 45 : Nat) : ℚ) / 2 ^ 53
/-- The greatest `z` of exponent field 1022 in subinterval `i`. -/
def highU (i : Nat) : ℚ :=
  ((min (2 ^ 52 + 1853042165022720 + (i + 1) * 2 ^ 45 - 1) (2 ^ 53 - 1) : Nat) : ℚ) / 2 ^ 53
/-- The least `z` of exponent field 1023 in subinterval `i`. -/
def lowL (i : Nat) : ℚ := ((max (2 ^ 52) (1853042165022720 + i * 2 ^ 45) : Nat) : ℚ) / 2 ^ 52
/-- The greatest `z` of exponent field 1023 in subinterval `i`. -/
def highL (i : Nat) : ℚ := ((1853042165022720 + (i + 1) * 2 ^ 45 - 1 : Nat) : ℚ) / 2 ^ 52

def rminQ (i : Nat) : ℚ := if i ≤ 75 then lowU i * invcQ i - 1 else lowL i * invcQ i - 1
def rmaxQ (i : Nat) : ℚ := if i ≤ 75 then highU i * invcQ i - 1 else highL i * invcQ i - 1

def tolerance : ℚ := 1 / 2 ^ 97

/-- The Taylor remainder bound of degree 24 for arguments of magnitude at most `35/100`. -/
def expRemainder : ℚ := (35 / 100) ^ 24 * ((24 + 1) / ((Nat.factorial 24 : ℚ) * 24))

theorem checked_entries : ∀ i : Fin 128,
    Finite Pow.powLogTable[4 * i.val]! ∧ Finite Pow.powLogTable[4 * i.val + 2]! ∧
    Finite Pow.powLogTable[4 * i.val + 3]! ∧
    1 / 2 ≤ invcQ i.val ∧ invcQ i.val ≤ 3 / 2 ∧
    (i.val ≤ 75 → Wasm.IEEE64.scaledValue Pow.powLogTable[4 * i.val]! % 2 ^ 1067 = 0) ∧
    (75 ≤ i.val → Wasm.IEEE64.scaledValue Pow.powLogTable[4 * i.val]! % 2 ^ 1066 = 0) ∧
    Wasm.IEEE64.scaledValue Pow.powLogTable[4 * i.val + 2]! % 2 ^ 1031 = 0 ∧
    qabs (logcQ i.val) ≤ 3466 / 10000 ∧ qabs (tailQ i.val) ≤ 1 / 2 ^ 43 ∧
    (i.val ≤ 75 → -(23 / 4000) ≤ lowU i.val * invcQ i.val - 1 ∧
      highU i.val * invcQ i.val - 1 ≤ 23 / 4000) ∧
    (75 ≤ i.val → -(23 / 4000) ≤ lowL i.val * invcQ i.val - 1 ∧
      highL i.val * invcQ i.val - 1 ≤ 23 / 4000) ∧
    (0 < logcQ i.val → 1 / 10000 ≤ logcQ i.val + 2 * rminQ i.val ∧
      1 / 450 ≤ logcQ i.val + rminQ i.val) ∧
    (logcQ i.val < 0 → logcQ i.val + 2 * rmaxQ i.val ≤ -(1 / 10000) ∧
      logcQ i.val + rmaxQ i.val ≤ -(1 / 450)) ∧
    (logcQ i.val = 0 → Pow.powLogTable[4 * i.val]! = 0x3FF0000000000000 ∧
      Pow.powLogTable[4 * i.val + 2]! = 0 ∧ Pow.powLogTable[4 * i.val + 3]! = 0) := by
  unfold CodeLib.IEEE64.Finite
  decide +kernel

theorem checked_logs : ∀ i : Fin 128,
    invcQ i.val * (evalQ (expCoeffs 24) (logcQ i.val + tailQ i.val - tolerance) + expRemainder)
      ≤ 1 ∧
    1 ≤ invcQ i.val *
      (evalQ (expCoeffs 24) (logcQ i.val + tailQ i.val + tolerance) - expRemainder) := by
  decide +kernel

theorem exp_near (x : ℝ) (hx : |x| ≤ 35 / 100) :
    |Real.exp x - eval (expCoeffs 24) x| ≤ (expRemainder : ℝ) := by
  have h := exp_remainder x (hx.trans (by norm_num)) 24 (by norm_num)
  simp only [Nat.cast_ofNat] at h
  have hrem : (expRemainder : ℝ) =
      (35 / 100) ^ 24 * ((24 + 1) / ((Nat.factorial 24 : ℝ) * 24)) := by
    rw [expRemainder]
    push_cast
    ring
  rw [hrem]
  calc _ ≤ |x| ^ 24 * ((24 + 1) / ((Nat.factorial 24 : ℝ) * 24)) := h
    _ ≤ (35 / 100) ^ 24 * ((24 + 1) / ((Nat.factorial 24 : ℝ) * 24)) := by gcongr

theorem rat_le {q b : ℚ} (h : q ≤ b) : (q : ℝ) ≤ (b : ℝ) := Rat.cast_le.mpr h

/-- `logc + logctail` is within `2 ^ -97` of `-log invc`. -/
theorem log_table (i : Fin 128) :
    0 < (invcQ i.val : ℝ) ∧
      |Real.log (invcQ i.val : ℝ) + ((logcQ i.val : ℝ) + (tailQ i.val : ℝ))| ≤ 1 / 2 ^ 97 := by
  obtain ⟨hlo, hhi⟩ := checked_logs i
  have he := checked_entries i
  have hi0 : (1 / 2 : ℝ) ≤ (invcQ i.val : ℝ) := by
    have := rat_le he.2.2.2.1
    push_cast at this
    exact this
  have hc0 : 0 < (invcQ i.val : ℝ) := by linarith
  have hl : |(logcQ i.val : ℝ)| ≤ 3466 / 10000 := by
    have h := rat_le he.2.2.2.2.2.2.2.2.1
    rw [qabs_cast] at h
    exact h.trans (by norm_num)
  have ht : |(tailQ i.val : ℝ)| ≤ 1 / 2 ^ 43 := by
    have h := rat_le he.2.2.2.2.2.2.2.2.2.1
    rw [qabs_cast] at h
    exact h.trans (by norm_num)
  set L := (logcQ i.val : ℝ) + (tailQ i.val : ℝ)
  have htol : ((tolerance : ℚ) : ℝ) = 1 / 2 ^ 97 := by norm_num [tolerance]
  have h1 := abs_le.mp hl
  have h2 := abs_le.mp ht
  have hn1 : (3466 / 10000 : ℝ) + 1 / 2 ^ 43 + 1 / 2 ^ 97 ≤ 35 / 100 := by norm_num
  have hx1 : |L - 1 / 2 ^ 97| ≤ 35 / 100 := by
    rw [abs_le]
    constructor <;> linarith
  have hx2 : |L + 1 / 2 ^ 97| ≤ 35 / 100 := by
    rw [abs_le]
    constructor <;> linarith
  have hdown := abs_le.mp (exp_near _ hx1)
  have hup := abs_le.mp (exp_near _ hx2)
  have hlo' := rat_le hlo
  have hhi' := rat_le hhi
  push_cast at hlo' hhi'
  rw [evalQ_cast] at hlo' hhi'
  push_cast at hlo' hhi'
  rw [htol] at hlo' hhi'
  have hA : (invcQ i.val : ℝ) * Real.exp (L - 1 / 2 ^ 97) ≤ 1 := by
    calc
      _ ≤ (invcQ i.val : ℝ) * (eval (expCoeffs 24) (L - 1 / 2 ^ 97) + (expRemainder : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith [hdown.2]) hc0.le
      _ ≤ 1 := hlo'
  have hB : 1 ≤ (invcQ i.val : ℝ) * Real.exp (L + 1 / 2 ^ 97) := by
    calc
      (1 : ℝ) ≤ (invcQ i.val : ℝ) *
          (eval (expCoeffs 24) (L + 1 / 2 ^ 97) - (expRemainder : ℝ)) := hhi'
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hup.1]) hc0.le
  have hA' : Real.exp (Real.log (invcQ i.val : ℝ) + (L - 1 / 2 ^ 97)) ≤ 1 := by
    rw [Real.exp_add, Real.exp_log hc0]
    exact hA
  have hB' : 1 ≤ Real.exp (Real.log (invcQ i.val : ℝ) + (L + 1 / 2 ^ 97)) := by
    rw [Real.exp_add, Real.exp_log hc0]
    exact hB
  have hA'' := Real.exp_le_one_iff.mp hA'
  have hB'' := Real.one_le_exp_iff.mp hB'
  refine ⟨hc0, ?_⟩
  rw [abs_le]
  constructor <;> linarith

/-- `1 - r/2 - A1 r ^ 2 / 2 - A2 r ^ 3 / 2 + A3 r ^ 4 / 4 + A4 r ^ 5 / 4 - A5 r ^ 6 / 8 -
A6 r ^ 7 / 8`, the polynomial of `Pow.powLog` divided by `r`. -/
def kernel : List ℚ :=
  [1, -1 / 2, -ratOfWord 0xBFE5555555555560 / 2, -ratOfWord 0x3FE0000000000006 / 2,
    ratOfWord 0x3FE999999959554E / 4, ratOfWord 0xBFE555555529A47A / 4,
    -ratOfWord 0xBFF2495B9B4845E9 / 8, -ratOfWord 0x3FF0002B8B263FC3 / 8]

theorem kernel_check :
    check (subP (log1pQuotCoeffs 10) kernel) (-23 / 4000) (23 / 4000) (5 / 2 ^ 70) 5 = true := by
  decide +kernel

/-- The polynomial of `Pow.powLog` relative to `r`. -/
theorem kernel_error (r : ℝ) (hr : |r| ≤ 23 / 4000) :
    |Real.log (1 + r) - r * eval kernel r| ≤ |r| * (6 / 2 ^ 70) := by
  have hr1 : |r| < 1 := hr.trans_lt (by norm_num)
  have hrem := log1p_remainder r hr1 10
  rw [eval_log1pCoeffs] at hrem
  obtain ⟨hlo, hhi⟩ := abs_le.mp hr
  have hc := check_sound _ _ _ _ _ kernel_check r (by push_cast; linarith) (by push_cast; linarith)
  rw [eval_subP] at hc
  have hc' : |eval (log1pQuotCoeffs 10) r - eval kernel r| ≤ 5 / 2 ^ 70 :=
    hc.trans (le_of_eq (by norm_num))
  have hd : |r * eval (log1pQuotCoeffs 10) r - r * eval kernel r| ≤ |r| * (5 / 2 ^ 70) := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left hc' (abs_nonneg r)
  have ht : |r| ^ (10 + 1) / (1 - |r|) ≤ |r| * (1 / 2 ^ 70) := by
    have h1 : 0 < 1 - |r| := by linarith
    have h2 : (3977 / 4000 : ℝ) ≤ 1 - |r| := by linarith
    have hp : |r| ^ 10 ≤ (23 / 4000) ^ 10 := pow_le_pow_left₀ (abs_nonneg r) hr 10
    rw [div_le_iff₀ h1, pow_succ]
    calc |r| ^ 10 * |r| ≤ ((1 / 2 ^ 70) * (1 - |r|)) * |r| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg r)
          calc |r| ^ 10 ≤ (1 / 2 ^ 70) * (3977 / 4000) := hp.trans (by norm_num)
            _ ≤ (1 / 2 ^ 70) * (1 - |r|) := by gcongr
      _ = |r| * (1 / 2 ^ 70) * (1 - |r|) := by ring
  calc |Real.log (1 + r) - r * eval kernel r| ≤
      |Real.log (1 + r) - r * eval (log1pQuotCoeffs 10) r| +
        |r * eval (log1pQuotCoeffs 10) r - r * eval kernel r| := abs_sub_le _ _ _
    _ ≤ |r| * (1 / 2 ^ 70) + |r| * (5 / 2 ^ 70) := add_le_add (hrem.trans ht) hd
    _ = |r| * (6 / 2 ^ 70) := by ring

theorem a0_value : value 0xBFE0000000000000 = -1 / 2 := by
  have h : ratOfWord 0xBFE0000000000000 = -1 / 2 := by decide +kernel
  rw [← ratOfWord_cast, h]
  norm_num

/-- `p` of `Pow.powLog` on reals, in the order of the code, with `ar = A0 r`. -/
noncomputable def poly (r : ℝ) : ℝ :=
  let ar := value 0xBFE0000000000000 * r
  let ar2 := r * ar
  let ar3 := r * ar2
  ar3 * (value 0xBFE5555555555560 + r * value 0x3FE0000000000006 +
    ar2 * (value 0x3FE999999959554E + r * value 0xBFE555555529A47A +
      ar2 * (value 0xBFF2495B9B4845E9 + r * value 0x3FF0002B8B263FC3)))

theorem kernel_eval (r : ℝ) : r * eval kernel r = r - r ^ 2 / 2 + poly r := by
  simp only [kernel, eval_cons, eval_nil]
  push_cast
  simp only [ratOfWord_cast, poly, a0_value]
  ring

#print axioms checked_entries
#print axioms checked_logs
#print axioms exp_near
#print axioms log_table
#print axioms kernel_check
#print axioms kernel_error
#print axioms a0_value
#print axioms kernel_eval

end Verified.Examples.PowLogTable
