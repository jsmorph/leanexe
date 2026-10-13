import Verified.Examples.Tgamma
import LeanExe.ProofKit.PolyBound
import LeanExe.ProofKit.F64Order

/-!
The argument reduction of `Tgamma.asLogd`: for every mantissa `m` of a normal double, the index
`j = jOf tab m` that the code computes from the top bits of `m` selects the factor
`r = r1 (j / 32) · r2 (j % 32)` with `|r t - 1| ≤ 1/2400` for `t = 1 + m/2^52`.

The code computes `j` from `m = i 2^47 + 2^16 k + s` as `f/2^42` with
`f = i 2^47 + A_i + 2^16 k + s + B_i k`, where `A_i = tab[2i] 2^33` and `B_i` is `tab[2i+1]` read as
a signed word, so that the product wraps modulo `2^64` for the negative `B_i` of `i ≥ 14`.
`redCheck` checks, for each bucket `i` and each index `j` it reaches, that `|r t - 1| ≤ 1/2400` at
the ends of an interval of `t` that contains every mantissa with index `j`: from `f` within `|B_i|`
of the linear function `i 2^47 + A_i + (m - i 2^47) (2^16 + B_i)/2^16`.  `red_sound` turns the
check into the bound, and `redCheck_logd` evaluates it for `Tgamma.logdTable` with the kernel.
A sample of 2.6 million mantissas gives `4.03 · 10^-4` against `1/2400 ≈ 4.17 · 10^-4`
(`devnotes.md`), and the check's intervals reach `4.0297 · 10^-4`.
-/

namespace Verified.Examples.TgammaLogdRed
open LeanExe.ProofKit PolyBound

set_option exponentiation.threshold 4096

/-- The index of `asLogd`'s reduction for the mantissa `m`, as the code computes it. -/
def jOf (tab : Array UInt64) (m : UInt64) : UInt64 :=
  let i : UInt64 := m >>> 47
  let d : UInt64 := m &&& 0x7FFFFFFFFFFF
  (m + (tab[(2 * i).toNat]! <<< 33) + tab[(2 * i + 1).toNat]! * (d >>> 16)) >>> 42

/-- A word read as a signed integer. -/
def sgn (w : UInt64) : ℤ := if 2 ^ 63 ≤ w.toNat then (w.toNat : ℤ) - 2 ^ 64 else w.toNat

/-- `2 ^ 1074` times the value of a nonnegative word. -/
def us (w : UInt64) : ℕ := F64Order.unsignedScaled w.toNat

/-- `|r t - 1| ≤ 1/2400` for `r = P/2^2148` and `t = T/(2^52 S)`. -/
def endOK (P : ℕ) (T S : ℤ) : Bool := decide (2400 * |(P : ℤ) * T - 2 ^ 2200 * S| ≤ 2 ^ 2200 * S)

/-- The constants of bucket `i`: `f = C + k S + s` for `m = i 2^47 + 2^16 k + s`. -/
def Aof (tab : Array UInt64) (i : ℕ) : ℤ := tab[2 * i]!.toNat * 2 ^ 33
def Bof (tab : Array UInt64) (i : ℕ) : ℤ := sgn tab[2 * i + 1]!
def Sof (tab : Array UInt64) (i : ℕ) : ℤ := 2 ^ 16 + Bof tab i
def Cof (tab : Array UInt64) (i : ℕ) : ℤ := i * 2 ^ 47 + Aof tab i
def fmaxOf (tab : Array UInt64) (i : ℕ) : ℤ := Cof tab i + (2 ^ 31 - 1) * Sof tab i + (2 ^ 16 - 1)

/-- `2 ^ 2148` times the reduction factor `r1 (j / 32) · r2 (j % 32)` of index `j`. -/
def Pof (tab : Array UInt64) (j : ℕ) : ℕ := us tab[64 + j / 32]! * us tab[97 + j % 32]!

/-- `S` times the ends `N/S + i 2^47` of the interval of mantissas with index `j`, plus `2^52 S`. -/
def Tlo (tab : Array UInt64) (i : ℕ) (j : ℤ) : ℤ :=
  2 ^ 52 * Sof tab i + (j * 2 ^ 42 - |Bof tab i| - Cof tab i) * 2 ^ 16 + i * 2 ^ 47 * Sof tab i
def Thi (tab : Array UInt64) (i : ℕ) (j : ℤ) : ℤ :=
  2 ^ 52 * Sof tab i + ((j + 1) * 2 ^ 42 + |Bof tab i| - Cof tab i) * 2 ^ 16 +
    i * 2 ^ 47 * Sof tab i

/-- The check for bucket `i` and index `j = C/2^42 + jj`: the bound at the two ends of the
interval of mantissas that can have index `j`. -/
def jCheck (tab : Array UInt64) (i : ℕ) (jj : ℕ) : Bool :=
  let j : ℤ := Cof tab i / 2 ^ 42 + jj
  endOK (Pof tab j.toNat) (Tlo tab i j) (Sof tab i) &&
    endOK (Pof tab j.toNat) (Thi tab i j) (Sof tab i)

/-- The check for bucket `i`. -/
def iCheck (tab : Array UInt64) (i : ℕ) : Bool :=
  decide (tab[2 * i]!.toNat < 2 ^ 31) && decide (0 < Sof tab i) && decide (fmaxOf tab i < 2 ^ 64) &&
    decide (fmaxOf tab i / 2 ^ 42 ≤ 1024) &&
    (List.range ((fmaxOf tab i / 2 ^ 42 - Cof tab i / 2 ^ 42).toNat + 1)).all (jCheck tab i)

/-! ### Soundness -/

theorem jOf_toNat (tab : Array UInt64) (m : UInt64) (hm : m.toNat < 2 ^ 52)
    (hA : tab[2 * (m.toNat / 2 ^ 47)]!.toNat < 2 ^ 31) :
    (jOf tab m).toNat = (m.toNat + tab[2 * (m.toNat / 2 ^ 47)]!.toNat * 2 ^ 33 +
      tab[2 * (m.toNat / 2 ^ 47) + 1]!.toNat * (m.toNat % 2 ^ 47 / 2 ^ 16)) % 2 ^ 64 / 2 ^ 42 := by
  have hi : (2 * (m >>> (47 : UInt64))).toNat = 2 * (m.toNat / 2 ^ 47) := by
    rw [UInt64.toNat_mul, UInt64.toNat_shiftRight]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    have : m.toNat / 2 ^ 47 < 32 := by omega
    omega
  have hi1 : (2 * (m >>> (47 : UInt64)) + 1).toNat = 2 * (m.toNat / 2 ^ 47) + 1 := by
    rw [UInt64.toNat_add, hi]
    simp only [UInt64.reduceToNat]
    have : m.toNat / 2 ^ 47 < 32 := by omega
    omega
  have hd : ((m &&& (0x7FFFFFFFFFFF : UInt64)) >>> (16 : UInt64)).toNat = m.toNat % 2 ^ 47 / 2 ^ 16 := by
    rw [UInt64.toNat_shiftRight, UInt64.toNat_and]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    rw [show (0x7FFFFFFFFFFF : ℕ) = 2 ^ 47 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  unfold jOf
  simp only []
  rw [hi, hi1, UInt64.toNat_shiftRight, UInt64.toNat_add, UInt64.toNat_add, UInt64.toNat_mul,
    UInt64.toNat_shiftLeft, hd]
  simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := tab[2 * (m.toNat / 2 ^ 47)]!.toNat * 2 ^ 33) (by
    calc tab[2 * (m.toNat / 2 ^ 47)]!.toNat * 2 ^ 33 < 2 ^ 31 * 2 ^ 33 := by
          exact Nat.mul_lt_mul_of_pos_right hA (by positivity)
      _ = 2 ^ 64 := by norm_num)]
  rw [Nat.add_mod (m.toNat + _) _]


theorem sgn_mod (w : UInt64) : ∃ q : ℤ, (w.toNat : ℤ) = sgn w + 2 ^ 64 * q ∧ (q = 0 ∨ q = 1) := by
  unfold sgn
  split
  · exact ⟨1, by ring, Or.inr rfl⟩
  · exact ⟨0, by ring, Or.inl rfl⟩

theorem sgn_abs (w : UInt64) : |sgn w| ≤ 2 ^ 63 := by
  have := w.toNat_lt
  unfold sgn
  split
  · rw [abs_le]; constructor <;> omega
  · rw [abs_le]; constructor <;> omega

theorem Sof_eq (tab : Array UInt64) (i : ℕ) : Sof tab i = 2 ^ 16 + Bof tab i := rfl
theorem Bof_eq (tab : Array UInt64) (i : ℕ) : Bof tab i = sgn tab[2 * i + 1]! := rfl
theorem Cof_eq (tab : Array UInt64) (i : ℕ) : Cof tab i = i * 2 ^ 47 + tab[2 * i]!.toNat * 2 ^ 33 := rfl
theorem fmaxOf_eq (tab : Array UInt64) (i : ℕ) :
    fmaxOf tab i = Cof tab i + (2 ^ 31 - 1) * Sof tab i + (2 ^ 16 - 1) := rfl
theorem Tlo_eq (tab : Array UInt64) (i : ℕ) (j : ℤ) : Tlo tab i j = 2 ^ 52 * Sof tab i +
    (j * 2 ^ 42 - |Bof tab i| - Cof tab i) * 2 ^ 16 + i * 2 ^ 47 * Sof tab i := rfl
theorem Thi_eq (tab : Array UInt64) (i : ℕ) (j : ℤ) : Thi tab i j = 2 ^ 52 * Sof tab i +
    ((j + 1) * 2 ^ 42 + |Bof tab i| - Cof tab i) * 2 ^ 16 + i * 2 ^ 47 * Sof tab i := rfl

theorem abs_scaled {x y : ℤ} (h : 2400 * |x| ≤ y) : -y ≤ 2400 * x ∧ 2400 * x ≤ y := by
  have : |2400 * x| ≤ y := by rw [abs_mul]; exact h
  exact abs_le.mp this

/-- **The reduction bound**: for every mantissa `m`, the index `j` of the code selects a factor `r`
with `|r t - 1| ≤ 1/2400`, `t = 1 + m/2^52`, when the check passes for every bucket. -/
theorem red_sound (tab : Array UInt64) (hc : ∀ i < 32, iCheck tab i = true) (m : UInt64)
    (hm : m.toNat < 2 ^ 52) :
    (jOf tab m).toNat ≤ 1024 ∧
      |(Pof tab (jOf tab m).toNat : ℝ) / 2 ^ 2148 * (1 + (m.toNat : ℝ) / 2 ^ 52) - 1| ≤
        1 / 2400 := by
  obtain ⟨n, hn⟩ : ∃ n, m.toNat = n := ⟨_, rfl⟩
  rw [hn] at hm ⊢
  obtain ⟨i, hi⟩ : ∃ i, n / 2 ^ 47 = i := ⟨_, rfl⟩
  have hi32 : i < 32 := by omega
  have hci := hc i hi32
  unfold iCheck at hci
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hci
  obtain ⟨⟨⟨⟨hA, hS⟩, hfmax⟩, hj1024⟩, hall⟩ := hci
  have hjn := jOf_toNat tab m (by rw [hn]; exact hm) (by rw [hn, hi]; exact hA)
  rw [hn, hi] at hjn
  obtain ⟨k, hk⟩ : ∃ k, n % 2 ^ 47 / 2 ^ 16 = k := ⟨_, rfl⟩
  rw [hk] at hjn
  obtain ⟨s, hs⟩ : ∃ s, n % 2 ^ 16 = s := ⟨_, rfl⟩
  have hnks : n = i * 2 ^ 47 + 2 ^ 16 * k + s := by omega
  have hk31 : k < 2 ^ 31 := by omega
  have hs16 : s < 2 ^ 16 := by omega
  obtain ⟨q, hq, -⟩ := sgn_mod tab[2 * i + 1]!
  have hC0' : 0 ≤ Cof tab i := by rw [Cof_eq]; positivity
  obtain ⟨f, hf⟩ : ∃ f : ℤ, f = Cof tab i + k * Sof tab i + s := ⟨_, rfl⟩
  have hkS : 0 ≤ (k : ℤ) * Sof tab i := mul_nonneg (by positivity) hS.le
  have hf0 : 0 ≤ f := by rw [hf]; have := Int.natCast_nonneg s; linarith
  have hfle : f ≤ fmaxOf tab i := by
    have hk' : (k : ℤ) ≤ 2 ^ 31 - 1 := by omega
    have hs' : (s : ℤ) ≤ 2 ^ 16 - 1 := by omega
    have h1 : (k : ℤ) * Sof tab i ≤ (2 ^ 31 - 1) * Sof tab i :=
      mul_le_mul_of_nonneg_right hk' hS.le
    rw [hf, fmaxOf_eq]; linarith
  -- the code's sum is `f`
  have hsum : (((n + tab[2 * i]!.toNat * 2 ^ 33 + tab[2 * i + 1]!.toNat * k) % 2 ^ 64 : ℕ) : ℤ) =
      f := by
    have hcast : (((n + tab[2 * i]!.toNat * 2 ^ 33 + tab[2 * i + 1]!.toNat * k) % 2 ^ 64 : ℕ) : ℤ) =
        ((n : ℤ) + tab[2 * i]!.toNat * 2 ^ 33 + tab[2 * i + 1]!.toNat * k) % 2 ^ 64 := by
      push_cast; rfl
    rw [hcast, hq]
    have : (n : ℤ) + tab[2 * i]!.toNat * 2 ^ 33 + (sgn tab[2 * i + 1]! + 2 ^ 64 * q) * k =
        f + 2 ^ 64 * (q * k) := by
      rw [hf, Sof_eq, Cof_eq, Bof_eq, hnks]; push_cast; ring
    rw [this, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hf0 (lt_of_le_of_lt hfle hfmax)]
  obtain ⟨jN, hjN⟩ : ∃ j, (jOf tab m).toNat = j := ⟨_, rfl⟩
  rw [hjN] at hjn ⊢
  have hjZ : (jN : ℤ) = f / 2 ^ 42 := by
    rw [hjn, ← hsum]
    push_cast; rfl
  have hfj1 : (jN : ℤ) * 2 ^ 42 ≤ f := by
    rw [hjZ]; exact Int.ediv_mul_le f (by norm_num)
  have hfj2 : f < ((jN : ℤ) + 1) * 2 ^ 42 := by
    rw [hjZ]; exact Int.lt_ediv_add_one_mul_self f (by norm_num)
  have hCle : Cof tab i / 2 ^ 42 ≤ (jN : ℤ) := by
    rw [hjZ]; apply Int.ediv_le_ediv (by norm_num); rw [hf]
    linarith [(Int.natCast_nonneg s)]
  have hjle : (jN : ℤ) ≤ fmaxOf tab i / 2 ^ 42 := by
    rw [hjZ]; exact Int.ediv_le_ediv (by norm_num) hfle
  refine ⟨by omega, ?_⟩
  -- the check for `j`
  have hC0 : 0 ≤ Cof tab i / 2 ^ 42 := Int.ediv_nonneg hC0' (by norm_num)
  obtain ⟨jj, hjj⟩ : ∃ jj : ℕ, (jj : ℤ) = (jN : ℤ) - Cof tab i / 2 ^ 42 :=
    ⟨((jN : ℤ) - Cof tab i / 2 ^ 42).toNat, Int.toNat_of_nonneg (by linarith)⟩
  have hjjv : Cof tab i / 2 ^ 42 + (jj : ℤ) = jN := by rw [hjj]; ring
  have hjc := hall jj (by
    have : (jj : ℤ) < (fmaxOf tab i / 2 ^ 42 - Cof tab i / 2 ^ 42).toNat + 1 := by
      rw [Int.toNat_of_nonneg (by linarith), hjj]; linarith
    exact_mod_cast this)
  unfold jCheck at hjc
  simp only [Bool.and_eq_true] at hjc
  rw [hjjv] at hjc
  simp only [Int.toNat_natCast] at hjc
  obtain ⟨hlo, hhi⟩ := hjc
  unfold endOK at hlo hhi
  simp only [decide_eq_true_eq] at hlo hhi
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, (2 : ℤ) ^ 2200 = Q := ⟨_, rfl⟩
  rw [hQ] at hlo hhi
  obtain ⟨hlo1, hlo2⟩ := abs_scaled hlo
  obtain ⟨hhi1, hhi2⟩ := abs_scaled hhi
  -- the mantissa lies between the two ends
  have hkey : Sof tab i * ((n : ℤ) - i * 2 ^ 47) = 2 ^ 16 * (f - Cof tab i) + Bof tab i * s := by
    rw [hf, Sof_eq, hnks]; push_cast; ring
  have hBs : |Bof tab i * s| ≤ |Bof tab i| * 2 ^ 16 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ s)]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hs16.le) (abs_nonneg _)
  obtain ⟨hBs1, hBs2⟩ := abs_le.mp hBs
  obtain ⟨X, hX⟩ : ∃ X : ℤ, Sof tab i * (2 ^ 52 + (n : ℤ)) = X := ⟨_, rfl⟩
  have hsplit : X = 2 ^ 52 * Sof tab i + Sof tab i * ((n : ℤ) - i * 2 ^ 47) +
      i * 2 ^ 47 * Sof tab i := by rw [← hX]; ring
  have hT1 : Tlo tab i jN ≤ X := by rw [Tlo_eq, hsplit, hkey]; linarith
  have hT2 : X ≤ Thi tab i jN := by rw [Thi_eq, hsplit, hkey]; linarith
  have hP0 : (0 : ℤ) ≤ (Pof tab jN : ℤ) := Int.natCast_nonneg _
  have hm1 := mul_le_mul_of_nonneg_left hT1 hP0
  have hm2 := mul_le_mul_of_nonneg_left hT2 hP0
  have hmid1 : -(Q * Sof tab i) ≤ 2400 * ((Pof tab jN : ℤ) * X - Q * Sof tab i) := by linarith
  have hmid2 : 2400 * ((Pof tab jN : ℤ) * X - Q * Sof tab i) ≤ Q * Sof tab i := by linarith
  -- in the reals
  have hS0 : (0 : ℝ) < (Sof tab i : ℝ) := by exact_mod_cast hS
  have hQR : (Q : ℝ) = 2 ^ 2200 := by rw [← hQ, Int.cast_pow, Int.cast_ofNat]
  have hXR : (X : ℝ) = (Sof tab i : ℝ) * (2 ^ 52 + n) := by
    rw [← hX]; push_cast; ring
  have hr1 : -((Q : ℝ) * Sof tab i) ≤ 2400 * ((Pof tab jN : ℝ) * X - Q * Sof tab i) := by
    exact_mod_cast hmid1
  have hr2 : 2400 * ((Pof tab jN : ℝ) * X - Q * Sof tab i) ≤ (Q : ℝ) * Sof tab i := by
    exact_mod_cast hmid2
  rw [hQR, hXR] at hr1 hr2
  have hrw : (Pof tab jN : ℝ) / 2 ^ 2148 * (1 + (n : ℝ) / 2 ^ 52) - 1 =
      ((Pof tab jN : ℝ) * ((Sof tab i : ℝ) * (2 ^ 52 + n)) - 2 ^ 2200 * Sof tab i) /
        (2 ^ 2200 * Sof tab i) := by
    field_simp
  rw [hrw, abs_le, le_div_iff₀ (by positivity), div_le_iff₀ (by positivity)]
  constructor <;> nlinarith

#print axioms red_sound

end Verified.Examples.TgammaLogdRed
