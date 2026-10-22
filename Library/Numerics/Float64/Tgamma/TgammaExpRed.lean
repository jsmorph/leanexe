import Library.Numerics.Float64.Tgamma.TgammaMul
import Library.Numerics.Float64.Tgamma.TgammaMainRed
import Library.Numerics.Float64.Tgamma.TgammaApprox
import Library.Numerics.Float64.Tgamma.TgammaWords
import Library.Numerics.Float64.Tgamma.TgammaSmall

/-!
The argument reduction of `Tgamma.asExpd` for `1 ≤ x + l ≤ 1001` and `|l| ≤ 2 ^ -14`.  The product
of `x + l` with the double-double `1024/ln 2` lies within `2 ^ -54` of `(x + l) invLn2`, and its low
part, which carries `1477 l`, stays below `1/10` (`exp_mulc`).  The high part rounds to an integer
`K ≥ 1000`, and the double-double `X = q1 + q2` after the subtraction of `K` lies within `2 ^ -53` of
the product minus `K`, with `|q1| ≤ 61/100` and `|q2| ≤ 2 ^ -52` (`exp_red`).  The code's subtraction and `fastTwoSum` are exact, but the analysis does not need it:
an error of `2 ^ -53` in `X` changes the result by about `2 ^ -63.5` relative.  `exp_index` gives
the table indices and the exponent `K / 1024` from the word of `K`.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaExpRed
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul TgammaWords TgammaMainRed
  TgammaFloor

set_option exponentiation.threshold 4096

theorem ih_finite : Wasm.IEEE64.isFinite 0x40971547652B82FE = true := by decide
theorem il_finite : Wasm.IEEE64.isFinite 0x3D1777D0FFDA0D24 = true := by decide

theorem ih_le : |value (Float.ofBits 0x40971547652B82FE).toBits| ≤ 1478 := by
  rw [ofBits_value _ ih_finite]
  have := TgammaSmall.abs_rat_le _ 1478
    (show PolyBound.qabs (PolyBound.ratOfWord 0x40971547652B82FE) ≤ 1478 by decide +kernel)
  push_cast at this
  exact this

theorem il_le : |value (Float.ofBits 0x3D1777D0FFDA0D24).toBits| ≤ 1 / 2 ^ 45 := by
  rw [ofBits_value _ il_finite]
  have := TgammaSmall.abs_rat_le _ (1 / 2 ^ 45)
    (show PolyBound.qabs (PolyBound.ratOfWord 0x3D1777D0FFDA0D24) ≤ 1 / 2 ^ 45 by decide +kernel)
  push_cast at this
  exact this

theorem invLn2_eq : value (Float.ofBits 0x40971547652B82FE).toBits +
    value (Float.ofBits 0x3D1777D0FFDA0D24).toBits = (TgammaApprox.invLn2 : ℝ) := by
  rw [ofBits_value _ ih_finite, ofBits_value _ il_finite, TgammaApprox.invLn2]
  push_cast
  ring

/-- **The product** `(x + l) (1024/ln 2)` as a double-double. -/
theorem exp_mulc (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (x l : Float) (hx : Finite x.toBits)
    (hl : Finite l.toBits) (hY : |value x.toBits + value l.toBits| ≤ 1001)
    (hlb : |value l.toBits| ≤ 1 / 2 ^ 14) :
    Finite (mulDD x l (Float.ofBits 0x40971547652B82FE)
        (Float.ofBits 0x3D1777D0FFDA0D24)).1.toBits ∧
      Finite (mulDD x l (Float.ofBits 0x40971547652B82FE)
        (Float.ofBits 0x3D1777D0FFDA0D24)).2.toBits ∧
      |value (mulDD x l (Float.ofBits 0x40971547652B82FE)
          (Float.ofBits 0x3D1777D0FFDA0D24)).1.toBits +
        value (mulDD x l (Float.ofBits 0x40971547652B82FE)
          (Float.ofBits 0x3D1777D0FFDA0D24)).2.toBits -
        (value x.toBits + value l.toBits) * TgammaApprox.invLn2| ≤ 1 / 2 ^ 54 ∧
      |value (mulDD x l (Float.ofBits 0x40971547652B82FE)
        (Float.ofBits 0x3D1777D0FFDA0D24)).2.toBits| ≤ 1 / 10 ∧
      |value (mulDD x l (Float.ofBits 0x40971547652B82FE)
        (Float.ofBits 0x3D1777D0FFDA0D24)).1.toBits| ≤ 2 ^ 21 := by
  have hxb : |value x.toBits| ≤ 1002 := by
    have := abs_sub (value x.toBits + value l.toBits) (value l.toBits)
    rw [add_sub_cancel_right] at this
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 14 ≤ 1)]
  have h0 := abs_nonneg (value x.toBits)
  have h0' := abs_nonneg (value l.toBits)
  obtain ⟨h1, h2, he, hlow, hhigh⟩ := mulDD_spec hF x l (Float.ofBits 0x40971547652B82FE)
    (Float.ofBits 0x3D1777D0FFDA0D24) hx hl (ofBits_finite _ ih_finite) (ofBits_finite _ il_finite)
    (1478 * 1002) (1478 * (1 / 2 ^ 14)) (1 / 2 ^ 45 * 1002) (1 / 2 ^ 45 * (1 / 2 ^ 14))
    (mul_le_mul ih_le hxb h0 (by norm_num)) (mul_le_mul ih_le hlb h0' (by norm_num))
    (mul_le_mul il_le hxb h0 (by norm_num)) (mul_le_mul il_le hlb h0' (by norm_num))
    (by norm_num) (by norm_num)
  rw [invLn2_eq] at he
  refine ⟨h1, h2, ?_, ?_, ?_⟩
  · refine he.trans ?_
    norm_num
  · refine hlow.trans ?_
    norm_num
  · refine hhigh.trans ?_
    norm_num

/-- **The reduction** by the nearest integer `K` of the high part. -/
theorem exp_red (p1 p2 : Float) (hp1 : Finite p1.toBits) (hp2 : Finite p2.toBits)
    (hp2b : |value p2.toBits| ≤ 1 / 10) (hlo : 1000 ≤ value p1.toBits)
    (hhi : value p1.toBits ≤ 2 ^ 21) :
    ∃ K : ℕ, (K : ℝ) = value (roundEven p1).toBits ∧ K ≤ 2 ^ 22 ∧ Finite (roundEven p1).toBits ∧
      Finite (fastTwoSum (p1 - roundEven p1) p2).1.toBits ∧
      Finite (fastTwoSum (p1 - roundEven p1) p2).2.toBits ∧
      |value (fastTwoSum (p1 - roundEven p1) p2).1.toBits +
          value (fastTwoSum (p1 - roundEven p1) p2).2.toBits -
          (value p1.toBits + value p2.toBits - K)| ≤ 1 / 2 ^ 53 ∧
      |value (fastTwoSum (p1 - roundEven p1) p2).1.toBits| ≤ 61 / 100 ∧
      |value (fastTwoSum (p1 - roundEven p1) p2).2.toBits| ≤ 1 / 2 ^ 52 := by
  obtain ⟨hif, ⟨R, hR⟩, hRd, -⟩ := roundEven_spec p1 hp1
  obtain ⟨hRd1, hRd2⟩ := abs_le.mp hRd
  have hR0 : 0 ≤ R := by
    have : (0 : ℝ) ≤ R := by rw [← hR]; linarith
    exact_mod_cast this
  have hKR : ((R.toNat : ℕ) : ℝ) = (R : ℝ) := by
    have : ((R.toNat : ℤ) : ℝ) = (R : ℝ) := by rw [Int.toNat_of_nonneg hR0]
    exact_mod_cast this
  refine ⟨R.toNat, ?_, ?_, hif, ?_⟩
  · rw [hKR, hR]
  · have : (R : ℝ) ≤ 2 ^ 22 := by rw [← hR]; linarith [(by norm_num : (2 : ℝ) ^ 21 + 1 ≤ 2 ^ 22)]
    have : R ≤ 2 ^ 22 := by exact_mod_cast this
    omega
  rw [hKR]
  set ix := roundEven p1 with hix
  -- `d = p1 - ix`
  have hd := fapprox_sub (fapprox_self p1 hp1) (fapprox_self ix hif) (1 / 2)
    (by rw [add_zero, add_zero, abs_le]; constructor <;> linarith) (by norm_num)
  set d := p1 - ix with hddef
  have hde : |value d.toBits - (value p1.toBits - value ix.toBits)| ≤ 1 / 2 ^ 54 := by
    have := hd.2; linarith [(by norm_num : (0 : ℝ) + 0 + 1 / 2 / 2 ^ 53 = 1 / 2 ^ 54)]
  have hdb : |value d.toBits| ≤ 1 / 2 + 1 / 2 ^ 54 := by
    have := abs_sub_abs_le_abs_sub (value d.toBits) (value p1.toBits - value ix.toBits)
    have : |value p1.toBits - value ix.toBits| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    linarith
  -- `s = d + p2`
  have hs := fapprox_add (fapprox_self d hd.1) (fapprox_self p2 hp2) (|value d.toBits + value p2.toBits|)
    (by simp only [add_zero, le_refl])
    (by linarith [abs_add_le (value d.toBits) (value p2.toBits), (by norm_num : (1 : ℝ) / 2 + 1 / 2 ^ 54 +
      1 / 10 < 2 ^ 1023)])
  set s := d + p2 with hsdef
  have hse : |value s.toBits - (value d.toBits + value p2.toBits)| ≤ 1 / 2 ^ 53 * 0.61 := by
    have h := hs.2
    have : |value d.toBits + value p2.toBits| ≤ 0.61 := by
      linarith [abs_add_le (value d.toBits) (value p2.toBits), (by norm_num : (1 : ℝ) / 2 + 1 / 2 ^ 54 +
        1 / 10 ≤ 0.61)]
    simp only [zero_add] at h
    have : |value d.toBits + value p2.toBits| / 2 ^ 53 ≤ 0.61 / 2 ^ 53 := div_le_div_of_nonneg_right this (by norm_num)
    linarith
  -- `z = s - d`
  have hsd : |value s.toBits - value d.toBits| ≤ 1 / 8 := by
    have := abs_sub (value s.toBits - (value d.toBits + value p2.toBits)) (-value p2.toBits)
    rw [show value s.toBits - (value d.toBits + value p2.toBits) - -value p2.toBits = value s.toBits - value d.toBits by ring,
      abs_neg] at this
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 53 * 0.61 + 1 / 10 ≤ 1 / 8)]
  have hz := fapprox_sub (fapprox_self s hs.1) (fapprox_self d hd.1) (1 / 8)
    (by rw [add_zero, add_zero]; exact hsd) (by norm_num)
  set z := s - d with hzdef
  have hze : |value z.toBits - (value s.toBits - value d.toBits)| ≤ 1 / 2 ^ 56 := by
    have := hz.2; linarith [(by norm_num : (0 : ℝ) + 0 + 1 / 8 / 2 ^ 53 = 1 / 2 ^ 56)]
  -- `t = p2 - z`
  have hpz : |value p2.toBits - value z.toBits| ≤ 1 / 2 ^ 53 := by
    have h1 := abs_add_le (value p2.toBits - (value s.toBits - value d.toBits))
      (value s.toBits - value d.toBits - value z.toBits)
    rw [show value p2.toBits - (value s.toBits - value d.toBits) + (value s.toBits - value d.toBits - value z.toBits)
      = value p2.toBits - value z.toBits by ring] at h1
    have h2 : |value p2.toBits - (value s.toBits - value d.toBits)| = |value s.toBits - (value d.toBits + value p2.toBits)| := by
      rw [abs_sub_comm]; congr 1; ring
    have h3 : |value s.toBits - value d.toBits - value z.toBits| =
        |value z.toBits - (value s.toBits - value d.toBits)| := abs_sub_comm _ _
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 53 * 0.61 + 1 / 2 ^ 56 ≤ 1 / 2 ^ 53)]
  have ht := fapprox_sub (fapprox_self p2 hp2) (fapprox_self z hz.1) (1 / 2 ^ 53)
    (by rw [add_zero, add_zero]; exact hpz) (by norm_num)
  have hte : |value (p2 - z).toBits - (value p2.toBits - value z.toBits)| ≤ 1 / 2 ^ 106 := by
    have := ht.2; linarith [(by norm_num : (0 : ℝ) + 0 + 1 / 2 ^ 53 / 2 ^ 53 = 1 / 2 ^ 106)]
  have hft : fastTwoSum d p2 = (s, p2 - z) := rfl
  rw [hft]
  dsimp only
  refine ⟨hs.1, ht.1, ?_, ?_, ?_⟩
  · have hsplit : value s.toBits + value (p2 - z).toBits - (value p1.toBits + value p2.toBits - value ix.toBits) =
        (value (p2 - z).toBits - (value p2.toBits - value z.toBits)) -
        (value z.toBits - (value s.toBits - value d.toBits)) +
        (value d.toBits - (value p1.toBits - value ix.toBits)) := by ring
    rw [← hR, hsplit]
    have h1 := abs_add_le ((value (p2 - z).toBits - (value p2.toBits - value z.toBits)) -
        (value z.toBits - (value s.toBits - value d.toBits))) (value d.toBits - (value p1.toBits - value ix.toBits))
    have h2 := abs_sub (value (p2 - z).toBits - (value p2.toBits - value z.toBits))
        (value z.toBits - (value s.toBits - value d.toBits))
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 106 + 1 / 2 ^ 56 + 1 / 2 ^ 54 ≤ 1 / 2 ^ 53)]
  · have := abs_sub_abs_le_abs_sub (value s.toBits) (value d.toBits + value p2.toBits)
    linarith [abs_add_le (value d.toBits) (value p2.toBits), (by norm_num : (1 : ℝ) / 2 + 1 / 2 ^ 54 + 1 / 10 +
      1 / 2 ^ 53 * 0.61 ≤ 61 / 100)]
  · have := abs_sub_abs_le_abs_sub (value (p2 - z).toBits) (value p2.toBits - value z.toBits)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 53 + 1 / 2 ^ 106 ≤ 1 / 2 ^ 52)]

/-- **The indices and the exponent** from the word of `K`. -/
theorem exp_index (K : ℕ) (hK : K < 2 ^ 40) :
    ((UInt64.ofNat K >>> 5) &&& 31).toNat = K / 32 % 32 ∧ (UInt64.ofNat K &&& 31).toNat = K % 32 ∧
      sar (UInt64.ofNat K) 10 = UInt64.ofNat (K / 1024) := by
  have hs : UInt64.size = 2 ^ 64 := rfl
  have hk : (UInt64.ofNat K).toNat = K := UInt64.toNat_ofNat_of_lt' (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hk]
    show K >>> (5 % 64) &&& 31 = K / 32 % 32
    rw [show 5 % 64 = 5 from rfl, Nat.shiftRight_eq_div_pow, show (31 : ℕ) = 2 ^ 5 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]
  · rw [UInt64.toNat_and, hk]
    show K &&& 31 = K % 32
    rw [show (31 : ℕ) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  · unfold sar
    have h63 : ¬ ((UInt64.ofNat K >>> 63 == 1) = true) := by
      intro h
      have h' : UInt64.ofNat K >>> 63 = 1 := by simpa using h
      have := congrArg UInt64.toNat h'
      rw [UInt64.toNat_shiftRight, hk] at this
      have h2 : K >>> ((63 : UInt64).toNat % 64) = 0 := by
        rw [show (63 : UInt64).toNat % 64 = 63 from rfl, Nat.shiftRight_eq_div_pow]
        exact Nat.div_eq_of_lt (by omega)
      rw [h2] at this
      exact absurd this (by decide)
    rw [ite_eq_right h63]
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_shiftRight, hk, UInt64.toNat_ofNat_of_lt' (by omega)]
    show K >>> (10 % 64) = K / 1024
    rw [show 10 % 64 = 10 from rfl, Nat.shiftRight_eq_div_pow]

/-- `toWord` of a nonnegative integer-valued double. -/
theorem toWord_nat (v : Float) (K : ℕ) (hv : Finite v.toBits) (hK : value v.toBits = K)
    (hK63 : K < 2 ^ 63) : toWord v = UInt64.ofNat K := by
  unfold toWord
  have hnlt : ¬ v < 0.0 := by
    rw [F64UpperWord.float_lt_iff _ _ hv zero_finite, zero_value, hK]
    exact not_lt.mpr (Nat.cast_nonneg K)
  rw [ite_eq_right hnlt]
  exact toUInt64_nat v K hv hK hK63

#print axioms exp_mulc
#print axioms exp_red
#print axioms exp_index

end Library.Numerics.Float64.Tgamma.TgammaExpRed
