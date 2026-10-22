import Library.Numerics.Float64.Pow.PowTheoremPos
import Library.Numerics.Float64.Pow.PowExpSign

/-!
`Pow.powMain` with the sign bias against `powMain` without it, on the normalized word of a
positive finite `x` and a finite `y` with `2 ^ -65 ≤ |y| < 2 ^ 63`.  Both run `powExp` on the
same `ehi` and `elo`, which meet the conditions of `PowExpSign.powExp_rel` when `x ≠ 1`; for
`x = 1`, `ehi` is a zero and both take the branch `±(1 + ehi)`.
-/

namespace Library.Numerics.Float64.Pow.PowMainSign
open CodeLib.IEEE64 LeanExe.ProofKit PowSignRel

set_option exponentiation.threshold 4096

theorem main_rel (ix : UInt64) (E : Int) (f : Nat) (hE1 : -51 ≤ E) (hE2 : E ≤ 2046)
    (hf : f < 4503599627370496)
    (hix : (ix.toNat : Int) = (E * 4503599627370496 + f) % 18446744073709551616)
    (hX1 : ¬ (E = 1023 ∧ f = 0)) (y : Float) (hyf : Finite y.toBits)
    (hy1 : 1 / 2 ^ 65 ≤ |value y.toBits|) (hy2 : |value y.toBits| < 2 ^ 63) :
    Rel (Pow.powMain Pow.powLogTable Exp.expTable ix y y.toBits PowExpSign.bias).toBits
      (Pow.powMain Pow.powLogTable Exp.expTable ix y y.toBits 0).toBits := by
  obtain ⟨h1f, h2f, hlog, htail⟩ := PowLogFinal.log_within ix E f hE1 hE2 hf hix hX1
  obtain ⟨hL1, hL2⟩ := PowMainPath.log_bounds E f hE1 hE2 (by simpa using hf) hX1
  simp only [Pow.powMain]
  generalize hP : Pow.powLog Pow.powLogTable ix = P at h1f h2f hlog htail ⊢
  obtain ⟨hiF, loF⟩ := P
  simp only at h1f h2f hlog htail ⊢
  set Y := value hiF.toBits
  set T := value loF.toBits
  set lX := Real.log (((2 ^ 52 + f : Nat) : ℝ) * (2 : ℝ) ^ (E - 1075))
  have hY1 : 1 / 2 ^ 54 ≤ |Y| := by
    have h1 := abs_sub_abs_le_abs_sub lX (Y + T)
    rw [abs_sub_comm] at h1
    have h2 := abs_add_le Y T
    have h3 : 7 / 8 / 2 ^ 65 * |lX| ≤ |lX| / 4 := by linarith [abs_nonneg lX]
    linarith [abs_nonneg Y]
  have hY2 : |Y| ≤ 800 := by
    have h1 := abs_sub_abs_le_abs_sub (Y + T) lX
    have h2 := abs_sub_abs_le_abs_sub Y (-T)
    rw [sub_neg_eq_add, abs_neg] at h2
    have h3 : 7 / 8 / 2 ^ 65 * |lX| ≤ 745 := by linarith [abs_nonneg lX]
    linarith [abs_nonneg Y]
  obtain ⟨hef, helf, -, helo⟩ := PowProduct.product_error y hiF loF hyf h1f h2f hy1 hy2
    hY1 hY2 htail
  exact PowExpSign.powExp_rel _ _ hef helf helo

theorem main_rel_one (y : Float) (hyf : Wasm.IEEE64.exponent y.toBits < 2047)
    (hey : 1 ≤ Wasm.IEEE64.exponent y.toBits) :
    Rel (Pow.powMain Pow.powLogTable Exp.expTable 0x3FF0000000000000 y y.toBits
        PowExpSign.bias).toBits
      (Pow.powMain Pow.powLogTable Exp.expTable 0x3FF0000000000000 y y.toBits 0).toBits := by
  obtain ⟨h1, -⟩ := PowMainPath.log_one
  simp only [Pow.powMain]
  generalize hP : Pow.powLog Pow.powLogTable 0x3FF0000000000000 = P at h1
  obtain ⟨a, b⟩ := P
  simp only at h1 ⊢
  have hyf' : Finite y.toBits := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq]
    omega
  obtain ⟨hmf, -, -, -, -⟩ := PowProduct.mask_state y.toBits hyf' hey
  set ehi := Float.ofBits (y.toBits &&& 0xFFFFFFFFF8000000) *
    Float.ofBits (a.toBits &&& 0xFFFFFFFFF8000000)
  have hehi : ehi.toBits = 0 ∨ ehi.toBits = 0x8000000000000000 := by
    have hz : (Float.ofBits (a.toBits &&& 0xFFFFFFFFF8000000)).toBits = 0 := by
      rw [h1, F64Bits.toBits_ofBits]
      decide
    have hm : (Float.ofBits (y.toBits &&& 0xFFFFFFFFF8000000)).toBits = PowProduct.mask y.toBits :=
      PowExpPaths.ofBits_finite _ hmf
    simp only [ehi, F64Bits.toBits_mul, hz, hm]
    simp only [Wasm.IEEE64.mul, not_nan_of_finite hmf, not_infinite_of_finite hmf,
      show Wasm.IEEE64.isNaN 0 = false by decide, show Wasm.IEEE64.isInfinite 0 = false by decide,
      show Wasm.IEEE64.scaledMagnitude 0 = 0 by decide, Bool.or_false, Bool.false_eq_true,
      ite_false, beq_self_eq_true, Bool.or_true, ite_true]
    cases Wasm.IEEE64.sign (PowProduct.mask y.toBits) <;> decide
  have hexp : Wasm.IEEE64.exponent ehi.toBits < 969 := by
    rcases hehi with h | h <;> rw [h] <;> decide
  rw [PowExpSign.tiny_sel _ ehi _ _ hexp, PowExpSign.tiny_sel _ ehi _ _ hexp,
    ite_eq_left PowExpSign.bias_ne, ite_eq_right PowExpSign.zero_bias]
  exact fneg _

/-- The word that `Pow.powWith` passes to `powMain` for a positive finite nonzero `x`. -/
def normWord (x : Float) : UInt64 :=
  if x.toBits >>> 52 == 0 then
    ((x * Float.ofBits 0x4330000000000000).toBits &&& (0x7fffffffffffffff : UInt64)) -
      ((52 : UInt64) <<< 52)
  else x.toBits

/-- `powMain` with and without the bias on the normalized word of a positive finite `x`. -/
theorem main_rel_any (x y : Float) (hxf : Finite x.toBits) (hx : 0 < value x.toBits)
    (hyf : Finite y.toBits) (hy1 : 1 / 2 ^ 65 ≤ |value y.toBits|)
    (hy2 : |value y.toBits| < 2 ^ 63) :
    Rel (Pow.powMain Pow.powLogTable Exp.expTable (normWord x) y y.toBits
        PowExpSign.bias).toBits
      (Pow.powMain Pow.powLogTable Exp.expTable (normWord x) y y.toBits 0).toBits := by
  have hs := PowExpPaths.sign_of_pos _ hx
  have hT : x.toBits.toNat < 2 ^ 63 := by
    simpa only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] using hs
  have hxexp : Wasm.IEEE64.exponent x.toBits < 2047 := by
    have h := hxf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hx0 : x.toBits ≠ 0 := by
    intro h
    rw [h, F64Magnitude.value_zero] at hx
    exact lt_irrefl _ hx
  have hyexp : Wasm.IEEE64.exponent y.toBits < 2047 := by
    have h := hyf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent y.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  have hey1 : 958 ≤ Wasm.IEEE64.exponent y.toBits := PowProduct.exponent_of_abs _ 958
    (by norm_num) (by norm_num at hy1 ⊢; exact hy1)
  have ht := PowBranches.top_word x.toBits hT
  by_cases hxe : 1 ≤ Wasm.IEEE64.exponent x.toBits
  · have htop : (x.toBits >>> 52 == 0) = false := by
      apply beq_eq_false_iff_ne.mpr
      intro h
      rw [h] at ht
      change 0 = _ at ht
      omega
    simp only [normWord, htop, Bool.false_eq_true, ite_false]
    by_cases hx1 : x.toBits = 0x3FF0000000000000
    · rw [hx1]
      exact main_rel_one y hyexp (by omega)
    · have hix : (x.toBits.toNat : Int) =
          ((Wasm.IEEE64.exponent x.toBits : Int) * 4503599627370496 +
            Wasm.IEEE64.fraction x.toBits) % 18446744073709551616 := by
        simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction]
        simp only [Nat.reducePow] at hT ⊢
        omega
      have hne : ¬ ((Wasm.IEEE64.exponent x.toBits : Int) = 1023 ∧
          Wasm.IEEE64.fraction x.toBits = 0) := by
        rintro ⟨h1, h2⟩
        apply hx1
        apply UInt64.toNat_inj.mp
        have h1' : Wasm.IEEE64.exponent x.toBits = 1023 := by exact_mod_cast h1
        simp only [Wasm.IEEE64.exponent, Wasm.IEEE64.fraction] at h1' h2
        simp only [Nat.reducePow] at hT h1' h2 ⊢
        change _ = 4607182418800017408
        omega
      exact main_rel x.toBits _ _ (by omega) (by omega) (Nat.mod_lt _ (by norm_num)) hix hne y
        hyf hy1 hy2
  · have he0 : Wasm.IEEE64.exponent x.toBits = 0 := by omega
    have hs52 : x.toBits.toNat < 2 ^ 52 := by
      have : x.toBits.toNat / 2 ^ 52 % 2 ^ 11 = 0 := he0
      simp only [Nat.reducePow] at hT this ⊢
      omega
    have h0 : 0 < x.toBits.toNat := by
      by_contra hn
      exact hx0 (UInt64.toNat_inj.mp (by simp; omega))
    have htop0 : (x.toBits >>> 52 == 0) = true := by
      rw [he0] at ht
      simp only [beq_iff_eq]
      exact UInt64.toNat_inj.mp (by rw [ht]; rfl)
    simp only [normWord, htop0, ite_true]
    obtain ⟨E', f', hE1', hE2', hf', hix', -⟩ := PowSubnormal.subnormal_word x hs52 h0
    exact main_rel _ E' f' hE1' (by omega) (by simpa using hf') (by simpa using hix')
      (by omega) y hyf hy1 hy2

#print axioms main_rel
#print axioms main_rel_one
#print axioms main_rel_any

end Library.Numerics.Float64.Pow.PowMainSign
