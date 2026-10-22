import Library.Numerics.Float64.Trig.TrigMedium
import Library.Numerics.Float64.Trig.TrigLargeSpec

/-!
The accuracy of `Trig.remPio2`, fdlibm's argument reduction, for a positive double `x` above
`π/4`: the count `n` and the pair `y0 + y1` satisfy `Reduced`.  The one-step branches leave
`|x - n π/2|` up to `π/4 + 4.8 · 10 ^ -6`, which `π/4 + 2 ^ -17` bounds.
-/

namespace Library.Numerics.Float64.Trig.TrigReduce

open CodeLib.IEEE64 LeanExe.ProofKit TrigSmall TrigMedium

/-- `y0 + y1` approximates `r = x - N π/2` for some `N` congruent to `n` modulo 4, within
`|r| / 2 ^ 60`, with `|y1| ≤ |y0| / 2 ^ 52` and `2 ^ -63 ≤ |r| ≤ π/4 + 2 ^ -17`. -/
def Reduced (x n y0 y1 : UInt64) : Prop :=
  ∃ N : Int, (n.toNat : Int) % 4 = N % 4 ∧ CodeLib.IEEE64.Finite y0 ∧
    CodeLib.IEEE64.Finite y1 ∧
    |value y0 + value y1 - (value x - N * (Real.pi / 2))| ≤
      |value x - N * (Real.pi / 2)| / 2 ^ 60 ∧
    |value y1| ≤ |value y0| / 2 ^ 52 ∧
    1 / 2 ^ 63 ≤ |value x - N * (Real.pi / 2)| ∧
    |value x - N * (Real.pi / 2)| ≤ Real.pi / 4 + 1 / 2 ^ 17

theorem value_word (w : UInt64) (m k : Nat) (hk : k ≤ 1074)
    (h : Wasm.IEEE64.scaledValue w = (m : Int) * 2 ^ (1074 - k)) :
    value w = (m : ℝ) / 2 ^ k := by
  rw [TrigSmall.value_of_scaled, h]
  push_cast
  rw [show (2 : ℝ) ^ 1074 = 2 ^ (1074 - k) * 2 ^ k by rw [← pow_add, Nat.sub_add_cancel hk]]
  field_simp

/-- Bounds on `x` from bounds on its word, for a one-step branch. -/
theorem small_range (X A B E1 E2 : UInt64) (K : Nat) (a b e1 e2 : ℝ)
    (hs : X.toNat < 2 ^ 63) (hB63 : B.toNat < 2 ^ 63) (hE163 : E1.toNat < 2 ^ 63)
    (hE263 : E2.toNat < 2 ^ 63)
    (hA : A.toNat ≤ X.toNat) (hB : X.toNat < B.toNat)
    (hE : X.toNat < E1.toNat ∨ E2.toNat ≤ X.toNat)
    (ha : value A = a) (hb : value B = b) (he1 : value E1 = e1) (he2 : value E2 = e2)
    (h1 : 1 / 2 ≤ a) (h2 : -(Real.pi / 4 + 1 / 2 ^ 17) ≤ a - K * (Real.pi / 2))
    (h3 : b - K * (Real.pi / 2) ≤ Real.pi / 4 + 1 / 2 ^ 17)
    (h4 : 1 / 2 ^ 22 ≤ K * (Real.pi / 2) - e1) (h5 : 1 / 2 ^ 22 ≤ e2 - K * (Real.pi / 2)) :
    1 / 2 ≤ |value X| ∧ 1 / 2 ^ 22 ≤ |value X - K * (Real.pi / 2)| ∧
      |value X - K * (Real.pi / 2)| ≤ Real.pi / 4 + 1 / 2 ^ 17 := by
  have hxa : a ≤ value X := by
    rw [← ha]
    exact (F64PositiveOrder.value_le_iff (by omega) hs).mpr hA
  have hxb : value X < b := by
    rw [← hb]
    exact F64PositiveOrder.value_strict hB63 hB
  have h0 : 0 ≤ value X := by linarith
  refine ⟨by rw [abs_of_nonneg h0]; linarith, ?_, ?_⟩
  · rcases hE with h | h
    · have hx : value X < e1 := by
        rw [← he1]
        exact F64PositiveOrder.value_strict hE163 h
      rw [abs_of_neg (by linarith)]
      linarith
    · have hx : e2 ≤ value X := by
        rw [← he2]
        exact (F64PositiveOrder.value_le_iff hE263 hs).mpr h
      rw [abs_of_pos (by linarith)]
      linarith
  · rw [abs_le]
    constructor <;> linarith

theorem range1 (X : UInt64) (hs : X.toNat < 2 ^ 63) (hA : 0x3FE921FC00000000 ≤ X.toNat)
    (hB : X.toNat < 0x4002D97D00000000)
    (hE : X.toNat < 0x3FF921FB00000000 ∨ 0x3FF921FC00000000 ≤ X.toNat) :
    1 / 2 ≤ |value X| ∧ 1 / 2 ^ 22 ≤ |value X - (1 : Nat) * (Real.pi / 2)| ∧
      |value X - (1 : Nat) * (Real.pi / 2)| ≤ Real.pi / 4 + 1 / 2 ^ 17 := by
  have hpl : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hpu : Real.pi < 3.14159265358979323847 := Real.pi_lt_d20
  exact small_range X 0x3FE921FC00000000 0x4002D97D00000000 0x3FF921FB00000000
    0x3FF921FC00000000 1 (1647100 / 2 ^ 21) (1235325 / 2 ^ 19) (1647099 / 2 ^ 20)
    (1647100 / 2 ^ 20) hs (by decide) (by decide) (by decide) hA hB hE
    (by exact_mod_cast value_word _ 1647100 21 (by norm_num) (by decide +kernel))
    (by exact_mod_cast value_word _ 1235325 19 (by norm_num) (by decide +kernel))
    (by exact_mod_cast value_word _ 1647099 20 (by norm_num) (by decide +kernel))
    (by exact_mod_cast value_word _ 1647100 20 (by norm_num) (by decide +kernel))
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith)

theorem range2 (X : UInt64) (hs : X.toNat < 2 ^ 63) (hA : 0x4002D97D00000000 ≤ X.toNat)
    (hB : X.toNat < 0x400F6A7B00000000)
    (hE : X.toNat < 0x400921FB00000000 ∨ 0x400921FC00000000 ≤ X.toNat) :
    1 / 2 ≤ |value X| ∧ 1 / 2 ^ 22 ≤ |value X - (2 : Nat) * (Real.pi / 2)| ∧
      |value X - (2 : Nat) * (Real.pi / 2)| ≤ Real.pi / 4 + 1 / 2 ^ 17 := by
  have hpl : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hpu : Real.pi < 3.14159265358979323847 := Real.pi_lt_d20
  exact small_range X 0x4002D97D00000000 0x400F6A7B00000000 0x400921FB00000000
    0x400921FC00000000 2 (1235325 / 2 ^ 19) (2058875 / 2 ^ 19) (1647099 / 2 ^ 19)
    (1647100 / 2 ^ 19) hs (by decide) (by decide) (by decide) hA hB hE
    (by exact_mod_cast value_word _ 1235325 19 (by norm_num) (by decide +kernel))
    (by exact_mod_cast value_word _ 2058875 19 (by norm_num) (by decide +kernel))
    (by exact_mod_cast value_word _ 1647099 19 (by norm_num) (by decide +kernel))
    (by exact_mod_cast value_word _ 1647100 19 (by norm_num) (by decide +kernel))
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith)

theorem range3 (X : UInt64) (hs : X.toNat < 2 ^ 63) (hA : 0x400F6A7B00000000 ≤ X.toNat)
    (hB : X.toNat < 0x4015FDBD00000000)
    (hE : X.toNat < 0x4012D97C00000000 ∨ 0x4012D97D00000000 ≤ X.toNat) :
    1 / 2 ≤ |value X| ∧ 1 / 2 ^ 22 ≤ |value X - (3 : Nat) * (Real.pi / 2)| ∧
      |value X - (3 : Nat) * (Real.pi / 2)| ≤ Real.pi / 4 + 1 / 2 ^ 17 := by
  have hpl : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hpu : Real.pi < 3.14159265358979323847 := Real.pi_lt_d20
  exact small_range X 0x400F6A7B00000000 0x4015FDBD00000000 0x4012D97C00000000
    0x4012D97D00000000 3 (2058875 / 2 ^ 19) (1441213 / 2 ^ 18) (1235324 / 2 ^ 18)
    (1235325 / 2 ^ 18) hs (by decide) (by decide) (by decide) hA hB hE
    (by exact_mod_cast value_word _ 2058875 19 (by norm_num) (by decide +kernel))
    (by exact_mod_cast value_word _ 1441213 18 (by norm_num) (by decide +kernel))
    (by exact_mod_cast value_word _ 1235324 18 (by norm_num) (by decide +kernel))
    (by exact_mod_cast value_word _ 1235325 18 (by norm_num) (by decide +kernel))
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith)

theorem range4 (X : UInt64) (hs : X.toNat < 2 ^ 63) (hA : 0x4015FDBD00000000 ≤ X.toNat)
    (hB : X.toNat < 0x401C463C00000000)
    (hE : X.toNat < 0x401921FB00000000 ∨ 0x401921FC00000000 ≤ X.toNat) :
    1 / 2 ≤ |value X| ∧ 1 / 2 ^ 22 ≤ |value X - (4 : Nat) * (Real.pi / 2)| ∧
      |value X - (4 : Nat) * (Real.pi / 2)| ≤ Real.pi / 4 + 1 / 2 ^ 17 := by
  have hpl : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hpu : Real.pi < 3.14159265358979323847 := Real.pi_lt_d20
  exact small_range X 0x4015FDBD00000000 0x401C463C00000000 0x401921FB00000000
    0x401921FC00000000 4 (1441213 / 2 ^ 18) (1852988 / 2 ^ 18) (1647099 / 2 ^ 18)
    (1647100 / 2 ^ 18) hs (by decide) (by decide) (by decide) hA hB hE
    (by exact_mod_cast value_word _ 1441213 18 (by norm_num) (by decide +kernel))
    (by exact_mod_cast value_word _ 1852988 18 (by norm_num) (by decide +kernel))
    (by exact_mod_cast value_word _ 1647099 18 (by norm_num) (by decide +kernel))
    (by exact_mod_cast value_word _ 1647100 18 (by norm_num) (by decide +kernel))
    (by norm_num) (by norm_num; linarith) (by norm_num; linarith) (by norm_num; linarith)
    (by norm_num; linarith)

theorem small_branch (x k : Float) (n : UInt64) (K : Nat) (kb C W : UInt64)
    (hc : SmallConst K kb C W) (hk : k.toBits = kb) (hn : n.toNat = K) (hK1 : 1 ≤ K)
    (hK4 : K ≤ 4) (hxf : CodeLib.IEEE64.Finite x.toBits) (hx : 1 / 2 ≤ |value x.toBits|)
    (hr1 : 1 / 2 ^ 22 ≤ |value x.toBits - K * (Real.pi / 2)|)
    (hr2 : |value x.toBits - K * (Real.pi / 2)| ≤ Real.pi / 4 + 1 / 2 ^ 17) :
    Reduced x.toBits n (Trig.remSmall x k).1.toBits (Trig.remSmall x k).2.toBits := by
  obtain ⟨b1, b2⟩ := remSmall_bits x k
  rw [b1, b2, hk]
  obtain ⟨f1, f2, e1, e2⟩ := remSmallW_spec x.toBits kb C W K hc hK1 hK4 hxf hx hr1 hr2
  have h63 : (1 : ℝ) / 2 ^ 63 ≤ 1 / 2 ^ 22 := by norm_num
  refine ⟨K, by rw [hn], f1, f2, ?_, e2, ?_, ?_⟩ <;> rw [Int.cast_natCast]
  · exact e1
  · linarith
  · exact hr2

theorem medium_branch (x : Float) (hs : x.toBits.toNat < 2 ^ 63)
    (hlo : 0x3FF0000000000000 ≤ x.toBits.toNat) (hhi : x.toBits.toNat < 0x413921FB00000000) :
    Reduced x.toBits (Trig.remMedium x (x.toBits >>> 32)).1
      (Trig.remMedium x (x.toBits >>> 32)).2.1.toBits
      (Trig.remMedium x (x.toBits >>> 32)).2.2.toBits := by
  obtain ⟨N, hN, f1, f2, e1, e2, hrl, hru⟩ := remMedium_spec x hs hlo hhi
  have h28 : (1 : ℝ) / 2 ^ 28 ≤ 1 / 2 ^ 17 := by norm_num
  refine ⟨N, by rw [hN], f1, f2, ?_, e2, ?_, ?_⟩ <;> rw [Int.cast_natCast]
  · exact e1
  · exact hrl
  · linarith

theorem large_branch (x : Float) (hs : x.toBits.toNat < 2 ^ 63)
    (hE1 : 1043 ≤ x.toBits.toNat / 2 ^ 52 % 2 ^ 11)
    (hE2 : x.toBits.toNat / 2 ^ 52 % 2 ^ 11 < 2047) :
    Reduced x.toBits (Trig.remLarge Trig.invPi Trig.halfPi x).1
      (Trig.remLarge Trig.invPi Trig.halfPi x).2.1.toBits
      (Trig.remLarge Trig.invPi Trig.halfPi x).2.2.toBits := by
  obtain ⟨N, hN, f1, f2, e1, hrl, hru, e2⟩ := TrigLargeSpec.remLarge_spec x hs hE1 hE2
  have h134 : (1 : ℝ) / 2 ^ 134 ≤ 1 / 2 ^ 17 := by norm_num
  refine ⟨N, hN, f1, f2, ?_, ?_, hrl, by linarith⟩
  · exact e1.trans (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by norm_num))
  · exact e2.trans (div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (by norm_num))

theorem high_and (w : UInt64) :
    ((w >>> 32) &&& 0xfffff).toNat = w.toNat / 2 ^ 32 % 2 ^ 20 := by
  rw [UInt64.toNat_and, TrigWords.shr_toNat]
  have h1 : (0xfffff : UInt64).toNat = 2 ^ 20 - 1 := rfl
  have h2 : (32 : UInt64).toNat % 64 = 32 := rfl
  rw [h1, h2, Nat.and_two_pow_sub_one_eq_mod]

theorem high_word (w : UInt64) : (w >>> 32).toNat = w.toNat / 2 ^ 32 := by
  rw [TrigWords.shr_toNat]
  rfl

theorem one_bits : (1.0 : Float).toBits = 0x3FF0000000000000 ∧
    (2.0 : Float).toBits = 0x4000000000000000 ∧ (3.0 : Float).toBits = 0x4008000000000000 ∧
    (4.0 : Float).toBits = 0x4010000000000000 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The accuracy of `remPio2` on a positive finite double above `π/4`. -/
theorem remPio2_spec (x : Float) (hs : x.toBits.toNat < 2 ^ 63)
    (hlo : 0x3FE921FC00000000 ≤ x.toBits.toNat) (hhi : x.toBits.toNat < 0x7FF0000000000000) :
    Reduced x.toBits (Trig.remPio2 Trig.invPi Trig.halfPi x).1
      (Trig.remPio2 Trig.invPi Trig.halfPi x).2.1.toBits
      (Trig.remPio2 Trig.invPi Trig.halfPi x).2.2.toBits := by
  have hxf : CodeLib.IEEE64.Finite x.toBits := by
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite Wasm.IEEE64.exponent
    simp only [bne_iff_ne, ne_eq]
    omega
  obtain ⟨k1, k2, k3, k4⟩ := one_bits
  unfold Trig.remPio2
  dsimp only
  simp only [UInt64.le_iff_toNat_le, UInt64.lt_iff_toNat_lt, beq_iff_eq, ← UInt64.toNat_inj,
    high_and, high_word, UInt64.reduceToNat]
  split_ifs with c1 c2 c3 c4 c5 c6 c7 c8
  · exact medium_branch x hs (by omega) (by omega)
  · obtain ⟨h1, h2, h3⟩ := range1 x.toBits hs hlo (by omega) (by omega)
    exact small_branch x 1.0 1 1 _ _ _ const1 k1 rfl (by norm_num) (by norm_num) hxf h1 h2 h3
  · obtain ⟨h1, h2, h3⟩ := range2 x.toBits hs (by omega) (by omega) (by omega)
    exact small_branch x 2.0 2 2 _ _ _ const2 k2 rfl (by norm_num) (by norm_num) hxf h1 h2 h3
  · exact medium_branch x hs (by omega) (by omega)
  · obtain ⟨h1, h2, h3⟩ := range3 x.toBits hs (by omega) (by omega) (by omega)
    exact small_branch x 3.0 3 3 _ _ _ const3 k3 rfl (by norm_num) (by norm_num) hxf h1 h2 h3
  · exact medium_branch x hs (by omega) (by omega)
  · obtain ⟨h1, h2, h3⟩ := range4 x.toBits hs (by omega) (by omega) (by omega)
    exact small_branch x 4.0 4 4 _ _ _ const4 k4 rfl (by norm_num) (by norm_num) hxf h1 h2 h3
  · exact medium_branch x hs (by omega) (by omega)
  · exact large_branch x hs (by omega) (by omega)

#print axioms value_word
#print axioms small_range
#print axioms range1
#print axioms range2
#print axioms range3
#print axioms range4
#print axioms small_branch
#print axioms medium_branch
#print axioms large_branch
#print axioms remPio2_spec

end Library.Numerics.Float64.Trig.TrigReduce
