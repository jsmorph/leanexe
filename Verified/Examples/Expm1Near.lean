import Verified.Examples.Expm1Theorem
import Verified.Examples.Expm1NearForms

/-!
`Tanh.expm1` with the error before its last rounding, for the arguments that `tanh` passes.  For
`x < 0` the result is `-w` for a word `w` within `u S` and `u/2` of a positive `S`; `S` lies
within `0.56 u abs(x) + 16 η` of `1 - exp x` on the path without reduction (`abs(x)` below the
threshold `θ1 ≈ 0.3466`), within `0.2451 u` for `k = -1` (`abs(x)` from `θ1` to
`θ2 ≈ 1.0397`), and within `0.3726 u` from `θ2` to 38.  For `2 ≤ x ≤ 44` the result is within
`u S` of a positive `S`, and `S` within `0.85 u (exp x - 1)` of `exp x - 1`.
-/

namespace Verified.Examples.Expm1Near
open CodeLib.IEEE64 LeanExe.ProofKit Expm1Branches Expm1ReduceConst Expm1PathsReduced
  Expm1Theorem Expm1NearForms

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

theorem high_of_ge (w : UInt64) (C : Nat) (hC : C < 0x7ff00000)
    (h : value (UInt64.ofNat (C * 2 ^ 32)) ≤ |value w|) : C ≤ (highWord w).toNat := by
  have := UInt64.le_iff_toNat_le.mp ((high_le_iff w C hC).mpr h)
  rwa [UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)] at this

theorem high_of_lt (w : UInt64) (C : Nat) (hC : C < 0x7ff00000)
    (h : |value w| < value (UInt64.ofNat (C * 2 ^ 32))) : (highWord w).toNat < C := by
  by_contra hc
  have h' := high_ge w C hC (by omega)
  linarith

theorem tiny_threshold : value (UInt64.ofNat (1016070144 * 2 ^ 32)) = 1 / 2 ^ 54 := by
  have a := word_le (1 / 2 ^ 54) (UInt64.ofNat (1016070144 * 2 ^ 32)) (by decide +kernel)
  have b := word_ge (1 / 2 ^ 54) (UInt64.ofNat (1016070144 * 2 ^ 32)) (by decide +kernel)
  push_cast at a b
  exact le_antisymm a b

/-- The thresholds `θ1` and `θ2` as numbers. -/
theorem threshold_bounds :
    34657359 / 10 ^ 8 ≤ value (UInt64.ofNat (1071001155 * 2 ^ 32)) ∧
      value (UInt64.ofNat (1071001155 * 2 ^ 32)) ≤ 3466 / 10000 ∧
      10397205 / 10 ^ 7 ≤ value (UInt64.ofNat (1072734898 * 2 ^ 32)) ∧
      value (UInt64.ofNat (1072734898 * 2 ^ 32)) ≤ 10397206 / 10 ^ 7 ∧
      3881 / 100 ≤ value (UInt64.ofNat (1078159482 * 2 ^ 32)) := by
  have h1 := word_ge (34657359 / 10 ^ 8) (UInt64.ofNat (1071001155 * 2 ^ 32)) (by decide +kernel)
  have h2 := word_le (3466 / 10000) (UInt64.ofNat (1071001155 * 2 ^ 32)) (by decide +kernel)
  have h3 := word_ge (10397205 / 10 ^ 7) (UInt64.ofNat (1072734898 * 2 ^ 32)) (by decide +kernel)
  have h4 := word_le (10397206 / 10 ^ 7) (UInt64.ofNat (1072734898 * 2 ^ 32)) (by decide +kernel)
  have h5 := word_ge (3881 / 100) (UInt64.ofNat (1078159482 * 2 ^ 32)) (by decide +kernel)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact le_of_eq_of_le (by push_cast; ring) h1
  · exact le_of_le_of_eq h2 (by push_cast; ring)
  · exact le_of_eq_of_le (by push_cast; ring) h3
  · exact le_of_le_of_eq h4 (by push_cast; ring)
  · exact le_of_eq_of_le (by push_cast; ring) h5

/-- `neg_one_near` for a count word `m` with `m.toNat = 1`. -/
theorem neg_one_near_m (y c m : UInt64) (hm : m.toNat = 1) (hyf : Finite y) (hcf : Finite c)
    (hy : |value y| ≤ 3466 / 10000) (hc : |value c| ≤ 36 / 100 * u) (r : ℝ)
    (hr : |value y + value c - r| ≤ 1 / 2 ^ 70) :
    ∃ w : UInt64, ∃ S : ℝ, Expm1Words.kernel y c true m = Wasm.IEEE64.negate w ∧ Finite w ∧
      |value w - S| ≤ u * S ∧ |value w - S| ≤ u / 2 ∧
      |S - (1 - Real.exp r / 2)| ≤ 2451 / 10000 * u := by
  rw [word_one m hm]
  exact neg_one_near y c hyf hcf hy hc r hr

/-- The negative path without reduction. -/
theorem near_middle (x : Float) (hxf : Finite x.toBits) (hneg : value x.toBits < 0)
    (hlo : 1 / 2 ^ 54 ≤ -value x.toBits)
    (hhi : -value x.toBits < value (UInt64.ofNat (1071001155 * 2 ^ 32))) :
    ∃ w : UInt64, ∃ S : ℝ, (Tanh.expm1 x).toBits = Wasm.IEEE64.negate w ∧ Finite w ∧
      |value w - S| ≤ u * S ∧ |value w - S| ≤ u / 2 ∧
      |S - (1 - Real.exp (value x.toBits))| ≤ 56 / 100 * u * (-value x.toBits) + 16 * η := by
  obtain ⟨-, hθ1, -, -, -⟩ := threshold_bounds
  set θ1 := value (UInt64.ofNat (1071001155 * 2 ^ 32))
  have habs : |value x.toBits| = -value x.toBits := abs_of_neg hneg
  have h1 := high_finite x.toBits hxf
  have hn4 := high_of_lt x.toBits 1071001155 (by norm_num) (by rw [habs]; exact hhi)
  have hn5 := high_of_ge x.toBits 1016070144 (by norm_num) (by rw [habs, tiny_threshold]; exact hlo)
  have h2 : ¬ (highWord x.toBits ≥ 1082535490 ∧ x > Float.ofBits 4649454530587146735) := by
    intro h
    have := UInt64.le_iff_toNat_le.mp h.1
    change 1082535490 ≤ _ at this
    omega
  have h3 : ¬ (highWord x.toBits ≥ 1078159482 ∧ sgn x.toBits = true ∧
      x + Float.ofBits 118622047889322841 < 0.0) := by
    intro h
    have := UInt64.le_iff_toNat_le.mp h.1
    change 1078159482 ≤ _ at this
    omega
  have h4 : ¬ highWord x.toBits > 1071001154 := by
    intro h
    have := UInt64.lt_iff_toNat_lt.mp h
    change 1071001154 < _ at this
    omega
  have h5 : ¬ highWord x.toBits < 1016070144 := by
    intro h
    have := UInt64.lt_iff_toNat_lt.mp h
    change _ < 1016070144 at this
    omega
  rw [select_middle x h1 h2 h3 h4 h5, Expm1Words.kernel_bits]
  have hk : Expm1Words.kernel x.toBits (0.0 : Float).toBits false 0 = Wasm.IEEE64.sub x.toBits
      (Wasm.IEEE64.sub (Wasm.IEEE64.mul x.toBits (Expm1Words.e0 x.toBits))
        (Expm1Words.hxs x.toBits)) := by
    simp [Expm1Words.kernel]
  rw [hk]
  obtain ⟨hwf, hw⟩ := Expm1KernelOuter.m0_spec x.toBits hxf (by rw [habs]; linarith)
  set W := Wasm.IEEE64.sub (Wasm.IEEE64.mul x.toBits (Expm1Words.e0 x.toBits))
    (Expm1Words.hxs x.toBits)
  rw [habs] at hw
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have hη : 16 * η ≤ 1 / 10 ^ 10 := by rw [Expm1KernelInner.eta_value]; norm_num
  have h2' := Expm1KernelOuter.exp_second (value x.toBits) (by rw [habs]; linarith)
  have hb := abs_le.mp h2'
  have hwb := abs_le.mp hw
  have hsq : value x.toBits ^ 2 ≤ 3466 / 10000 * -value x.toBits := by
    rw [← sq_abs, habs, sq]
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hux : u * -value x.toBits ≤ 1 / 2 ^ 53 * (3466 / 10000) := by
    rw [hu]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hux' : 56 / 100 * u * -value x.toBits = 56 / 100 * (1 / 2 ^ 53) * -value x.toBits := by
    rw [hu]
  have hη' : 16 * η ≤ 1 / 2 ^ 60 := by rw [Expm1KernelInner.eta_value]; norm_num
  have h54 : (1 : ℝ) / 2 ^ 60 ≤ 1 / 2 ^ 54 := by norm_num
  obtain ⟨heq, hcf, hc1, hc2⟩ := final_neg x.toBits W hxf hwf (by linarith) (by linarith)
  refine ⟨_, value W - value x.toBits, heq, hcf, hc1, hc2, ?_⟩
  rw [show value W - value x.toBits - (1 - Real.exp (value x.toBits)) =
    -((value x.toBits - value W) - (Real.exp (value x.toBits) - 1)) by ring, abs_neg]
  exact hw

/-- The path for `k = -1`, from the reduction with `ln2Hi` and `ln2Lo`. -/
theorem near_one (x : Float) (hxf : Finite x.toBits) (hneg : value x.toBits < 0)
    (hlo : value (UInt64.ofNat (1071001155 * 2 ^ 32)) ≤ -value x.toBits)
    (hhi : -value x.toBits < value (UInt64.ofNat (1072734898 * 2 ^ 32))) :
    ∃ w : UInt64, ∃ S : ℝ, (Tanh.expm1 x).toBits = Wasm.IEEE64.negate w ∧ Finite w ∧
      |value w - S| ≤ u * S ∧ |value w - S| ≤ u / 2 ∧
      |S - (1 - Real.exp (value x.toBits))| ≤ 2451 / 10000 * u := by
  obtain ⟨hθ1, -, -, hθ2, -⟩ := threshold_bounds
  set θ1 := value (UInt64.ofNat (1071001155 * 2 ^ 32))
  set θ2 := value (UInt64.ofNat (1072734898 * 2 ^ 32))
  have habs : |value x.toBits| = -value x.toBits := abs_of_neg hneg
  have h1 := high_finite x.toBits hxf
  have hn4 := high_of_ge x.toBits 1071001155 (by norm_num) (by rw [habs]; exact hlo)
  have hn5 := high_of_lt x.toBits 1072734898 (by norm_num) (by rw [habs]; exact hhi)
  have h2 : ¬ (highWord x.toBits ≥ 1082535490 ∧ x > Float.ofBits 4649454530587146735) := by
    intro h
    have := UInt64.le_iff_toNat_le.mp h.1
    change 1082535490 ≤ _ at this
    omega
  have h3 : ¬ (highWord x.toBits ≥ 1078159482 ∧ sgn x.toBits = true ∧
      x + Float.ofBits 118622047889322841 < 0.0) := by
    intro h
    have := UInt64.le_iff_toNat_le.mp h.1
    change 1078159482 ≤ _ at this
    omega
  have h4 : highWord x.toBits > 1071001154 := UInt64.lt_iff_toNat_lt.mpr (by
    change 1071001154 < _; omega)
  have h5 : highWord x.toBits < 1072734898 := UInt64.lt_iff_toNat_lt.mpr (by
    change _ < 1072734898; omega)
  have hs : sgn x.toBits = true := by
    rw [sgn_iff]
    exact (F64Magnitude.sign_value x.toBits (magnitude_pos x.toBits (by
      rw [habs]; linarith))).mpr hneg
  rw [select_reduced_one x h1 h2 h3 h4 h5, hs]
  simp only [ite_true]
  rw [Expm1Words.kernel_bits]
  simp only [F64Bits.toBits_sub, F64Bits.toBits_add, F64Bits.toBits_neg,
    Expm1Words.float_ofBits, ln2Hi_bits, ln2Lo_bits, ln2Lo_neg]
  obtain ⟨hyf, hcf, hy, hc, hr⟩ := Expm1ReduceOne.reduce_one_neg x.toBits hxf (by linarith)
    (by linarith)
  obtain ⟨w, S, heq, hwf, hw1, hw2, hS⟩ := neg_one_near _ _ hyf hcf hy hc _ hr
  refine ⟨w, S, heq, hwf, hw1, hw2, ?_⟩
  have he : Real.exp (value x.toBits + Real.log 2) / 2 = Real.exp (value x.toBits) := by
    have := exp_shift_neg (value x.toBits) 1
    push_cast at this
    rwa [pow_one, one_mul] at this
  rwa [he] at hS

/-- The negative paths with `k` from the quotient, `θ2 ≤ abs(x) ≤ 38`. -/
theorem near_k (x : Float) (hxf : Finite x.toBits) (hneg : value x.toBits < 0)
    (hlo : value (UInt64.ofNat (1072734898 * 2 ^ 32)) ≤ -value x.toBits)
    (hhi : -value x.toBits ≤ 38) :
    ∃ w : UInt64, ∃ S : ℝ, (Tanh.expm1 x).toBits = Wasm.IEEE64.negate w ∧ Finite w ∧
      |value w - S| ≤ u * S ∧ |value w - S| ≤ u / 2 ∧
      |S - (1 - Real.exp (value x.toBits))| ≤ 3726 / 10000 * u := by
  obtain ⟨-, -, hθ2, -, hθ3⟩ := threshold_bounds
  set θ2 := value (UInt64.ofNat (1072734898 * 2 ^ 32))
  set θ3 := value (UInt64.ofNat (1078159482 * 2 ^ 32))
  have habs : |value x.toBits| = -value x.toBits := abs_of_neg hneg
  have h1 := high_finite x.toBits hxf
  have hn5 := high_of_ge x.toBits 1072734898 (by norm_num) (by rw [habs]; exact hlo)
  have hn3 := high_of_lt x.toBits 1078159482 (by norm_num) (by rw [habs]; linarith)
  have h2 : ¬ (highWord x.toBits ≥ 1082535490 ∧ x > Float.ofBits 4649454530587146735) := by
    intro h
    have := UInt64.le_iff_toNat_le.mp h.1
    change 1082535490 ≤ _ at this
    omega
  have h3 : ¬ (highWord x.toBits ≥ 1078159482 ∧ sgn x.toBits = true ∧
      x + Float.ofBits 118622047889322841 < 0.0) := by
    intro h
    have := UInt64.le_iff_toNat_le.mp h.1
    change 1078159482 ≤ _ at this
    omega
  have h4 : highWord x.toBits > 1071001154 := UInt64.lt_iff_toNat_lt.mpr (by
    change 1071001154 < _; omega)
  have h5 : ¬ highWord x.toBits < 1072734898 := by
    intro h
    have := UInt64.lt_iff_toNat_lt.mp h
    change _ < 1072734898 at this
    omega
  have hs : sgn x.toBits = true := by
    rw [sgn_iff]
    exact (F64Magnitude.sign_value x.toBits (magnitude_pos x.toBits (by
      rw [habs]; linarith))).mpr hneg
  rw [select_reduced_neg x h1 h2 h3 h4 h5 hs, Expm1Words.kernel_bits]
  simp only [F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_neg,
    F64Convert.toUInt64_eq, F64Convert.toBits_toFloat, Expm1Words.float_ofBits, ln2Hi_bits,
    ln2Lo_bits, invln2_bits, half_bits]
  rw [neg_bits _ (quotient_half_finite x.toBits hxf (by rw [habs]; linarith))]
  obtain ⟨hm1, hm2, hyf, hcf, hy, hc, hr⟩ :=
    Expm1ReduceK.reduce_k_neg x.toBits hxf (by linarith) (by linarith)
  obtain ⟨hcvf, -, -⟩ := Expm1ReduceK.integer_word _ (lt_of_le_of_lt hm2 (by norm_num))
  rw [neg_bits _ hcvf]
  set m := Wasm.IEEE64.truncSatI64U
    (Wasm.IEEE64.negate (Wasm.IEEE64.sub (Wasm.IEEE64.mul invln2 x.toBits) Expm1Words.half))
  have he := exp_shift_neg (value x.toBits) m.toNat
  rcases Nat.lt_or_ge m.toNat 2 with hm | hm
  · have hm' : m.toNat = 1 := by omega
    rw [hm'] at hr he
    obtain ⟨w, S, heq, hwf, hw1, hw2, hS⟩ := neg_one_near_m _ _ m hm' hyf hcf hy hc _ hr
    refine ⟨w, S, heq, hwf, hw1, hw2, ?_⟩
    rw [pow_one] at he
    rw [he] at hS
    have : (2451 : ℝ) / 10000 * u ≤ 3726 / 10000 * u := by
      rw [Expm1KernelInner.u_value]; norm_num
    linarith
  · obtain ⟨w, S, heq, hwf, hw1, hw2, hS⟩ := neg_k_near _ _ m hyf hcf hy hc _ hr hm hm2
    refine ⟨w, S, heq, hwf, hw1, hw2, ?_⟩
    rwa [he] at hS

/-- The positive paths for `2 ≤ x ≤ 44`, with `3 ≤ k ≤ 63`. -/
theorem near_pos (x : Float) (hxf : Finite x.toBits) (hlo : 2 ≤ value x.toBits)
    (hhi : value x.toBits ≤ 44) :
    ∃ S : ℝ, Finite (Tanh.expm1 x).toBits ∧ 0 < S ∧
      |value (Tanh.expm1 x).toBits - S| ≤ u * S ∧
      |S - (Real.exp (value x.toBits) - 1)| ≤ 85 / 100 * u * (Real.exp (value x.toBits) - 1) := by
  obtain ⟨-, -, hθ2, hθ2', hθ3⟩ := threshold_bounds
  set θ2 := value (UInt64.ofNat (1072734898 * 2 ^ 32))
  have hpos : 0 < value x.toBits := by linarith
  have habs : |value x.toBits| = value x.toBits := abs_of_pos hpos
  have h1 := high_finite x.toBits hxf
  have hn5 := high_of_ge x.toBits 1072734898 (by norm_num) (by rw [habs]; linarith)
  have hθ4 : (709 : ℝ) ≤ value (UInt64.ofNat (1082535490 * 2 ^ 32)) :=
    le_of_eq_of_le (by push_cast; ring)
      (word_ge 709 (UInt64.ofNat (1082535490 * 2 ^ 32)) (by decide +kernel))
  set θ4 := value (UInt64.ofNat (1082535490 * 2 ^ 32))
  have hn2 := high_of_lt x.toBits 1082535490 (by norm_num) (by rw [habs]; linarith)
  have h2 : ¬ (highWord x.toBits ≥ 1082535490 ∧ x > Float.ofBits 4649454530587146735) := by
    intro h
    have := UInt64.le_iff_toNat_le.mp h.1
    change 1082535490 ≤ _ at this
    omega
  have hs : sgn x.toBits = false := by
    rw [sgn_iff]
    have h := F64Magnitude.sign_value x.toBits (magnitude_pos x.toBits (by rw [habs]; linarith))
    cases hsg : Wasm.IEEE64.sign x.toBits
    · rfl
    · rw [hsg] at h; exact absurd (h.mp rfl) (by linarith)
  have h3 : ¬ (highWord x.toBits ≥ 1078159482 ∧ sgn x.toBits = true ∧
      x + Float.ofBits 118622047889322841 < 0.0) := by
    intro h
    rw [hs] at h
    exact absurd h.2.1 (by decide)
  have h4 : highWord x.toBits > 1071001154 := UInt64.lt_iff_toNat_lt.mpr (by
    change 1071001154 < _; omega)
  have h5 : ¬ highWord x.toBits < 1072734898 := by
    intro h
    have := UInt64.lt_iff_toNat_lt.mp h
    change _ < 1072734898 at this
    omega
  have hov := overflow_value
  rw [select_reduced_pos x h1 h2 h3 h4 h5 hs, Expm1Words.kernel_bits]
  simp only [F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_add,
    F64Convert.toUInt64_eq, F64Convert.toBits_toFloat, Expm1Words.float_ofBits, ln2Hi_bits,
    ln2Lo_bits, invln2_bits, half_bits, hs]
  obtain ⟨hm1, hm2, hyf, hcf, hy, hc, hr⟩ :=
    Expm1ReduceK.reduce_k_pos x.toBits hxf (by linarith) (by linarith)
  set m := Wasm.IEEE64.truncSatI64U
    (Wasm.IEEE64.add (Wasm.IEEE64.mul invln2 x.toBits) Expm1Words.half)
  obtain ⟨hL1, hL2⟩ := Expm1ReduceK.log_two_bounds
  have hu : u = 1 / 2 ^ 53 := Expm1KernelInner.u_value
  have hyc : |value x.toBits - (m.toNat : ℝ) * Real.log 2| ≤ 3467 / 10000 := by
    have h1' : |(m.toNat : ℤ) * Real.log 2 - (m.toNat : ℝ) * Real.log 2| = 0 := by
      push_cast; simp
    have hyb := abs_le.mp hy
    have hcb := abs_le.mp hc
    have hrb := abs_le.mp hr
    have hsm : 36 / 100 * u ≤ 1 / 10 ^ 10 := by rw [hu]; norm_num
    have h70 : (1 : ℝ) / 2 ^ 70 ≤ 1 / 10 ^ 10 := by norm_num
    push_cast at hrb
    rw [abs_le]; constructor <;> linarith
  have hyb := abs_le.mp hyc
  have hm3 : 3 ≤ m.toNat := by
    have : (2 : ℝ) < m.toNat := by nlinarith
    have : 2 < m.toNat := by exact_mod_cast this
    omega
  have hm63 : m.toNat ≤ 63 := by
    have : (m.toNat : ℝ) < 64 := by nlinarith
    have : m.toNat < 64 := by exact_mod_cast this
    omega
  have he := exp_shift_pos (value x.toBits) m.toNat
  rw [← he]
  rcases Nat.lt_or_ge m.toNat 20 with h20 | h20
  · exact mid_low_near _ _ m hyf hcf hy hc _ hr hm3 h20
  rcases Nat.lt_or_ge m.toNat 57 with h57 | h57
  · exact mid_high_near _ _ m hyf hcf hy hc _ hr h20 (by omega)
  · exact large_near _ _ m hyf hcf hy hc _ hr h57 (by omega)

#print axioms near_middle
#print axioms near_one
#print axioms near_k
#print axioms near_pos

end Verified.Examples.Expm1Near
