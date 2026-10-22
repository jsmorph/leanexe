import LeanExe.ProofKit.F64ErrorTrack

/-!
Error tracking with magnitude bounds: `AB w A e M` states that the word `w` approximates `A`
within `e` and that `|A| ≤ M`.  The rules for products, sums, and differences of
`F64ErrorTrack` then need only bounds on the operands.
-/

namespace Library.Numerics.Float64.Trig.TrigApprox

open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack

/-- `w` approximates `A` within `e`, and `|A| ≤ M`. -/
def AB (w : UInt64) (A e M : ℝ) : Prop := Approx w A e ∧ |A| ≤ M

theorem four_lt (n : Nat) (hn : 3 ≤ n) : (4 : ℝ) < 2 ^ n :=
  lt_of_lt_of_le (by norm_num) (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hn)

theorem AB.const (w : UInt64) (hw : Finite w) (M : ℝ) (h : |value w| ≤ M) :
    AB w (value w) 0 M :=
  ⟨approx_self w hw, h⟩

theorem AB.mono {w : UInt64} {A e M e' M' : ℝ} (h : AB w A e M) (he : e ≤ e') (hM : M ≤ M') :
    AB w A e' M' :=
  ⟨h.1.mono he, h.2.trans hM⟩

theorem AB.err_nonneg {w : UInt64} {A e M : ℝ} (h : AB w A e M) : 0 ≤ e :=
  (abs_nonneg _).trans h.1.2

theorem AB.mag_nonneg {w : UInt64} {A e M : ℝ} (h : AB w A e M) : 0 ≤ M :=
  (abs_nonneg _).trans h.2

theorem AB.mul {a b : UInt64} {A B ea eb MA MB : ℝ} (ha : AB a A ea MA) (hb : AB b B eb MB)
    (hA2 : MA + ea ≤ 2) (hB2 : MB + eb ≤ 2) :
    AB (Wasm.IEEE64.mul a b) (A * B)
      ((MA + ea) * eb + ea * MB + unitRoundoff64 * ((MA + ea) * (MB + eb)) +
        multiplicationUnderflowEpsilon) (MA * MB) := by
  have h0a : 0 ≤ MA + ea := add_nonneg ha.mag_nonneg ha.err_nonneg
  have h0b : 0 ≤ MB + eb := add_nonneg hb.mag_nonneg hb.err_nonneg
  have hmax : (MA + ea) * (MB + eb) < 2 ^ 1022 :=
    lt_of_le_of_lt (mul_le_mul hA2 hB2 h0b (by norm_num)) (by norm_num; exact four_lt 1022 (by norm_num))
  refine ⟨mul_approx ha.1 hb.1 MA MB ha.2 hb.2 hmax, ?_⟩
  rw [abs_mul]
  exact mul_le_mul ha.2 hb.2 (abs_nonneg _) ha.mag_nonneg

theorem AB.add {a b : UInt64} {A B ea eb MA MB : ℝ} (ha : AB a A ea MA) (hb : AB b B eb MB)
    (hA2 : MA + ea ≤ 2) (hB2 : MB + eb ≤ 2) :
    AB (Wasm.IEEE64.add a b) (A + B)
      (ea + eb + unitRoundoff64 * (MA + MB + ea + eb)) (MA + MB) := by
  have hAB : |A + B| ≤ MA + MB := (abs_add_le A B).trans (add_le_add ha.2 hb.2)
  have h4 := four_lt 1023 (by norm_num)
  refine ⟨add_approx ha.1 hb.1 _ (by linarith) (lt_of_le_of_lt (by linarith) h4), hAB⟩

theorem AB.sub {a b : UInt64} {A B ea eb MA MB : ℝ} (ha : AB a A ea MA) (hb : AB b B eb MB)
    (hA2 : MA + ea ≤ 2) (hB2 : MB + eb ≤ 2) :
    AB (Wasm.IEEE64.sub a b) (A - B)
      (ea + eb + unitRoundoff64 * (MA + MB + ea + eb)) (MA + MB) := by
  have hAB : |A - B| ≤ MA + MB := by
    rw [sub_eq_add_neg]
    exact (abs_add_le A (-B)).trans (by rw [abs_neg]; exact add_le_add ha.2 hb.2)
  have h4 := four_lt 1023 (by norm_num)
  refine ⟨sub_approx ha.1 hb.1 _ (by linarith) (lt_of_le_of_lt (by linarith) h4), hAB⟩

#print axioms AB.mul
#print axioms AB.add
#print axioms AB.sub

end Library.Numerics.Float64.Trig.TrigApprox
