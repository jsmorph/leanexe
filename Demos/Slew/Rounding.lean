import Demos.Slew.Program
import LeanExe.ProofKit.F64Approx

/-! Binary64 facts for the slew planner's error lemmas.  `val x` is the real value of the float
`x` and `Fin x` states that it is finite.  The comparisons, `max`, `min`, and negation of finite
floats follow their real values, and the program's constants `margin`, `eta`, and `sMin` and the
literals it uses have the values stated here.  `Bnd x X e M` states that `x` is finite, within `e`
of the real `X`, and that `|X| ≤ M`.  The operations carry it from operands to results with the
rounding error that `F64Approx` charges, so a chain of operations yields numeric bounds that
`norm_num` checks. -/

namespace Demos.Slew.Rounding

open CodeLib.IEEE64 LeanExe.ProofKit LeanExe.ProofKit.F64Approx

set_option exponentiation.threshold 4096

/-- The real value of a float. -/
noncomputable def val (x : Float) : ℝ := value x.toBits

/-- The float `x` is finite. -/
def Fin (x : Float) : Prop := Finite x.toBits

theorem fapprox_val {x : Float} (hx : Fin x) : FApprox x (val x) 0 := approx_self x.toBits hx

theorem val_of_fapprox {x : Float} {X : ℝ} (h : FApprox x X 0) : val x = X := by
  have := h.2
  simp only [val]
  linarith [abs_nonneg (value x.toBits - X), abs_le.mp this]

theorem fin_of_fapprox {x : Float} {X e : ℝ} (h : FApprox x X e) : Fin x := h.1

/-! ### Comparisons -/

theorem le_value (a b : UInt64) (ha : Finite a) (hb : Finite b) :
    Wasm.IEEE64.le a b = decide (value a ≤ value b) := by
  simp only [Wasm.IEEE64.le, not_nan_of_finite ha, not_nan_of_finite hb, Bool.or_self,
    Bool.false_eq_true, ite_false, value]
  congr 1
  apply propext
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact_mod_cast Iff.rfl

theorem lt_value (a b : UInt64) (ha : Finite a) (hb : Finite b) :
    Wasm.IEEE64.lt a b = decide (value a < value b) := by
  simp only [Wasm.IEEE64.lt, not_nan_of_finite ha, not_nan_of_finite hb, Bool.or_self,
    Bool.false_eq_true, ite_false, value]
  congr 1
  apply propext
  rw [div_lt_div_iff_of_pos_right (by positivity)]
  exact_mod_cast Iff.rfl

theorem le_iff_val {a b : Float} (ha : Fin a) (hb : Fin b) : a ≤ b ↔ val a ≤ val b := by
  rw [F64Bits.le_iff, le_value _ _ ha hb, decide_eq_true_iff]
  rfl

theorem lt_iff_val {a b : Float} (ha : Fin a) (hb : Fin b) : a < b ↔ val a < val b := by
  rw [F64Bits.lt_iff, lt_value _ _ ha hb, decide_eq_true_iff]
  rfl

theorem max_val {a b : Float} (ha : Fin a) (hb : Fin b) :
    Fin (max a b) ∧ val (max a b) = max (val a) (val b) := by
  have e := F64Bits.toBits_max a b
  rw [le_value _ _ ha hb] at e
  simp only [Fin, val, e]
  by_cases h : value a.toBits ≤ value b.toBits
  · simp only [h, decide_true, ite_true]
    exact ⟨hb, (max_eq_right h).symm⟩
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    exact ⟨ha, (max_eq_left (le_of_lt (not_le.mp h))).symm⟩

theorem min_val {a b : Float} (ha : Fin a) (hb : Fin b) :
    Fin (min a b) ∧ val (min a b) = min (val a) (val b) := by
  have e := F64Bits.toBits_min a b
  rw [le_value _ _ ha hb] at e
  simp only [Fin, val, e]
  by_cases h : value a.toBits ≤ value b.toBits
  · simp only [h, decide_true, ite_true]
    exact ⟨ha, (min_eq_left h).symm⟩
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    exact ⟨hb, (min_eq_right (le_of_lt (not_le.mp h))).symm⟩

theorem neg_val {a : Float} (ha : Fin a) : Fin (-a) ∧ val (-a) = -val a := by
  have h := fapprox_neg (fapprox_val ha)
  exact ⟨h.1, val_of_fapprox h⟩

/-! ### Constants -/

theorem margin_bits : Demos.Slew.margin.toBits = 0x3E12E5D9E5C45270 := rfl
theorem eta_bits : Demos.Slew.eta.toBits = 0x3D719799812DEA11 := rfl
theorem sMin_bits : Demos.Slew.sMin.toBits = 0x3E7AD7F29ABCAF48 := rfl
theorem two_bits : (2.0 : Float).toBits = 0x4000000000000000 := rfl
theorem twoEighth_bits : (2.125 : Float).toBits = 0x4001000000000000 := rfl

theorem margin_val : Fin Demos.Slew.margin ∧ val Demos.Slew.margin = 5319273606304368 / 2 ^ 82 := by
  have hs : Wasm.IEEE64.scaledValue 0x3E12E5D9E5C45270 = 5319273606304368 * 2 ^ 992 := by
    decide +kernel
  refine ⟨?_, ?_⟩
  · simp only [Fin, margin_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [val, margin_bits, value, hs]; push_cast; ring

theorem eta_val : Fin Demos.Slew.eta ∧ val Demos.Slew.eta = 4951760157141521 / 2 ^ 92 := by
  have hs : Wasm.IEEE64.scaledValue 0x3D719799812DEA11 = 4951760157141521 * 2 ^ 982 := by
    decide +kernel
  refine ⟨?_, ?_⟩
  · simp only [Fin, eta_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [val, eta_bits, value, hs]; push_cast; ring

theorem sMin_val : Fin Demos.Slew.sMin ∧ val Demos.Slew.sMin = 7555786372591432 / 2 ^ 76 := by
  have hs : Wasm.IEEE64.scaledValue 0x3E7AD7F29ABCAF48 = 7555786372591432 * 2 ^ 998 := by
    decide +kernel
  refine ⟨?_, ?_⟩
  · simp only [Fin, sMin_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [val, sMin_bits, value, hs]; push_cast; ring

theorem two_val : Fin (2.0 : Float) ∧ val (2.0 : Float) = 2 := by
  have hs : Wasm.IEEE64.scaledValue 0x4000000000000000 = 2 ^ 1075 := by decide +kernel
  refine ⟨?_, ?_⟩
  · simp only [Fin, two_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [val, two_bits, value, hs]; push_cast; ring

theorem twoEighth_val : Fin (2.125 : Float) ∧ val (2.125 : Float) = 17 / 8 := by
  have hs : Wasm.IEEE64.scaledValue 0x4001000000000000 = 17 * 2 ^ 1071 := by decide +kernel
  refine ⟨?_, ?_⟩
  · simp only [Fin, twoEighth_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [val, twoEighth_bits, value, hs]; push_cast; ring

theorem margin_bounds : 1.0999e-9 ≤ val Demos.Slew.margin ∧ val Demos.Slew.margin ≤ 1.1e-9 := by
  rw [margin_val.2]; constructor <;> norm_num

theorem eta_bounds : 0.9999e-12 ≤ val Demos.Slew.eta ∧ val Demos.Slew.eta ≤ 1.0001e-12 := by
  rw [eta_val.2]; constructor <;> norm_num

theorem sMin_bounds : 0.9999e-7 ≤ val Demos.Slew.sMin ∧ val Demos.Slew.sMin ≤ 1.0001e-7 := by
  rw [sMin_val.2]; constructor <;> norm_num

/-! ### Bounded approximations -/

/-- `x` is finite, within `e` of `X`, and `|X| ≤ M`. -/
def Bnd (x : Float) (X e M : ℝ) : Prop := FApprox x X e ∧ |X| ≤ M

theorem Bnd.of_val {x : Float} {M : ℝ} (hx : Fin x) (hM : |val x| ≤ M) : Bnd x (val x) 0 M :=
  ⟨fapprox_val hx, hM⟩

theorem Bnd.err_nonneg {x : Float} {X e M : ℝ} (h : Bnd x X e M) : 0 ≤ e :=
  (abs_nonneg _).trans h.1.2

theorem Bnd.bound_nonneg {x : Float} {X e M : ℝ} (h : Bnd x X e M) : 0 ≤ M :=
  (abs_nonneg _).trans h.2

theorem Bnd.mono {x : Float} {X e M e' M' : ℝ} (h : Bnd x X e M) (he : e ≤ e') (hM : M ≤ M') :
    Bnd x X e' M' := ⟨Approx.mono h.1 he, h.2.trans hM⟩

theorem Bnd.rebound {x : Float} {X e M M' : ℝ} (h : Bnd x X e M) (hM : |X| ≤ M') :
    Bnd x X e M' := ⟨h.1, hM⟩

theorem Bnd.lower {x : Float} {X e M : ℝ} (h : Bnd x X e M) : X - e ≤ val x := h.1.lower

theorem Bnd.upper {x : Float} {X e M : ℝ} (h : Bnd x X e M) : val x ≤ X + e := h.1.upper

theorem Bnd.mul {a b : Float} {A B ea eb Ma Mb : ℝ} (e : ℝ) (ha : Bnd a A ea Ma)
    (hb : Bnd b B eb Mb) (hbig : (Ma + ea) * (Mb + eb) < 2 ^ 1022)
    (he : ea * Mb + Ma * eb + ea * eb + (Ma + ea) * (Mb + eb) / 2 ^ 53 + 1 / 2 ^ 1075 ≤ e) :
    Bnd (a * b) (A * B) e (Ma * Mb) := by
  refine ⟨Approx.mono (fapprox_mul ha.1 hb.1 Ma Mb ha.2 hb.2 _ le_rfl hbig) he, ?_⟩
  rw [abs_mul]
  exact mul_le_mul ha.2 hb.2 (abs_nonneg _) ha.bound_nonneg

theorem Bnd.add {a b : Float} {A B ea eb Ma Mb : ℝ} (e : ℝ) (ha : Bnd a A ea Ma)
    (hb : Bnd b B eb Mb) (hbig : Ma + Mb + (ea + eb) < 2 ^ 1023)
    (he : ea + eb + (Ma + Mb + (ea + eb)) / 2 ^ 53 ≤ e) :
    Bnd (a + b) (A + B) e (Ma + Mb) := by
  have hAB : |A + B| ≤ Ma + Mb := (abs_add_le _ _).trans (add_le_add ha.2 hb.2)
  exact ⟨Approx.mono (fapprox_add ha.1 hb.1 _ (by linarith) hbig) he, hAB⟩

theorem Bnd.sub {a b : Float} {A B ea eb Ma Mb : ℝ} (e : ℝ) (ha : Bnd a A ea Ma)
    (hb : Bnd b B eb Mb) (hbig : Ma + Mb + (ea + eb) < 2 ^ 1023)
    (he : ea + eb + (Ma + Mb + (ea + eb)) / 2 ^ 53 ≤ e) :
    Bnd (a - b) (A - B) e (Ma + Mb) := by
  have hAB : |A - B| ≤ Ma + Mb := (abs_sub _ _).trans (add_le_add ha.2 hb.2)
  exact ⟨Approx.mono (fapprox_sub ha.1 hb.1 _ (by linarith) hbig) he, hAB⟩

theorem Bnd.neg {a : Float} {A ea Ma : ℝ} (ha : Bnd a A ea Ma) : Bnd (-a) (-A) ea Ma :=
  ⟨fapprox_neg ha.1, by rw [abs_neg]; exact ha.2⟩

theorem Bnd.two : Bnd (2.0 : Float) 2 0 2 := by
  have h := Bnd.of_val two_val.1 (M := 2) (by rw [two_val.2]; norm_num)
  rwa [two_val.2] at h

end Demos.Slew.Rounding
