import Project.ProofKit.CompensatedSumBounds
import Project.ProofKit.F64OneAdd
import Project.ProofKit.F64SubnormalScale

namespace Project.ProofKit.F64CompensatedSum
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

def roundedSum (s p : UInt64) : UInt64 :=
  let y := Wasm.IEEE64.add s p
  let l := Wasm.IEEE64.add (Wasm.IEEE64.sub s y) p
  let h := Wasm.IEEE64.add 0x3FF0000000000000 y
  let c := Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.sub 0x3FF0000000000000 h) y) l
  Wasm.IEEE64.sub (Wasm.IEEE64.add h c) 0x3FF0000000000000

theorem rounded_sum_error (s p : UInt64) (hsf : Finite s) (hpf : Finite p)
    (hs : 0 < value s ∧ value s ≤ 2) (hp : |value p| ≤ value s/200)
    (hyword : Wasm.IEEE64.add s p < 0x3FF0000000000000) :
    Finite (roundedSum s p) ∧
    |value (roundedSum s p)-(value s+value p)| ≤
      1/(2 : ℝ)^53+3/1000000000000000000 ∧
    ∃ j : UInt64, 0x3FF0000000000000 ≤ j ∧ j ≤ 0x4000000000000000 ∧
      roundedSum s p = Wasm.IEEE64.sub j 0x3FF0000000000000 := by
  let y := Wasm.IEEE64.add s p
  let d := Wasm.IEEE64.sub s y
  let l := Wasm.IEEE64.add d p
  let h := Wasm.IEEE64.add 0x3FF0000000000000 y
  let z := Wasm.IEEE64.sub 0x3FF0000000000000 h
  let a := Wasm.IEEE64.add z y
  let c := Wasm.IEEE64.add a l
  have hp1 : |value p| ≤ 1 := by linarith
  have hpm := abs_le.mp hp
  have hT : 0 < value s+value p := by linarith
  have hsum : |value s+value p| ≤ 3 := by
    rw [abs_of_pos hT]
    linarith
  have hY := F64AddBounds.add_real_relative s p hsf hpf (hsum.trans_lt (by norm_num))
  change Finite y ∧ |value y-(value s+value p)| ≤ unitRoundoff64*|value s+value p| at hY
  have hyp : 0 < value y := by
    have he := hY.2
    rw [abs_of_pos hT] at he
    have hb := (abs_le.mp he).1
    norm_num [unitRoundoff64] at hb
    linarith
  have hyu : value y ≤ 1-1/(2 : ℝ)^53 := F64OneAdd.below_one_value y hyword
  have hym : |value y| ≤ 1 := by rw [abs_of_pos hyp]; linarith
  have hdiff : |value s-value y| ≤ 3 := by
    apply (abs_sub _ _).trans
    rw [abs_of_pos hs.1]
    linarith
  have hD := F64AddBounds.sub_real_relative s y hsf hY.1 (hdiff.trans_lt (by norm_num))
  change Finite d ∧ |value d-(value s-value y)| ≤ unitRoundoff64*|value s-value y| at hD
  have hdm : |value d| ≤ 4 := by
    have he : |value d-(value s-value y)| ≤ 3*unitRoundoff64 := by
      exact hD.2.trans (by nlinarith [show 0 ≤ unitRoundoff64 by norm_num [unitRoundoff64]])
    have ht := abs_add_le (value d-(value s-value y)) (value s-value y)
    rw [sub_add_cancel] at ht
    norm_num [unitRoundoff64] at he
    linarith
  have hls : |value d+value p| ≤ 5 := (abs_add_le _ _).trans (by linarith)
  have hL := F64AddBounds.add_real_relative d p hD.1 hpf (hls.trans_lt (by norm_num))
  change Finite l ∧ |value l-(value d+value p)| ≤ unitRoundoff64*|value d+value p| at hL
  have hlm : |value l| ≤ 6 := by
    have he : |value l-(value d+value p)| ≤ 5*unitRoundoff64 := by
      exact hL.2.trans (by nlinarith [show 0 ≤ unitRoundoff64 by norm_num [unitRoundoff64]])
    have ht := abs_add_le (value l-(value d+value p)) (value d+value p)
    rw [sub_add_cancel] at ht
    norm_num [unitRoundoff64] at he
    linarith
  have hH := F64OneAdd.add_one y hY.1 hyp (by linarith)
  change Finite h ∧ 0x3FF0000000000000 ≤ h ∧ h ≤ 0x4000000000000000 ∧
    1 ≤ value h ∧ value h ≤ 1+2*value y ∧
    |value h-(1+value y)| ≤ 1/(2 : ℝ)^53 at hH
  have hZ := F64OneSubtract.subtract_one_exact h hH.2.1 hH.2.2.1
  have hzv : value z = 1-value h := hZ.2.2.2
  have hzm : |value z| ≤ 2 := by
    rw [hzv]
    apply abs_le.mpr
    constructor <;> linarith [hH.2.2.2.1, hH.2.2.2.2.1]
  have has : |value z+value y| ≤ 3 := (abs_add_le _ _).trans (by linarith)
  have hA := F64AddBounds.add_real_relative z y hZ.2.2.1 hY.1 (has.trans_lt (by norm_num))
  change Finite a ∧ |value a-(value z+value y)| ≤ unitRoundoff64*|value z+value y| at hA
  have ham : |value a| ≤ 4 := by
    have he : |value a-(value z+value y)| ≤ 3*unitRoundoff64 := by
      exact hA.2.trans (by nlinarith [show 0 ≤ unitRoundoff64 by norm_num [unitRoundoff64]])
    have ht := abs_add_le (value a-(value z+value y)) (value z+value y)
    rw [sub_add_cancel] at ht
    norm_num [unitRoundoff64] at he
    linarith
  have hcs : |value a+value l| ≤ 10 := (abs_add_le _ _).trans (by linarith)
  have hC := F64AddBounds.add_real_relative a l hA.1 hL.1 (hcs.trans_lt (by norm_num))
  change Finite c ∧ |value c-(value a+value l)| ≤ unitRoundoff64*|value a+value l| at hC
  have hcomp := CompensatedSumBounds.correction_bounds (value s) (value p) (value y)
    (value d) (value l) (value h) (value a) (value c) hs hp ⟨hyp, hyu⟩
    hY.2 hD.2 hL.2 ⟨hH.2.2.2.1, hH.2.2.2.2.1, hH.2.2.2.2.2⟩
    (by rw [hzv] at hA; exact hA.2) hC.2
  have hJ := F64OneAdd.add_interval h c hH.1 hC.1 hcomp.1 hcomp.2.1
  have hR := F64OneSubtract.subtract_one_exact _ hJ.2.1 hJ.2.2.1
  refine ⟨hR.1, ?_, ⟨Wasm.IEEE64.add h c, hJ.2.1, hJ.2.2.1, rfl⟩⟩
  change |value (Wasm.IEEE64.sub (Wasm.IEEE64.add h c) 0x3FF0000000000000)-(value s+value p)| ≤ _
  rw [hR.2.1]
  have hid : value (Wasm.IEEE64.add h c)-1-(value s+value p) =
      (value (Wasm.IEEE64.add h c)-(value h+value c))+(value h+value c-(1+value s+value p)) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hJ.2.2.2 hcomp.2.2)

theorem scaled_sum_error (s p : UInt64) (hsf : Finite s) (hpf : Finite p)
    (hs : 0 < value s ∧ value s ≤ 2) (hp : |value p| ≤ value s/200)
    (hyword : Wasm.IEEE64.add s p < 0x3FF0000000000000) :
    let r := Wasm.IEEE64.mul 0x0010000000000000 (roundedSum s p)
    Finite r ∧ |value r-(value s+value p)*(2 : ℝ)^(-1022 : Int)| ≤
      (1/(2 : ℝ)^53+3/1000000000000000000)*(2 : ℝ)^(-1022 : Int) := by
  have hr := rounded_sum_error s p hsf hpf hs hp hyword
  obtain ⟨j, hjl, hju, hje⟩ := hr.2.2
  have hm := F64SubnormalScale.scale_subtracted_one j hjl hju
  rw [hje]
  refine ⟨hm.1, ?_⟩
  rw [hm.2, ← sub_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2^(-1022 : Int))]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  simpa only [hje] using hr.2.1

theorem rounded_sum_zero (s p : UInt64) (hsf : Finite s) (hpf : Finite p)
    (hs : 0 < value s ∧ value s ≤ 1/(2 : ℝ)^55) (hp : |value p| ≤ value s/200)
    (hyword : Wasm.IEEE64.add s p < 0x3FF0000000000000) : roundedSum s p = 0 := by
  have hr := rounded_sum_error s p hsf hpf ⟨hs.1, hs.2.trans (by norm_num)⟩ hp hyword
  obtain ⟨j, hjl, hju, hje⟩ := hr.2.2
  have hj := F64OneSubtract.subtract_one_exact j hjl hju
  have he := (abs_le.mp hr.2.1).2
  rw [hje, hj.2.1] at he
  have hpm := (abs_le.mp hp).2
  have hv : value j < 1+1/(2 : ℝ)^52 := by linarith
  have hword := F64OneAdd.eq_one_of_small j hjl hju hv
  rw [hje, hword]
  decide

#print axioms rounded_sum_zero
#print axioms rounded_sum_error
#print axioms scaled_sum_error
end Project.ProofKit.F64CompensatedSum
