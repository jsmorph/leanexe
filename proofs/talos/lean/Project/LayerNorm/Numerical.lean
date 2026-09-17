import Project.LayerNorm.Quotient

namespace Project.LayerNorm
open CodeLib.IEEE64 Project.ProofKit

set_option exponentiation.threshold 4096

theorem affine_error_bounded (q g b : UInt64) (target error : ℝ)
    (hq : Finite q) (hg : Finite g) (hb : Finite b)
    (bq : |value q| ≤ 3) (bg : |value g| ≤ 4) (bb : |value b| ≤ 4)
    (he : |value q-target| ≤ error) :
    let output := Wasm.IEEE64.add (Wasm.IEEE64.mul q g) b
    Finite output ∧ |value output-(target*value g+value b)| ≤ 4*error+29*arithmeticEpsilon := by
  have bm : |value q * value g| ≤ 12 := by
    rw [abs_mul]
    exact (mul_le_mul bq bg (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hm := F64ArithmeticBounds.mul_error q g hq hg 12 (by norm_num) (by norm_num) bm
  have hmMag : |value (Wasm.IEEE64.mul q g)| ≤ 13 :=
    (F64ArithmeticBounds.magnitude_of_error _ _ _ 12 hm.2 bm).trans (by norm_num [arithmeticEpsilon])
  have hs := F64ArithmeticBounds.add_error _ b hm.1 hb 17 (by norm_num) (by norm_num)
    ((abs_add_le _ _).trans (by linarith only [hmMag, bb]))
  have hp : |value q * value g-target*value g| ≤ 4*error := by
    rw [← sub_mul, abs_mul]
    exact (mul_le_mul he bg (abs_nonneg _) ((abs_nonneg _).trans he)).trans_eq (by ring)
  have he' : |value (Wasm.IEEE64.mul q g)-target*value g| ≤ 4*error+12*arithmeticEpsilon :=
    (abs_sub_le _ _ _).trans ((add_le_add hm.2 hp).trans_eq (by ring))
  refine ⟨hs.1, ?_⟩
  have h1 := abs_le.mp hs.2
  have h2 := abs_le.mp he'
  apply abs_le.mpr
  constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]

theorem affine_error (q g b : UInt64) (target : ℝ)
    (hq : Finite q) (hg : Finite g) (hb : Finite b)
    (bq : |value q| ≤ 3) (bg : |value g| ≤ 4) (bb : |value b| ≤ 4)
    (he : |value q-target| ≤ 1000000000*arithmeticEpsilon) :
    let output := Wasm.IEEE64.add (Wasm.IEEE64.mul q g) b
    Finite output ∧ |value output-(target*value g+value b)| ≤ 1/1000000 := by
  have h := affine_error_bounded q g b target (1000000000*arithmeticEpsilon) hq hg hb bq bg bb he
  exact ⟨h.1, h.2.trans (by norm_num [arithmeticEpsilon])⟩

theorem component_error_bounded (x : Fin 4 → UInt64) (g b : UInt64) (bound : ℝ)
    (hb1 : 1 ≤ bound) (hbmax : bound ≤ 16)
    (hf : ∀ i, Finite (x i)) (hx : ∀ i, |value (x i)| ≤ bound)
    (hg : Finite g) (hb : Finite b) (bg : |value g| ≤ 4) (bb : |value b| ≤ 4) (i : Fin 4) :
    let c := centeredWords x
    let d := denominator (c 0) (c 1) (c 2) (c 3)
    Finite (affine (c i) d g b) ∧
      |value (affine (c i) d g b)-
        (Real.normalized (1/100000) (fun j => value (x j)) i*value g+value b)| ≤
          (160000000*bound^2+64000*bound+16000057)*arithmeticEpsilon := by
  have hq := normalized_error_bounded x bound hb1 hbmax hf hx i
  have h := affine_error_bounded _ g b _ _ hq.1 hg hb hq.2.1 bg bb hq.2.2
  exact ⟨h.1, h.2.trans_eq (by ring)⟩

theorem component_error (x : Fin 4 → UInt64) (g b : UInt64)
    (hf : ∀ i, Finite (x i)) (hx : ∀ i, |value (x i)| ≤ 4)
    (hg : Finite g) (hb : Finite b) (bg : |value g| ≤ 4) (bb : |value b| ≤ 4) (i : Fin 4) :
    let c := centeredWords x
    let d := denominator (c 0) (c 1) (c 2) (c 3)
    Finite (affine (c i) d g b) ∧
      |value (affine (c i) d g b) -
        (Real.normalized (1/100000) (fun j => value (x j)) i * value g + value b)| ≤
          1/1000000 := by
  have hq := normalized_error x hf hx i
  exact affine_error _ g b _ hq.1 hg hb hq.2.1 bg bb hq.2.2

#print axioms affine_error
#print axioms component_error
#print axioms component_error_bounded
end Project.LayerNorm
