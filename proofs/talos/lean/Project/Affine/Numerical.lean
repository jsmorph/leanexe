import Project.Affine.Model
import Project.Affine.Real

namespace Project.Affine
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

def Bounded (word : UInt64) (bound : ℝ) : Prop := Finite word ∧ |value word| ≤ bound

theorem dot2_error (x0 x1 w0 w1 : UInt64)
    (hx0 : Bounded x0 64) (hx1 : Bounded x1 64)
    (hw0 : Bounded w0 16) (hw1 : Bounded w1 16) :
    Approximation (dot2 x0 x1 w0 w1) (value x0*value w0+value x1*value w1)
      2050 (4097*arithmeticEpsilon) := by
  have product (x w : UInt64) (hx : Bounded x 64) (hw : Bounded w 16) :=
    (Approximation.exact x hx.1 64 hx.2).mul (Approximation.exact w hw.1 16 hw.2)
      hw.2 (bound := 1024) (by norm_num) (by norm_num) (by norm_num)
  have hp0 := product x0 w0 hx0 hw0
  have hp1 := product x1 w1 hx1 hw1
  have hs := hp0.add hp1 (bound := 2049) (by norm_num) (by norm_num)
    (by norm_num [arithmeticEpsilon])
  exact hs.weaken (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])

theorem dot4_error (x w : Fin 4 → UInt64)
    (hx : ∀ i, Bounded (x i) 64) (hw : ∀ i, Bounded (w i) 16) :
    Approximation (dot4 (x 0) (x 1) (x 2) (x 3) (w 0) (w 1) (w 2) (w 3))
      (Real.dot (fun i => value (x i)) (fun i => value (w i))) 4101 (12294*arithmeticEpsilon) := by
  have h0 := dot2_error (x 0) (x 1) (w 0) (w 1) (hx 0) (hx 1) (hw 0) (hw 1)
  have h1 := dot2_error (x 2) (x 3) (w 2) (w 3) (hx 2) (hx 3) (hw 2) (hw 3)
  have hs := (h0.add h1 (bound := 4100) (by norm_num) (by norm_num) (by norm_num)).weaken
    (b' := 4101) (e' := 12294*arithmeticEpsilon)
      (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])
  convert hs using 1 <;> first | rfl | (simp [Real.dot, Fin.sum_univ_succ]; ring)

theorem dot8_error (x w : Fin 8 → UInt64)
    (hx : ∀ i, Bounded (x i) 64) (hw : ∀ i, Bounded (w i) 16) :
    Approximation (dot8 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
      (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7))
      (Real.dot (fun i => value (x i)) (fun i => value (w i))) 8203 (32790*arithmeticEpsilon) := by
  let low (i : Fin 4) : Fin 8 := ⟨i.val, by omega⟩
  let high (i : Fin 4) : Fin 8 := ⟨i.val+4, by omega⟩
  have h0 := dot4_error (fun i => x (low i)) (fun i => w (low i)) (fun i => hx _) (fun i => hw _)
  have h1 := dot4_error (fun i => x (high i)) (fun i => w (high i)) (fun i => hx _) (fun i => hw _)
  have hs := (h0.add h1 (bound := 8202) (by norm_num) (by norm_num) (by norm_num)).weaken
    (b' := 8203) (e' := 32790*arithmeticEpsilon)
      (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])
  convert hs using 1 <;> first | rfl | (simp [Real.dot, Fin.sum_univ_succ, low, high]; ring)

theorem affine4_error (x w : Fin 4 → UInt64) (bias : UInt64)
    (hx : ∀ i, Bounded (x i) 64) (hw : ∀ i, Bounded (w i) 16) (hb : Bounded bias 16) :
    Approximation (affine4 (x 0) (x 1) (x 2) (x 3) (w 0) (w 1) (w 2) (w 3) bias)
      (Real.dot (fun i => value (x i)) (fun i => value (w i))+value bias) 4118 (1/10000000000) := by
  have hs := (dot4_error x w hx hw).add (Approximation.exact bias hb.1 16 hb.2)
    (bound := 4117) (by norm_num) (by norm_num) (by norm_num)
  exact hs.weaken (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])

theorem affine8_error (x w : Fin 8 → UInt64) (bias : UInt64)
    (hx : ∀ i, Bounded (x i) 64) (hw : ∀ i, Bounded (w i) 16) (hb : Bounded bias 16) :
    Approximation (affine8 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
      (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7) bias)
      (Real.dot (fun i => value (x i)) (fun i => value (w i))+value bias) 8220 (1/10000000000) := by
  have hs := (dot8_error x w hx hw).add (Approximation.exact bias hb.1 16 hb.2)
    (bound := 8219) (by norm_num) (by norm_num) (by norm_num)
  exact hs.weaken (by norm_num [arithmeticEpsilon]) (by norm_num [arithmeticEpsilon])

#print axioms affine4_error
#print axioms affine8_error
end Project.Affine
