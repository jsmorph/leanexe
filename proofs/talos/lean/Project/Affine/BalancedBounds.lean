import Project.Affine.Numerical

namespace Project.Affine
open CodeLib.IEEE64 Project.ProofKit F64Horner

set_option exponentiation.threshold 4096

theorem Bounded.weaken {word : UInt64} {bound larger : ℝ}
    (h : Bounded word bound) (hb : bound ≤ larger) : Bounded word larger :=
  ⟨h.1, h.2.trans hb⟩

theorem product_error_bounded (x w : UInt64) (bound : ℝ)
    (hb : 1 ≤ bound) (hbMax : bound ≤ 2^40)
    (hx : Finite x) (hw : Finite w) (hp : |value x*value w| ≤ bound) :
    Approximation (Wasm.IEEE64.mul x w) (value x*value w)
      (bound+arithmeticEpsilon*bound) (arithmeticEpsilon*bound) := by
  have h := F64ArithmeticBounds.mul_error x w hx hw bound hb
    (hbMax.trans_lt (by norm_num)) hp
  exact ⟨h.1, F64ArithmeticBounds.magnitude_of_error _ _ _ _ h.2 hp, h.2⟩

theorem dot2_error_bounded (x0 x1 w0 w1 : UInt64) (bound : ℝ)
    (hb : 1 ≤ bound) (hbMax : bound ≤ 2^40)
    (hx0 : Finite x0) (hx1 : Finite x1) (hw0 : Finite w0) (hw1 : Finite w1)
    (hp0 : |value x0*value w0| ≤ bound) (hp1 : |value x1*value w1| ≤ bound) :
    Approximation (dot2 x0 x1 w0 w1) (value x0*value w0+value x1*value w1)
      (2*bound+2) ((4*bound+1)*arithmeticEpsilon) := by
  have h0 := product_error_bounded x0 w0 bound hb hbMax hx0 hw0 hp0
  have h1 := product_error_bounded x1 w1 bound hb hbMax hx1 hw1 hp1
  have hs := h0.add h1 (bound := 2*bound+1) (by linarith)
    (by norm_num at hbMax ⊢; linarith)
    (by norm_num [arithmeticEpsilon] at hbMax ⊢; linarith)
  exact hs.weaken (by norm_num [arithmeticEpsilon] at hbMax ⊢; linarith)
    (by ring_nf; rfl)

theorem dot4_error_bounded (x w : Fin 4 → UInt64) (bound : ℝ)
    (hb : 1 ≤ bound) (hbMax : bound ≤ 2^40)
    (hx : ∀ i, Finite (x i)) (hw : ∀ i, Finite (w i))
    (hp : ∀ i, |value (x i)*value (w i)| ≤ bound) :
    Approximation (dot4 (x 0) (x 1) (x 2) (x 3) (w 0) (w 1) (w 2) (w 3))
      (Real.dot (fun i => value (x i)) (fun i => value (w i)))
      (4*bound+5) ((12*bound+6)*arithmeticEpsilon) := by
  have h0 := dot2_error_bounded (x 0) (x 1) (w 0) (w 1) bound hb hbMax
    (hx 0) (hx 1) (hw 0) (hw 1) (hp 0) (hp 1)
  have h1 := dot2_error_bounded (x 2) (x 3) (w 2) (w 3) bound hb hbMax
    (hx 2) (hx 3) (hw 2) (hw 3) (hp 2) (hp 3)
  have hs := (h0.add h1 (bound := 4*bound+4) (by linarith)
    (by norm_num at hbMax ⊢; linarith) (by linarith)).weaken
    (b' := 4*bound+5) (e' := (12*bound+6)*arithmeticEpsilon)
    (by norm_num [arithmeticEpsilon] at hbMax ⊢; linarith) (by ring_nf; rfl)
  convert hs using 1 <;> first | rfl | (simp [Real.dot, Fin.sum_univ_succ]; ring)

theorem dot8_error_bounded (x w : Fin 8 → UInt64) (bound : ℝ)
    (hb : 1 ≤ bound) (hbMax : bound ≤ 2^40)
    (hx : ∀ i, Finite (x i)) (hw : ∀ i, Finite (w i))
    (hp : ∀ i, |value (x i)*value (w i)| ≤ bound) :
    Approximation (dot8 (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7)
      (w 0) (w 1) (w 2) (w 3) (w 4) (w 5) (w 6) (w 7))
      (Real.dot (fun i => value (x i)) (fun i => value (w i)))
      (8*bound+11) ((32*bound+22)*arithmeticEpsilon) := by
  let low (i : Fin 4) : Fin 8 := ⟨i.val, by omega⟩
  let high (i : Fin 4) : Fin 8 := ⟨i.val+4, by omega⟩
  have h0 := dot4_error_bounded (fun i => x (low i)) (fun i => w (low i)) bound hb hbMax
    (fun i => hx _) (fun i => hw _) (fun i => hp _)
  have h1 := dot4_error_bounded (fun i => x (high i)) (fun i => w (high i)) bound hb hbMax
    (fun i => hx _) (fun i => hw _) (fun i => hp _)
  have hs := (h0.add h1 (bound := 8*bound+10) (by linarith)
    (by norm_num at hbMax ⊢; linarith) (by linarith)).weaken
    (b' := 8*bound+11) (e' := (32*bound+22)*arithmeticEpsilon)
    (by norm_num [arithmeticEpsilon] at hbMax ⊢; linarith) (by ring_nf; rfl)
  convert hs using 1 <;> first | rfl | (simp [Real.dot, Fin.sum_univ_succ, low, high]; ring)

#print axioms dot4_error_bounded
#print axioms dot8_error_bounded
end Project.Affine
