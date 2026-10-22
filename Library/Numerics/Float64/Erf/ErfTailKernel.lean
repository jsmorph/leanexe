import Library.Numerics.Float64.Erf.ErfTailPieces7

/-!
The tail kernels of `s_erf.c`.  `R_a/S_a` models `log (x erfcx x) + 0.5625` within `2^-56` on
`[1.25, tailB2]`, where `erf` and `erfc` use it, and `R_b/S_b` within `2^-56` on `[tailB1, 28]`.
The pieces of `ErfTailPieces0` to `ErfTailPieces7` cover each range.  Their models of `erfcxN`
form one chain from the asymptotic bounds at 28 down to 1.25, each piece's accuracy following from
the previous one by `ode_backward` and a rational check at the common end.
-/

namespace Library.Numerics.Float64.Erf.ErfTailKernel
open Real Set LeanExe.ProofKit PolyBound RealErf RealErfScaled ErfTailBase ErfTailCoeffs
  ErfTailPieces0 ErfTailPieces1 ErfTailPieces2 ErfTailPieces3 ErfTailPieces4 ErfTailPieces5 ErfTailPieces6 ErfTailPieces7

theorem tail_kernel_a : ∀ x ∈ Icc (5 / 4 : ℝ) tailB2, |tailF tailRA tailSA x| ≤ (epsT : ℝ) := by
  intro x hx
  have hlo : (a31 : ℝ) = 5 / 4 := by rw [show a31 = 5 / 4 by decide +kernel] <;> norm_num
  have hhi : (b24 : ℝ) = (tailB2 : ℝ) := by rw [show b24 = tailB2 by decide +kernel] <;> norm_num
  rcases le_or_gt x (b31 : ℝ) with h31 | h31
  · exact piece31a x ⟨by rw [hlo]; exact hx.1, h31⟩
  rcases le_or_gt x (b30 : ℝ) with h30 | h30
  · exact piece30a x ⟨h31.le, h30⟩
  rcases le_or_gt x (b29 : ℝ) with h29 | h29
  · exact piece29a x ⟨h30.le, h29⟩
  rcases le_or_gt x (b28 : ℝ) with h28 | h28
  · exact piece28a x ⟨h29.le, h28⟩
  rcases le_or_gt x (b27 : ℝ) with h27 | h27
  · exact piece27a x ⟨h28.le, h27⟩
  rcases le_or_gt x (b26 : ℝ) with h26 | h26
  · exact piece26a x ⟨h27.le, h26⟩
  rcases le_or_gt x (b25 : ℝ) with h25 | h25
  · exact piece25a x ⟨h26.le, h25⟩
  exact piece24a x ⟨h25.le, by rw [hhi]; exact hx.2⟩

theorem tail_kernel_b : ∀ x ∈ Icc (tailB1 : ℝ) 28, |tailF tailRB tailSB x| ≤ (epsT : ℝ) := by
  intro x hx
  have hlo : (a24 : ℝ) = (tailB1 : ℝ) := by rw [show a24 = tailB1 by decide +kernel] <;> norm_num
  have hhi : (b0 : ℝ) = 28 := by rw [show b0 = 28 by decide +kernel] <;> norm_num
  rcases le_or_gt x (b24 : ℝ) with h24 | h24
  · exact piece24b x ⟨by rw [hlo]; exact hx.1, h24⟩
  rcases le_or_gt x (b23 : ℝ) with h23 | h23
  · exact piece23b x ⟨h24.le, h23⟩
  rcases le_or_gt x (b22 : ℝ) with h22 | h22
  · exact piece22b x ⟨h23.le, h22⟩
  rcases le_or_gt x (b21 : ℝ) with h21 | h21
  · exact piece21b x ⟨h22.le, h21⟩
  rcases le_or_gt x (b20 : ℝ) with h20 | h20
  · exact piece20b x ⟨h21.le, h20⟩
  rcases le_or_gt x (b19 : ℝ) with h19 | h19
  · exact piece19b x ⟨h20.le, h19⟩
  rcases le_or_gt x (b18 : ℝ) with h18 | h18
  · exact piece18b x ⟨h19.le, h18⟩
  rcases le_or_gt x (b17 : ℝ) with h17 | h17
  · exact piece17b x ⟨h18.le, h17⟩
  rcases le_or_gt x (b16 : ℝ) with h16 | h16
  · exact piece16b x ⟨h17.le, h16⟩
  rcases le_or_gt x (b15 : ℝ) with h15 | h15
  · exact piece15b x ⟨h16.le, h15⟩
  rcases le_or_gt x (b14 : ℝ) with h14 | h14
  · exact piece14b x ⟨h15.le, h14⟩
  rcases le_or_gt x (b13 : ℝ) with h13 | h13
  · exact piece13b x ⟨h14.le, h13⟩
  rcases le_or_gt x (b12 : ℝ) with h12 | h12
  · exact piece12b x ⟨h13.le, h12⟩
  rcases le_or_gt x (b11 : ℝ) with h11 | h11
  · exact piece11b x ⟨h12.le, h11⟩
  rcases le_or_gt x (b10 : ℝ) with h10 | h10
  · exact piece10b x ⟨h11.le, h10⟩
  rcases le_or_gt x (b9 : ℝ) with h9 | h9
  · exact piece9b x ⟨h10.le, h9⟩
  rcases le_or_gt x (b8 : ℝ) with h8 | h8
  · exact piece8b x ⟨h9.le, h8⟩
  rcases le_or_gt x (b7 : ℝ) with h7 | h7
  · exact piece7b x ⟨h8.le, h7⟩
  rcases le_or_gt x (b6 : ℝ) with h6 | h6
  · exact piece6b x ⟨h7.le, h6⟩
  rcases le_or_gt x (b5 : ℝ) with h5 | h5
  · exact piece5b x ⟨h6.le, h5⟩
  rcases le_or_gt x (b4 : ℝ) with h4 | h4
  · exact piece4b x ⟨h5.le, h4⟩
  rcases le_or_gt x (b3 : ℝ) with h3 | h3
  · exact piece3b x ⟨h4.le, h3⟩
  rcases le_or_gt x (b2 : ℝ) with h2 | h2
  · exact piece2b x ⟨h3.le, h2⟩
  rcases le_or_gt x (b1 : ℝ) with h1 | h1
  · exact piece1b x ⟨h2.le, h1⟩
  exact piece0b x ⟨h1.le, by rw [hhi]; exact hx.2⟩

#print axioms tail_kernel_a
#print axioms tail_kernel_b

end Library.Numerics.Float64.Erf.ErfTailKernel
