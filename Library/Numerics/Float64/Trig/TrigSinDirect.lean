import Library.Numerics.Float64.Trig.TrigSinTail

/-!
The rounding error of `Trig.kernelSin x 0 false`, the sine kernel without a tail.  For
`2 ^ -70 ≤ |x| ≤ 0.78541`, the result is the rounding of a real `t` with
`|t - sin x| ≤ u (33/40 |x| ^ 3 + |x| / 30)`, and so is the result of `kernelSin x y true` for
`|y| ≤ |x| / 2 ^ 52` with `sin (x + y)` in place of `sin x`.
-/

namespace Library.Numerics.Float64.Trig.TrigSinDirect

open CodeLib.IEEE64 LeanExe.ProofKit F64ErrorTrack PolyBound TrigApprox TrigKernelWords
  TrigSinTail

local notation "𝐮" => unitRoundoff64
local notation "η" => multiplicationUnderflowEpsilon

/-- The product that `kernelSin x 0 false` adds to `x`, on words. -/
def LW (x : UInt64) : UInt64 :=
  Wasm.IEEE64.mul (Wasm.IEEE64.mul (Wasm.IEEE64.mul x x) x)
    (Wasm.IEEE64.add wS1 (Wasm.IEEE64.mul (Wasm.IEEE64.mul x x) (sinR (Wasm.IEEE64.mul x x))))

theorem sinDirectW_eq (x : UInt64) : sinDirectW x = Wasm.IEEE64.add x (LW x) := rfl

set_option exponentiation.threshold 1200 in
set_option maxHeartbeats 1000000 in
/-- The error of the product `LW`, in powers of `X = |x|`. -/
theorem LW_AB (x : UInt64) (X : ℝ) (hxf : Finite x) (hX : |value x| = X)
    (hX0 : 1 / 2 ^ 70 ≤ X) (hX1 : X ≤ 78541 / 100000) :
    ∃ M, AB (LW x)
      (value x * value x * value x * (value wS1 + value x * value x *
        (value wS2 + value x * value x * (value wS3 + value x * value x * value wS4) +
          value x * value x * (value x * value x * (value x * value x)) *
            (value wS5 + value x * value x * value wS6))))
      (3 / 4 * 𝐮 * X ^ 3 + 16 * 𝐮 * 𝐮 * X) M ∧ M ≤ 1 := by
  have h0 : 0 ≤ X := hX ▸ abs_nonneg _
  obtain ⟨⟨n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12⟩, ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11⟩, ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩, hX1', hXX⟩ := pow_facts X h0 hX1
  obtain ⟨c1, -⟩ := coeffs_AB
  have hx : AB x (value x) 0 X := AB.const x hxf X hX.le
  have z := (AB.mul hx hx (by linarith) (by linarith)).mono
    (e' := 𝐮 * X ^ 2 + η) (M' := X ^ 2) (le_of_eq (by ring)) (le_of_eq (by ring))
  have zc := z.mono (e' := 𝐮 * (617 / 1000) + η) (M' := 617 / 1000)
    (by simp only [unitRoundoff64]; linarith) hXX
  have r := sinR_AB _ _ zc
  have v := (AB.mul z hx (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (by linarith)).mono (e' := 2001 / 1000 * 𝐮 * X ^ 3 + 3 * η) (M' := X ^ 3)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (le_of_eq (by ring))
  have H := (AB.mul zc r (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon])
    (by norm_num [unitRoundoff64])).mono (e' := 𝐮 / 30)
    (by norm_num [unitRoundoff64, multiplicationUnderflowEpsilon]) le_rfl
  have K := (AB.add c1 H (by norm_num) (by norm_num [unitRoundoff64])).mono (e' := 21 / 100 * 𝐮)
    (by norm_num [unitRoundoff64]) le_rfl
  have L := (AB.mul v K (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith)
    (by norm_num [unitRoundoff64])).mono (e' := 3 / 4 * 𝐮 * X ^ 3 + 16 * 𝐮 * 𝐮 * X)
    (by simp only [unitRoundoff64, multiplicationUnderflowEpsilon]; linarith) le_rfl
  exact ⟨_, L, by linarith⟩

#print axioms LW_AB

end Library.Numerics.Float64.Trig.TrigSinDirect
