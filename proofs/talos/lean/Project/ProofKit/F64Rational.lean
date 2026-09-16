import CodeLib.IEEE64.Roundoff

namespace Project.ProofKit.F64Rational

def decode (word : UInt64) : ℚ :=
  (Wasm.IEEE64.scaledValue word : ℚ)/(2:ℚ)^1074

theorem decode_cast (word : UInt64) : (decode word : ℝ) = CodeLib.IEEE64.value word := by
  simp [decode, CodeLib.IEEE64.value]

theorem magnitude (word : UInt64) (bound : ℚ) (h : |decode word| ≤ bound) :
    |CodeLib.IEEE64.value word| ≤ (bound : ℝ) := by
  have hc : ((|decode word| : ℚ):ℝ) ≤ (bound : ℝ) := Rat.cast_le.mpr h
  simpa [decode_cast] using hc

end Project.ProofKit.F64Rational
