import CodeLib.IEEE64.Roundoff

namespace Project.ProofKit.F64Rational

def decode (word : UInt64) : ℚ :=
  (Wasm.IEEE64.scaledValue word : ℚ)/(2:ℚ)^1074

theorem decode_cast (word : UInt64) : (decode word : ℝ) = CodeLib.IEEE64.value word := by
  simp [decode, CodeLib.IEEE64.value]

end Project.ProofKit.F64Rational
