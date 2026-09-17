import Interpreter.Wasm.IEEE32
import Interpreter.Wasm.IEEE64

namespace Project.WGSL.Precision

/-- Finite-input conversion: one nearest/even rounding, preserving subnormals.
The total word function is not an IEEE NaN/infinity conversion specification. -/
def demote (a : UInt64) : UInt32 :=
  Wasm.IEEE32.roundDyadicMagnitude (Wasm.IEEE64.sign a) (Wasm.IEEE64.scaledMagnitude a) 925

/-- Exact promotion model on finite binary32 input words. -/
def promote (a : UInt32) : UInt64 :=
  Wasm.IEEE64.roundScaledMagnitude (Wasm.IEEE32.sign a) (Wasm.IEEE32.scaledMagnitude a * 2^925)

end Project.WGSL.Precision
