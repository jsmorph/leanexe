import Interpreter.Wasm.IEEE64

/-! The specifications: WebAssembly's signed conversions in Talos's IEEE 754 functions.
`convertI64S` rounds the integer of a word, read in two's complement, to the nearest float with
ties to even.  `truncSatI64S` truncates a float toward zero and saturates at `-2^63` and
`2^63 - 1`, with 0 for NaN, `-2^63` for negative infinity, and `2^63 - 1` for positive
infinity. -/

namespace Examples.Convert

/-- `f64.convert_i64_s` of `a`'s word. -/
def expectedToDouble (a : Int64) : UInt64 := Wasm.IEEE64.convertI64S a.toUInt64

/-- `f32.convert_i64_s` of `a`'s word. -/
def expectedToSingle (a : Int64) : UInt32 := Wasm.IEEE32.convertI64S a.toUInt64

/-- `i64.trunc_sat_f64_s` of `x`'s bits. -/
def expectedOfDouble (x : Float) : UInt64 := Wasm.IEEE64.truncSatI64S x.toBits

/-- `i64.trunc_sat_f32_s` of `x`'s bits. -/
def expectedOfSingle (x : Float32) : UInt64 := Wasm.IEEE32.truncSatI64S x.toBits

/-- `i64.trunc_sat_f64_s` of the product of `f64.convert_i64_s` of `a`'s word and `k`. -/
def expectedScale (a : Int64) (k : Float) : UInt64 :=
  Wasm.IEEE64.truncSatI64S (Wasm.IEEE64.mul (Wasm.IEEE64.convertI64S a.toUInt64) k.toBits)

end Examples.Convert
