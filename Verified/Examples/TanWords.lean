import Verified.Examples.Tan
import Verified.Examples.TrigKernelWords

/-!
`Tan.kernelTan` on words: the polynomial part, shared by both forms, and the two forms selected by
the high word, below `0x3FE59428` (`|x| < 0.67434`) and from it on.
-/

namespace Verified.Examples.TanWords

open CodeLib.IEEE64 LeanExe.ProofKit TrigKernelWords

def wT0 : UInt64 := 0x3FD5555555555563
def wT1 : UInt64 := 0x3FC111111110FE7A
def wT2 : UInt64 := 0x3FABA1BA1BB341FE
def wT3 : UInt64 := 0x3F9664F48406D637
def wT4 : UInt64 := 0x3F8226E3E96E8493
def wT5 : UInt64 := 0x3F6D6D22C9560328
def wT6 : UInt64 := 0x3F57DBC8FEE08315
def wT7 : UInt64 := 0x3F4344D8F2F26501
def wT8 : UInt64 := 0x3F3026F71A8D1068
def wT9 : UInt64 := 0x3F147E88A03792A6
def wT10 : UInt64 := 0x3F12B80F32F0A7E9
def wT11 : UInt64 := 0xBEF375CBDB605373
def wT12 : UInt64 := 0x3EFB2A7074BF7AD4
def wpio4 : UInt64 := 0x3FE921FB54442D18
def wpio4lo : UInt64 := 0x3C81A62633145C07
def negZero : UInt64 := 0x8000000000000000
def negOne : UInt64 := 0xBFF0000000000000
def two : UInt64 := 0x4000000000000000

/-- A word with its NaN patterns made canonical, as `Float.ofBits` reads it. -/
def canon (m : UInt64) : UInt64 := if Wasm.IEEE64.isNaN m then Wasm.IEEE64.canonicalNaN else m

/-- `T1 + T2 z + ... + T12 z ^ 11` as the kernel evaluates it, `r + v` with `w = z * z`. -/
def polyR (z : UInt64) : UInt64 :=
  let w := Wasm.IEEE64.mul z z
  Wasm.IEEE64.add
    (Wasm.IEEE64.add wT1 (Wasm.IEEE64.mul w (Wasm.IEEE64.add wT3 (Wasm.IEEE64.mul w
      (Wasm.IEEE64.add wT5 (Wasm.IEEE64.mul w (Wasm.IEEE64.add wT7 (Wasm.IEEE64.mul w
        (Wasm.IEEE64.add wT9 (Wasm.IEEE64.mul w wT11))))))))))
    (Wasm.IEEE64.mul z (Wasm.IEEE64.add wT2 (Wasm.IEEE64.mul w (Wasm.IEEE64.add wT4
      (Wasm.IEEE64.mul w (Wasm.IEEE64.add wT6 (Wasm.IEEE64.mul w (Wasm.IEEE64.add wT8
        (Wasm.IEEE64.mul w (Wasm.IEEE64.add wT10 (Wasm.IEEE64.mul w wT12)))))))))))

/-- The correction `r` with `tan (x + y) ≈ x + r`. -/
def corrW (x y : UInt64) : UInt64 :=
  let z := Wasm.IEEE64.mul x x
  let s := Wasm.IEEE64.mul z x
  Wasm.IEEE64.add
    (Wasm.IEEE64.add y (Wasm.IEEE64.mul z (Wasm.IEEE64.add (Wasm.IEEE64.mul s (polyR z)) y)))
    (Wasm.IEEE64.mul wT0 s)

/-- The kernel below `0x3FE59428`: `x + r`, or `-1/(x + r)` by the compensated reciprocal. -/
def smallW (x y : UInt64) (odd : Bool) : UInt64 :=
  let r := corrW x y
  let w := Wasm.IEEE64.add x r
  if !odd then w
  else
    let z := canon (w &&& 0xFFFFFFFF00000000)
    let v := Wasm.IEEE64.sub r (Wasm.IEEE64.sub z x)
    let a := Wasm.IEEE64.div negOne w
    let t := canon (a &&& 0xFFFFFFFF00000000)
    let s := Wasm.IEEE64.add one (Wasm.IEEE64.mul t z)
    Wasm.IEEE64.add t (Wasm.IEEE64.mul a (Wasm.IEEE64.add s (Wasm.IEEE64.mul t v)))

/-- The argument `π/4 - |x + y|` of the kernel from `0x3FE59428` on. -/
def bigArg (x y : UInt64) : UInt64 :=
  if x >>> 32 >>> 31 == 1 then
    Wasm.IEEE64.add (Wasm.IEEE64.sub wpio4 (Wasm.IEEE64.sub negZero x))
      (Wasm.IEEE64.sub wpio4lo (Wasm.IEEE64.sub negZero y))
  else Wasm.IEEE64.add (Wasm.IEEE64.sub wpio4 x) (Wasm.IEEE64.sub wpio4lo y)

/-- The kernel from `0x3FE59428` on: `±(v - 2 (x' - (w ^ 2/(w + v) - r)))`. -/
def bigW (x y : UInt64) (odd : Bool) : UInt64 :=
  let x' := bigArg x y
  let r := corrW x' 0
  let w := Wasm.IEEE64.add x' r
  let v := if odd then negOne else one
  let sign := if x >>> 32 >>> 31 == 1 then negOne else one
  Wasm.IEEE64.mul sign (Wasm.IEEE64.sub v (Wasm.IEEE64.mul two (Wasm.IEEE64.sub x'
    (Wasm.IEEE64.sub (Wasm.IEEE64.div (Wasm.IEEE64.mul w w) (Wasm.IEEE64.add w v)) r))))

theorem toBits_ite (c : Prop) [Decidable c] (a b : Float) :
    (if c then a else b).toBits = if c then a.toBits else b.toBits := by
  split <;> rfl

theorem const_bits :
    (Float.ofBits 0x3FD5555555555563).toBits = wT0 ∧
      (Float.ofBits 0x3FC111111110FE7A).toBits = wT1 ∧
      (Float.ofBits 0x3FABA1BA1BB341FE).toBits = wT2 ∧
      (Float.ofBits 0x3F9664F48406D637).toBits = wT3 ∧
      (Float.ofBits 0x3F8226E3E96E8493).toBits = wT4 ∧
      (Float.ofBits 0x3F6D6D22C9560328).toBits = wT5 ∧
      (Float.ofBits 0x3F57DBC8FEE08315).toBits = wT6 ∧
      (Float.ofBits 0x3F4344D8F2F26501).toBits = wT7 ∧
      (Float.ofBits 0x3F3026F71A8D1068).toBits = wT8 ∧
      (Float.ofBits 0x3F147E88A03792A6).toBits = wT9 ∧
      (Float.ofBits 0x3F12B80F32F0A7E9).toBits = wT10 ∧
      (Float.ofBits 0xBEF375CBDB605373).toBits = wT11 ∧
      (Float.ofBits 0x3EFB2A7074BF7AD4).toBits = wT12 ∧
      (Float.ofBits 0x3FE921FB54442D18).toBits = wpio4 ∧
      (Float.ofBits 0x3C81A62633145C07).toBits = wpio4lo ∧
      (0.0 : Float).toBits = 0 ∧ (1.0 : Float).toBits = one ∧
      (-1.0 : Float).toBits = negOne ∧ (2.0 : Float).toBits = two := by
  simp only [F64Bits.toBits_ofBits]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem big_iff (x : Float) :
    ((x.toBits >>> 32 &&& 0x7fffffff) ≥ 0x3FE59428) = (x.toBits >>> 32 &&& 0x7fffffff ≥ 0x3FE59428) :=
  rfl

/-- The kernel below `0x3FE59428` on words. -/
theorem kernelTan_small_bits (x y : Float) (odd : Bool)
    (h : ¬ ((x.toBits >>> 32) &&& 0x7fffffff) ≥ 0x3FE59428) :
    (Tan.kernelTan x y odd).toBits = smallW x.toBits y.toBits odd := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, -, -, -, h1, hn1, -⟩ := const_bits
  unfold Tan.kernelTan smallW corrW polyR
  simp only [h, decide_false, Bool.false_eq_true, ite_false]
  cases odd <;> simp only [F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_add,
    F64Bits.toBits_div, F64Bits.toBits_ofBits, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11,
    c12, h1, hn1, Bool.not_false, Bool.not_true, ite_true, ite_false, Bool.false_eq_true, canon]

/-- The kernel from `0x3FE59428` on, on words. -/
theorem kernelTan_big_bits (x y : Float) (odd : Bool)
    (h : ((x.toBits >>> 32) &&& 0x7fffffff) ≥ 0x3FE59428) :
    (Tan.kernelTan x y odd).toBits = bigW x.toBits y.toBits odd := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, p4, p4l, h0, h1, hn1, h2⟩ :=
    const_bits
  unfold Tan.kernelTan bigW bigArg corrW polyR
  simp only [h, decide_true, ite_true]
  by_cases hs : x.toBits >>> 32 >>> 31 == 1 <;> cases odd <;>
    simp only [hs, ite_true, ite_false, Bool.false_eq_true, F64Bits.toBits_sub,
      F64Bits.toBits_mul, F64Bits.toBits_add, F64Bits.toBits_div, F64Bits.toBits_neg, toBits_ite,
      c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, p4, p4l, h0, h1, hn1, h2, negZero]

#print axioms const_bits
#print axioms kernelTan_small_bits
#print axioms kernelTan_big_bits

end Verified.Examples.TanWords
