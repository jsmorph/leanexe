import Library.Numerics.Float64.Tanh.Compiled
import LeanExe.ProofKit.F64Bits
import LeanExe.ProofKit.F64Convert

/-!
The kernel of fdlibm's `expm1`, `Tanh.expm1Kernel`, on bit patterns.  `kernel x c neg m` applies
Talos's `IEEE64` operations in the order of the Lean definition, and `kernel_bits` states that it
gives the bits of `Tanh.expm1Kernel`.  The words computed from `m` pass through `ofBitsWord`, the
bits of `Float.ofBits`, which replaces a NaN pattern by the canonical NaN.
-/

namespace Library.Numerics.Float64.Tanh.Expm1Words
open Wasm.IEEE64 (add sub mul div lt)

def Q1 : UInt64 := 0xBFA11111111110F4
def Q2 : UInt64 := 0x3F5A01A019FE5585
def Q3 : UInt64 := 0xBF14CE199EAADBB7
def Q4 : UInt64 := 0x3ED0CFCA86E65239
def Q5 : UInt64 := 0xBE8AFDB76E09C32D

def one : UInt64 := 0x3FF0000000000000
def half : UInt64 := 0x3FE0000000000000
def two : UInt64 := 0x4000000000000000
def three : UInt64 := 0x4008000000000000
def six : UInt64 := 0x4018000000000000
def negTwo : UInt64 := 0xC000000000000000
def negQuarter : UInt64 := 0xBFD0000000000000
def maxPower : UInt64 := 0x7FE0000000000000

/-- The bits of `Float.ofBits w`. -/
def ofBitsWord (w : UInt64) : UInt64 :=
  if Wasm.IEEE64.isNaN w then Wasm.IEEE64.canonicalNaN else w

/-- `x / 2`. -/
def hfx (x : UInt64) : UInt64 := mul half x

/-- `x² / 2`, rounded twice. -/
def hxs (x : UInt64) : UInt64 := mul x (hfx x)

/-- fdlibm's `r1`, the polynomial in `hxs`. -/
def r1 (x : UInt64) : UInt64 :=
  add one (mul (hxs x) (add Q1 (mul (hxs x) (add Q2 (mul (hxs x)
    (add Q3 (mul (hxs x) (add Q4 (mul (hxs x) Q5)))))))))

/-- fdlibm's `t = 3 - r1 x / 2`. -/
def tt (x : UInt64) : UInt64 := sub three (mul (r1 x) (hfx x))

/-- fdlibm's `e = hxs (r1 - t)/(6 - x t)`. -/
def e0 (x : UInt64) : UInt64 :=
  mul (hxs x) (div (sub (r1 x) (tt x)) (sub six (mul x (tt x))))

/-- The corrected remainder `x (e - c) - c - hxs` of the paths with `k ≠ 0`. -/
def e2 (x c : UInt64) : UInt64 := sub (sub (mul x (sub (e0 x) c)) c) (hxs x)

/-- `2 ^ k` for `k = ±m`. -/
def twopk (neg : Bool) (m : UInt64) : UInt64 :=
  ofBitsWord ((if neg then 0x3ff - m else 0x3ff + m) <<< 52)

/-- `1 - 2 ^ -m` for `2 ≤ m < 20`. -/
def oneMinus (m : UInt64) : UInt64 :=
  ofBitsWord (((0x3ff00000 : UInt64) - (0x200000 >>> m)) <<< 32)

/-- `2 ^ -m` for `20 ≤ m ≤ 56`. -/
def powerNeg (m : UInt64) : UInt64 := ofBitsWord (((0x3ff : UInt64) - m) <<< 52)

/-- The kernel on bit patterns, with the branches of `Tanh.expm1Kernel`. -/
def kernel (x c : UInt64) (neg : Bool) (m : UInt64) : UInt64 :=
  if m == 0 then sub x (sub (mul x (e0 x)) (hxs x))
  else if m == 1 then
    if neg then sub (mul half (sub x (e2 x c))) half
    else if lt x negQuarter then mul negTwo (sub (e2 x c) (add x half))
    else add one (mul two (sub x (e2 x c)))
  else if neg || m > 56 then
    if !neg && m == 1024 then
      sub (mul (mul (sub one (sub (e2 x c) x)) two) (ofBitsWord maxPower)) one
    else sub (mul (sub one (sub (e2 x c) x)) (twopk neg m)) one
  else if m < 20 then mul (sub (oneMinus m) (sub (e2 x c) x)) (twopk neg m)
  else mul (add (sub x (add (e2 x c) (powerNeg m))) one) (twopk neg m)

theorem float_ofBits (w : UInt64) : (Float.ofBits w).toBits = ofBitsWord w :=
  LeanExe.ProofKit.F64Bits.toBits_ofBits w

theorem kernel_bits (x c : Float) (neg : Bool) (m : UInt64) :
    (Tanh.expm1Kernel x c neg m).toBits = kernel x.toBits c.toBits neg m := by
  open LeanExe.ProofKit in
  unfold Tanh.expm1Kernel kernel
  by_cases h0 : m == 0
  · simp only [h0, ite_true, F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_div,
      F64Bits.toBits_add, float_ofBits]
    rfl
  · simp only [h0, Bool.false_eq_true, ite_false]
    by_cases h1 : m == 1
    · simp only [h1, ite_true]
      cases neg
      · simp only [Bool.false_eq_true, ite_false]
        have hlt : decide (x < -0.25) = lt x.toBits negQuarter := by
          rw [F64Bits.decide_lt]
          rfl
        by_cases hx : x < -0.25
        · have hl : lt x.toBits negQuarter = true := by rw [← hlt]; simp [hx]
          simp only [hx, hl, ite_true, F64Bits.toBits_sub, F64Bits.toBits_mul,
            F64Bits.toBits_div, F64Bits.toBits_add, float_ofBits]
          rfl
        · have hl : lt x.toBits negQuarter = false := by rw [← hlt]; simp [hx]
          simp only [hx, hl, ite_false, Bool.false_eq_true, F64Bits.toBits_sub,
            F64Bits.toBits_mul, F64Bits.toBits_div, F64Bits.toBits_add, float_ofBits]
          rfl
      · simp only [ite_true, F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_div,
          F64Bits.toBits_add, float_ofBits]
        rfl
    · simp only [h1, Bool.false_eq_true, ite_false]
      by_cases h56 : (neg || m > 56) = true
      · simp only [h56, ite_true]
        by_cases hmax : (!neg && m == 1024) = true
        · simp only [hmax, ite_true, F64Bits.toBits_sub, F64Bits.toBits_mul,
            F64Bits.toBits_div, F64Bits.toBits_add, float_ofBits]
          rfl
        · simp only [hmax, Bool.false_eq_true, ite_false, F64Bits.toBits_sub,
            F64Bits.toBits_mul, F64Bits.toBits_div, F64Bits.toBits_add, float_ofBits]
          rfl
      · simp only [h56, Bool.false_eq_true, ite_false]
        by_cases h20 : m < 20
        · simp only [h20, ite_true, F64Bits.toBits_sub, F64Bits.toBits_mul,
            F64Bits.toBits_div, F64Bits.toBits_add, float_ofBits]
          rfl
        · simp only [h20, ite_false, F64Bits.toBits_sub, F64Bits.toBits_mul,
            F64Bits.toBits_div, F64Bits.toBits_add, float_ofBits]
          rfl

#print axioms kernel_bits

end Library.Numerics.Float64.Tanh.Expm1Words
