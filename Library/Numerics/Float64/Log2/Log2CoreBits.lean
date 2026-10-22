import Library.Numerics.Float64.Log2.Compiled
import Library.Numerics.Float64.Log.LogCoreBits

/-!
The word arithmetic of `Log2.log2Core`.  The reduction is that of `Log.logCore`, with the
subinterval among 64 taken from bits 46 to 51 of `tmp`, so `Library.Numerics.Float64.Log.LogCoreBits.tmpOf`, `kOf`, `zOf`, and
`kdOf` describe it.  `log2Core_eq` restates `Log2.log2Core` through `Library.Numerics.Float64.Log.LogCoreBits.reduced` and
`final2`, the arithmetic after `r`.
-/

namespace Library.Numerics.Float64.Log2.Log2CoreBits
open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Log.LogCoreBits

set_option exponentiation.threshold 4096

def index2Of (ix : UInt64) : UInt64 := (tmpOf ix >>> 46) % 64

/-- The arithmetic of `Log2.log2Core` after `r`, `kd`, and `logc`. -/
def final2 (r kd logc : Float) : Float :=
  let invln2hi := Float.ofBits 0x3FF7154765200000
  let invln2lo := Float.ofBits 0x3DE705FC2EEFA200
  let A0 := Float.ofBits 0xBFE71547652B8339
  let A1 := Float.ofBits 0x3FDEC709DC3A04BE
  let A2 := Float.ofBits 0xBFD7154764702FFB
  let A3 := Float.ofBits 0x3FD2776C50034C48
  let A4 := Float.ofBits 0xBFCEC7B328EA92BC
  let A5 := Float.ofBits 0x3FCA6225E117F92E
  let rhi := Float.ofBits (r.toBits &&& 0xFFFFFFFF00000000)
  let rlo := r - rhi
  let t1 := rhi * invln2hi
  let t2 := rlo * invln2hi + r * invln2lo
  let t3 := kd + logc
  let hi := t3 + t1
  let lo := t3 - hi + t1 + t2
  let r2 := r * r
  let r4 := r2 * r2
  let p := A0 + r * A1 + r2 * (A2 + r * A3) + r4 * (A4 + r * A5)
  lo + r2 * p + hi

theorem log2Core_eq (tab tab2 : Array UInt64) (ix : UInt64) :
    Log2.log2Core tab tab2 ix =
      final2 (reduced (Float.ofBits (zOf ix)) (Float.ofBits tab2[(2 * index2Of ix).toNat]!)
          (Float.ofBits tab2[(2 * index2Of ix + 1).toNat]!)
          (Float.ofBits tab[(2 * index2Of ix).toNat]!))
        (kdOf (kOf ix)) (Float.ofBits tab[(2 * index2Of ix + 1).toNat]!) := rfl

theorem index2_toNat (ix : UInt64) :
    (index2Of ix).toNat = (tmpOf ix).toNat / 70368744177664 % 64 := by
  simp only [index2Of, UInt64.toNat_mod, UInt64.toNat_shiftRight, UInt64.reduceToNat,
    Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow]

theorem index2_upper (ix : UInt64) (E : Int) (f : Nat) (hE1 : -51 ≤ E) (hE2 : E ≤ 2046)
    (hf : f < 4503599627370496) (hf6 : 1688849860263936 ≤ f)
    (hix : (ix.toNat : Int) = (E * 4503599627370496 + f) % 18446744073709551616) :
    (index2Of ix).toNat = f / 70368744177664 - 24 := by
  obtain ⟨-, -, ht, -⟩ := fields ix
  have hN := ix.toNat_lt
  simp only [Nat.reducePow] at hN
  rw [index2_toNat]
  omega

theorem index2_lower (ix : UInt64) (E : Int) (f : Nat) (hE1 : -51 ≤ E) (hE2 : E ≤ 2046)
    (hf6 : f < 1688849860263936)
    (hix : (ix.toNat : Int) = (E * 4503599627370496 + f) % 18446744073709551616) :
    (index2Of ix).toNat = f / 70368744177664 + 40 := by
  obtain ⟨-, -, ht, -⟩ := fields ix
  have hN := ix.toNat_lt
  simp only [Nat.reducePow] at hN
  rw [index2_toNat]
  omega

#print axioms log2Core_eq
#print axioms index2_upper
#print axioms index2_lower

end Library.Numerics.Float64.Log2.Log2CoreBits
