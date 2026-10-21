import Verified.Reflect.Command

namespace Verified.Examples.ScalarComposition

def divide (x y : UInt64) : UInt64 := x / y + x % y

def choose (x y : UInt64) : UInt64 :=
  if x < y then divide y x else divide x y

def sum (n acc : UInt64) : UInt64 :=
  if n = 0 then acc else sum (n - 1) (acc + n)
termination_by n.toNat
decreasing_by
  rename_i hn
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
  omega

def shiftedSum (n : UInt64) : UInt64 := choose (sum n 7) 13

def scale (x : Float) : Float := if x < 0 then -x else x * 1.5

def twice (x : Float) : Float := scale (scale x)

def round32 (x : Float32) : Float32 := if x < 0 then -x else LeanExe.Float32.nearest x

def bits32 (bits : UInt64) : UInt64 := (round32 (Float32.ofBits bits.toUInt32)).toBits.toUInt64

verified_compile compiled := [divide, choose, sum, shiftedSum, scale, twice, round32, bits32]

#print axioms compiled.divide.pure
#print axioms compiled.choose.pure
#print axioms compiled.sum.pure
#print axioms compiled.shiftedSum.pure
#print axioms compiled.scale.pure
#print axioms compiled.twice.pure
#print axioms compiled.round32.pure
#print axioms compiled.bits32.pure

end Verified.Examples.ScalarComposition
