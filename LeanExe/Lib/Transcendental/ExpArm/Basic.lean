/- Copyright (c) 2018-2025, Arm Limited.  SPDX-License-Identifier: MIT -/
import LeanExe.Float64
import LeanExe.Lib.Transcendental.ExpArm.Table

namespace LeanExe.Lib.Transcendental

open Float64

def ExpArm.rescale (tmp scaleBits kBits : UInt64) : UInt64 :=
  if kBits &&& 0x80000000 == 0 then
    let scale := scaleBits - ((1009 : UInt64) <<< 52)
    mulBits 0x7F00000000000000 (addBits scale (mulBits scale tmp))
  else
    let scale := scaleBits + ((1022 : UInt64) <<< 52)
    let y := addBits scale (mulBits scale tmp)
    let rounded := if y < 0x3FF0000000000000 then
      let lo := addBits (subBits scale y) (mulBits scale tmp)
      let hi := addBits 0x3FF0000000000000 y
      let lo := addBits (addBits (subBits 0x3FF0000000000000 hi) y) lo
      subBits (addBits hi lo) 0x3FF0000000000000
    else y
    mulBits 0x0010000000000000 rounded

/-- Binary64 exponential, with round-to-nearest arithmetic and canonical NaNs. -/
def exp (x : UInt64) : UInt64 :=
  let magnitude := x &&& 0x7FFFFFFFFFFFFFFF
  if magnitude < 0x3C90000000000000 then 0x3FF0000000000000
  else if magnitude >= 0x4090000000000000 then
    if magnitude > 0x7FF0000000000000 then 0x7FF8000000000000
    else if x >>> 63 != 0 then 0
    else 0x7FF0000000000000
  else
    let z := mulBits 0x40671547652B82FE x
    let kBits := addBits z 0x4338000000000000
    let kd := subBits kBits 0x4338000000000000
    let r := addBits (addBits x (mulBits kd 0xBF762E42FEFA0000))
      (mulBits kd 0xBD0CF79ABC9E3B3A)
    let index := (2 * (kBits &&& 127)).toNat
    let tail := ExpArm.table[index]!
    let scale := ExpArm.table[index + 1]! + (kBits <<< 45)
    let r2 := mulBits r r
    let p := mulBits r2 (addBits 0x3FDFFFFFFFFFFDBD (mulBits r 0x3FC555555555543C))
    let q := mulBits (mulBits r2 r2)
      (addBits 0x3FA55555CF172B91 (mulBits r 0x3F81111167A4D017))
    let tmp := addBits (addBits (addBits tail r) p) q
    if magnitude >= 0x4080000000000000 then ExpArm.rescale tmp scale kBits
    else addBits scale (mulBits scale tmp)

end LeanExe.Lib.Transcendental
