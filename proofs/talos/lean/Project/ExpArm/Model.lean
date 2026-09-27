/- Copyright (c) 2018-2025, Arm Limited.  SPDX-License-Identifier: MIT -/
import Interpreter.Wasm.IEEE64
import LeanExe.Lib.Transcendental.ExpArm.Table

namespace Project.ExpArm

open Wasm.IEEE64

def table : Array UInt64 := LeanExe.Lib.Transcendental.ExpArm.table

def rescale (tmp scaleBits kBits : UInt64) : UInt64 :=
  if kBits &&& 0x80000000 == 0 then
    let scale := scaleBits - ((1009 : UInt64) <<< 52)
    mul 0x7F00000000000000 (add scale (mul scale tmp))
  else
    let scale := scaleBits + ((1022 : UInt64) <<< 52)
    let y := add scale (mul scale tmp)
    let rounded := if y < 0x3FF0000000000000 then
      let lo := add (sub scale y) (mul scale tmp)
      let hi := add 0x3FF0000000000000 y
      let lo := add (add (sub 0x3FF0000000000000 hi) y) lo
      sub (add hi lo) 0x3FF0000000000000
    else y
    mul 0x0010000000000000 rounded

/-- Binary64 exponential, with round-to-nearest arithmetic and canonical NaNs. -/
def exp (x : UInt64) : UInt64 :=
  let magnitude := x &&& 0x7FFFFFFFFFFFFFFF
  if magnitude < 0x3C90000000000000 then 0x3FF0000000000000
  else if magnitude >= 0x4090000000000000 then
    if magnitude > 0x7FF0000000000000 then 0x7FF8000000000000
    else if x >>> 63 != 0 then 0
    else 0x7FF0000000000000
  else
    let z := mul 0x40671547652B82FE x
    let kBits := add z 0x4338000000000000
    let kd := sub kBits 0x4338000000000000
    let r := add (add x (mul kd 0xBF762E42FEFA0000))
      (mul kd 0xBD0CF79ABC9E3B3A)
    let index := (2 * (kBits &&& 127)).toNat
    let tail := table[index]!
    let scale := table[index + 1]! + (kBits <<< 45)
    let r2 := mul r r
    let p := mul r2 (add 0x3FDFFFFFFFFFFDBD (mul r 0x3FC555555555543C))
    let q := mul (mul r2 r2)
      (add 0x3FA55555CF172B91 (mul r 0x3F81111167A4D017))
    let tmp := add (add (add tail r) p) q
    if magnitude >= 0x4080000000000000 then rescale tmp scale kBits
    else add scale (mul scale tmp)

end Project.ExpArm
