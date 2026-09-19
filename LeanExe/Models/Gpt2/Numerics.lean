import LeanExe.Float32

namespace LeanExe.Models.Gpt2

def expPolynomial (x : UInt32) : UInt32 :=
  let p17 := LeanExe.Float32.addBits (LeanExe.Float32.mulBits 0x253413C3 x) 0x274A963C
  let p16 := LeanExe.Float32.addBits (LeanExe.Float32.mulBits p17 x) 0x29573F9F
  let p15 := LeanExe.Float32.addBits (LeanExe.Float32.mulBits p16 x) 0x2B573F9F
  let p14 := LeanExe.Float32.addBits (LeanExe.Float32.mulBits p15 x) 0x2D49CBA5
  let p13 := LeanExe.Float32.addBits (LeanExe.Float32.mulBits p14 x) 0x2F309231
  let p12 := LeanExe.Float32.addBits (LeanExe.Float32.mulBits p13 x) 0x310F76C7
  let p11 := LeanExe.Float32.addBits (LeanExe.Float32.mulBits p12 x) 0x32D7322B
  let p10 := LeanExe.Float32.addBits (LeanExe.Float32.mulBits p11 x) 0x3493F27E
  let p9 := LeanExe.Float32.addBits (LeanExe.Float32.mulBits p10 x) 0x3638EF1D
  let p8 := LeanExe.Float32.addBits (LeanExe.Float32.mulBits p9 x) 0x37D00D01
  let p7 := LeanExe.Float32.addBits (LeanExe.Float32.mulBits p8 x) 0x39500D01
  let p6 := LeanExe.Float32.addBits (LeanExe.Float32.mulBits p7 x) 0x3AB60B61
  let p5 := LeanExe.Float32.addBits (LeanExe.Float32.mulBits p6 x) 0x3C088889
  let p4 := LeanExe.Float32.addBits (LeanExe.Float32.mulBits p5 x) 0x3D2AAAAB
  let p3 := LeanExe.Float32.addBits (LeanExe.Float32.mulBits p4 x) 0x3E2AAAAB
  let p2 := LeanExe.Float32.addBits (LeanExe.Float32.mulBits p3 x) 0x3F000000
  let p1 := LeanExe.Float32.addBits (LeanExe.Float32.mulBits p2 x) 0x3F800000
  LeanExe.Float32.addBits (LeanExe.Float32.mulBits p1 x) 0x3F800000

def expNeg (x : UInt32) : UInt32 := Id.run do
  if x > 0xC2800000 then return 0
  let mut reduced := x
  let mut squares := 0
  for _ in [:6] do
    if reduced > 0xBF800000 then
      reduced := LeanExe.Float32.mulBits reduced 0x3F000000
      squares := squares + 1
  let mut value := expPolynomial reduced
  for _ in [:squares] do
    value := LeanExe.Float32.mulBits value value
  return value

def gelu (x : UInt32) : UInt32 :=
  let a := x &&& 0x7FFFFFFF
  if a > 0x41000000 then
    if x < 0x80000000 then x else 0
  else
    let square := LeanExe.Float32.mulBits a a
    let factor := LeanExe.Float32.addBits (LeanExe.Float32.mulBits square 0x3D372713) 0x3F800000
    let magnitude := LeanExe.Float32.mulBits (LeanExe.Float32.mulBits factor a) 0x3FCC422A
    let e := expNeg (magnitude ||| 0x80000000)
    let denominator := LeanExe.Float32.addBits 0x3F800000 e
    if x < 0x80000000 then LeanExe.Float32.divBits a denominator
    else LeanExe.Float32.divBits (LeanExe.Float32.mulBits (a ||| 0x80000000) e) denominator

def finiteLt (left right : UInt32) : Bool :=
  if (left &&& 0x7FFFFFFF) == 0 && (right &&& 0x7FFFFFFF) == 0 then false
  else if left < 0x80000000 then
    right < 0x80000000 && left < right
  else if right < 0x80000000 then true
  else right < left

end LeanExe.Models.Gpt2
