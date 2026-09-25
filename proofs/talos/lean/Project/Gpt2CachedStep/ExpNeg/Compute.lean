import LeanExe.Models.Gpt2.Numerics

namespace Project.Gpt2CachedStep.ExpNeg

def reduceStep (state : UInt32 × Nat) : UInt32 × Nat :=
  if state.1 > 0xBF800000 then (LeanExe.Float32.mulBits state.1 0x3F000000, state.2 + 1)
  else state

def reducePrefix (input : UInt32) (count : Nat) : UInt32 × Nat :=
  (List.range count).foldl (fun state _ => reduceStep state) (input, 0)

def squarePrefix (input : UInt32) (count : Nat) : UInt32 :=
  (List.range count).foldl (fun value _ => LeanExe.Float32.mulBits value value) input

def PolynomialError.coefficient (i : Nat) : UInt32 :=
  [0x274A963C, 0x29573F9F, 0x2B573F9F, 0x2D49CBA5, 0x2F309231, 0x310F76C7,
   0x32D7322B, 0x3493F27E, 0x3638EF1D, 0x37D00D01, 0x39500D01, 0x3AB60B61,
   0x3C088889, 0x3D2AAAAB, 0x3E2AAAAB, 0x3F000000, 0x3F800000, 0x3F800000][i]!

end Project.Gpt2CachedStep.ExpNeg
