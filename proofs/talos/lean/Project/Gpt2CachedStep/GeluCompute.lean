import LeanExe.Models.Gpt2.Numerics

namespace Project.Gpt2CachedStep.GeluArgumentError

def square (a : UInt32) : UInt32 := LeanExe.Float32.mulBits a a
def weighted (a : UInt32) : UInt32 := LeanExe.Float32.mulBits (square a) 0x3D372713
def factor (a : UInt32) : UInt32 := LeanExe.Float32.addBits (weighted a) 0x3F800000
def product (a : UInt32) : UInt32 := LeanExe.Float32.mulBits (factor a) a
def magnitude (a : UInt32) : UInt32 := LeanExe.Float32.mulBits (product a) 0x3FCC422A

end Project.Gpt2CachedStep.GeluArgumentError

namespace Project.Gpt2CachedStep.GeluError
open LeanExe.Models.Gpt2

def argument (a : UInt32) : UInt32 := GeluArgumentError.magnitude a ||| 0x80000000
def exponential (a : UInt32) : UInt32 := expNeg (argument a)
def denominator (a : UInt32) : UInt32 := LeanExe.Float32.addBits 0x3F800000 (exponential a)
def positivePart (a : UInt32) : UInt32 := LeanExe.Float32.divBits a (denominator a)
def numerator (a : UInt32) : UInt32 := LeanExe.Float32.mulBits (a ||| 0x80000000) (exponential a)
def negativePart (a : UInt32) : UInt32 := LeanExe.Float32.divBits (numerator a) (denominator a)

end Project.Gpt2CachedStep.GeluError
