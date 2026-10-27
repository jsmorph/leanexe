import Library.Numerics.Decimal.ParseFloat.Program
import Library.Numerics.Decimal.PrintFloat.Program
import LeanExe.Dialect.Bytes

namespace Demos.RunningSumFp

def stripCR (input : Array UInt64) : Array UInt64 :=
  let length := input.size.toUInt64
  if length > 0 && input[(length - 1).toNat]! == 13 then
    LeanExe.build (length - 1) fun i => input[i.toNat]!
  else input

def parse (input : Array UInt64) : Bool × Float :=
  let parsed := Library.Numerics.Decimal.ParseFloat.parse64 true (stripCR input)
  (parsed.1, Float.ofBits parsed.2)

def render (value : Float) : LeanExe.Bytes :=
  let text := Library.Numerics.Decimal.PrintFloat.print64 value.toBits
  let length := text.size.toUInt64
  LeanExe.Bytes.build (length + 1) fun i => if i == length then 10 else text[i.toNat]!

end Demos.RunningSumFp
