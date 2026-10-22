import LeanExe.Dialect.Build

namespace Library.Arrays.Word

def scaled (xs : Array UInt64) (k : UInt64) : Array UInt64 :=
  LeanExe.build xs.size.toUInt64 fun i => xs[i.toNat]! * k

end Library.Arrays.Word
