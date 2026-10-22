import LeanExe.Dialect.Loop
import LeanExe.Dialect.Build

namespace Library.Arrays.Range

def evens (n : UInt64) : Array UInt64 :=
  LeanExe.loop n (LeanExe.build 0 fun _ => 0) fun i acc => acc.push (2 * i)

end Library.Arrays.Range
