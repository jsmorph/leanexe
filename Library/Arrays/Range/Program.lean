module

public import LeanExe.Dialect.Loop
public import LeanExe.Dialect.Build

@[expose] public section

namespace Library.Arrays.Range

def evens (n : UInt64) : Array UInt64 :=
  LeanExe.loop n (LeanExe.build 0 fun _ => 0) fun i acc => acc.push (2 * i)

end Library.Arrays.Range
