module

public import LeanExe.Dialect.Loop
public import LeanExe.Dialect.Build

@[expose] public section

namespace Library.Arrays.Repeat

def repeated (xs : Array UInt64) (n : UInt64) : Array UInt64 :=
  LeanExe.loop n (LeanExe.build 0 fun _ => 0) fun _ acc => acc ++ xs

end Library.Arrays.Repeat
