namespace LeanExe.Examples.ArraySemantics

def base : Array UInt64 :=
  (Array.replicate 2 (0 : UInt64)).set! 0 11

def aliasValue (a : Array UInt64) : UInt64 :=
  (a.set! 0 22)[0]! * (100 : UInt64) + a[0]!

def aliasCheck : UInt64 :=
  aliasValue base

def oobGet : UInt64 :=
  (Array.replicate 1 (0 : UInt64))[5]!

def oobSet : UInt64 :=
  ((Array.replicate 1 (0 : UInt64)).set! 5 99)[0]!

end LeanExe.Examples.ArraySemantics
