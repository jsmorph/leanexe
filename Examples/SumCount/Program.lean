namespace Examples.SumCount

def sumCount (xs : Array UInt64) : Array UInt64 :=
  #[xs.foldl (· + ·) 0, xs.size.toUInt64]

end Examples.SumCount
