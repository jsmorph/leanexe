namespace Examples.PairSum

/-- The sum of `a` and `b`, computed by folding over a temporary array. -/
def pairSum (a b : UInt64) : UInt64 := #[a, b].foldl (· + ·) 0

end Examples.PairSum
