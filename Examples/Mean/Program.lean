namespace Examples.Mean

/-- The arithmetic mean, summed from the left in binary64.  It is NaN for an
empty array. -/
def mean (xs : Array Float) : Float := xs.foldl (· + ·) 0.0 / xs.size.toUInt64.toFloat

end Examples.Mean
