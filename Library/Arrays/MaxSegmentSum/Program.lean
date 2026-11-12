/-! Kadane's algorithm for the maximum segment sum in the verified compiler's dialect: one pass
over an array of `Int64` values from the left.  The sums wrap modulo `2^64`, and `Proof.lean` proves
that `mss` computes `maxSegmentSum` of the values read as integers when their absolute values sum
to less than `2^63`. -/

namespace Library.Arrays.MaxSegmentSum

/-- The maximum segment sum of `xs`, the empty segment included.  The state `(best, ending)` holds
the greatest sum of a segment of the elements read so far and the greatest sum of a suffix of them,
the empty suffix included, and it starts at `(0, 0)`.  An element `x` sets `ending` to
`max (ending + x) 0` and then `best` to `max best ending`. -/
def mss (xs : Array Int64) : Int64 :=
  (xs.foldl (fun (state : Int64 × Int64) x =>
    let ending := max (state.2 + x) 0
    (max state.1 ending, ending)) ((0 : Int64), (0 : Int64))).1

end Library.Arrays.MaxSegmentSum
