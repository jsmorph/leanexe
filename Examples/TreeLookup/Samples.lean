namespace Examples.TreeLookup

/-- A search tree with keys 50, 30, 70, 20, 40, 60, and 80 in breadth-first order, each with ten
times its key as its value. -/
def tree : List UInt64 := [50, 500, 30, 300, 70, 700, 20, 200, 40, 400, 60, 600, 80, 800]

def samples : List (Array UInt64) :=
  ([50, 30, 70, 20, 40, 60, 80, 55, 25, 0, 18446744073709551615].map fun q =>
    (q :: tree).toArray) ++
  [ -- Keys out of search-tree order: 9 is in the left subtree of 5, so a search for it misses.
    #[9, 5, 1, 7, 2, 3, 4, 9, 6, 8, 10, 11, 12, 13, 14],
    -- A key equal to the query in the subtree the search does not enter.
    #[40, 50, 1, 60, 2, 30, 3, 40, 4, 70, 5, 40, 6, 80, 7],
    -- Unsigned comparison: 2^63 is greater than 50 and 70, so the search goes right twice.
    #[9223372036854775808, 50, 500, 30, 300, 70, 700, 20, 200, 40, 400, 60, 600,
      9223372036854775808, 800],
    -- A matched value of 0.
    #[50, 50, 0, 30, 300, 70, 700, 20, 200, 40, 400, 60, 600, 80, 800],
    -- The query equals the keys of the root and of a leaf below it; the root matches first.
    #[50, 50, 1, 30, 2, 70, 3, 20, 4, 40, 5, 60, 6, 50, 7],
    -- Keys and values of 2^40 or more.
    ((1099511627816 :: tree.map (· + 1099511627776))).toArray,
    -- A miss at the left subtree's right leaf: 35 goes left, then right, and misses.
    (35 :: tree).toArray,
    #[], #[50], (50 :: tree.take 13).toArray, (50 :: tree ++ [0]).toArray]

end Examples.TreeLookup
