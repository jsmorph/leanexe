namespace Examples.RunningMax

def samples : List (Array UInt64) :=
  [#[], #[0], #[7], #[18446744073709551615],
    -- Increasing, decreasing, mixed, and equal entries.
    #[1, 2, 3, 4], #[4, 3, 2, 1], #[3, 1, 4, 1, 5, 9, 2, 6], #[5, 5, 5], #[0, 0, 0],
    -- A tie with the largest so far, then a new largest.
    #[2, 9, 9, 3, 10],
    -- The largest word first and last.
    #[18446744073709551615, 0, 1], #[0, 18446744073709551615],
    -- Unsigned comparison: 2^63 is greater than 2^63 − 1.
    #[9223372036854775808, 9223372036854775807], #[9223372036854775807, 9223372036854775808],
    -- Words around 2^32.
    #[4294967296, 4294967295, 4294967297],
    -- Twenty entries, `37 i mod 23` for `i` from 0 to 19.
    ((List.range 20).map fun i => UInt64.ofNat (37 * i % 23)).toArray,
    -- One hundred entries, `7919 i mod 1000` for `i` from 0 to 99, longer than every sample above.
    ((List.range 100).map fun i => UInt64.ofNat (7919 * i % 1000)).toArray,
    -- Lengths 6, 7, and 15, which leave remainders 6 and 7 after division by 8.
    #[1, 6, 2, 5, 3, 4], #[10, 3, 11, 2, 12, 1, 13],
    #[9, 2, 9, 10, 1, 1, 8, 12, 3, 12, 0, 15, 4, 7, 15],
    -- Five thousand entries, `i mod 1000` for `i` from 0 to 4999, more than a page of memory holds
    -- for the input and the result together.
    ((List.range 5000).map fun i => UInt64.ofNat (i % 1000)).toArray]

end Examples.RunningMax
