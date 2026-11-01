import TestSupport.Host

/-! The inputs of the verified compiler's cases of exact cover by dancing links. -/

namespace Library.Combinatorics.DancingLinks

open TestSupport.Host

/-- The input of `n` items and the options `os`, each followed by a zero. -/
def problem (n : Nat) (os : List (List Nat)) : List UInt64 :=
  n.toUInt64 :: (os.flatMap fun o => o.map Nat.toUInt64 ++ [0])

/-- Every nonempty subset of the items `1..n`, as an option, in the order of the binary numbers
from 1 to `2^n - 1`.  Its covers are the partitions of `n` items, whose number is the Bell number
`B(n)`. -/
def subsets (n : Nat) : List UInt64 :=
  problem n ((List.range (2 ^ n - 1)).map fun m =>
    (List.range n).filter (fun i => (m + 1) / 2 ^ i % 2 = 1) |>.map (· + 1))

/-- The tilings of an `r × c` board by dominoes: the cells are items `1..rc`, row by row, and the
options are the horizontal and vertical pairs of adjacent cells. -/
def dominoes (r c : Nat) : List UInt64 :=
  let cell := fun i j => i * c + j + 1
  problem (r * c)
    ((List.range r).flatMap fun i => (List.range c).flatMap fun j =>
      (if j + 1 < c then [[cell i j, cell i (j + 1)]] else []) ++
        (if i + 1 < r then [[cell i j, cell (i + 1) j]] else []))

/-- The 4 × 4 Sudoku with no clues: items for each cell, each row and digit, each column and
digit, and each box and digit, and an option for each cell and digit.  It has 288 solutions. -/
def sudoku4 : List UInt64 :=
  problem 64 ((List.range 16).flatMap fun c => (List.range 4).map fun d =>
    let r := c / 4
    let k := c % 4
    let box := r / 2 * 2 + k / 2
    [c + 1, 17 + 4 * r + d, 33 + 4 * k + d, 49 + 4 * box + d])

/-- Langford pairs of order `n`: the items are the numbers `1..n` and the positions `n + 1..3n`,
and the option for number `k` at position `i` holds `k` and the positions `i` and `i + k + 1`.
Orders 3 and 4 have two arrangements each, and order 7 has 52, each counted with its mirror
image. -/
def langford (n : Nat) : List UInt64 :=
  problem (3 * n) ((List.range n).flatMap fun k0 =>
    let k := k0 + 1
    (List.range (2 * n)).filterMap fun i =>
      if i + k + 1 < 2 * n then some [k, n + 1 + i, n + 1 + i + k + 1] else none)

/-- Knuth's example (6) of TAOCP 7.2.2.1, with the items `a` to `g` as 1 to 7: the options
`c e`, `a d g`, `b c f`, `a d f`, `b g`, and `d e g`, whose one exact cover is the first, the
fourth, and the fifth. -/
def knuth : List UInt64 := problem 7 [[3, 5], [1, 4, 7], [2, 3, 6], [1, 4, 6], [2, 7], [4, 5, 7]]

/-- The valid inputs of `count`.  The empty array and the inputs with no items, which have the one
cover of no options; one item with no option; an option without a trailing zero; leading,
consecutive, and trailing zeros; equal options, which count as distinct; two covers of different
sizes; an item in no option;
options that lie in no cover; an option whose items are not in increasing order; Knuth's example;
the Bell numbers `B(1)` to `B(6)` and `B(10)` from all subsets, the last with 1,023 options; ten
and seventeen items with two copies of each one-item option, which have `2^10` and `2^17` covers;
an option that holds the items 1 and 65; domino tilings of boards of 2 × 20, 3 × 8, 4 × 4, and
6 × 6 cells; the empty 4 × 4 Sudoku; Langford pairs of orders 3, 4, 5, and 7, of which order 5 has
none; and 998 items with one option for each, which uses the deepest recursion that the
compiler's depth limit allows. -/
def countInputs : List (List UInt64) :=
  [[], [0], [0, 0, 0], [1], [1, 1], [2, 1, 2], [2, 1, 0, 2],
    [2, 0, 0, 1, 0, 0, 2, 0, 0], [1, 1, 0, 1, 0], [2, 1, 2, 0, 1, 0, 2, 0], [3, 1, 2, 0],
    [3, 1, 2, 0, 2, 3, 0, 1, 3, 0], [3, 1, 2, 0, 3, 0, 2, 3, 0], [3, 3, 2, 1, 0, 2, 0, 1, 3, 0],
    knuth] ++
    ((List.range 6).map fun n => subsets (n + 1)) ++
    [subsets 10,
      problem 10 ((List.range 10).flatMap fun i => [[i + 1], [i + 1]]),
      problem 17 ((List.range 17).flatMap fun i => [[i + 1], [i + 1]]),
      problem 65 ([1, 65] :: (List.range 63).map fun i => [i + 2]),
      dominoes 2 20, dominoes 3 8, dominoes 4 4, dominoes 6 6, sudoku4,
      langford 3, langford 4, langford 5, langford 7,
      problem 998 ((List.range 998).map fun i => [i + 1])]

/-- The inputs of `valid`: every input of `count`; the item counts 998, 999, and `2^64 - 1`, alone
and with an option; an option that repeats an item next to itself in the first, a middle, and an
unterminated last option, and apart in a single option; the items 1 and 65 in one option, which a
one-word bit set would take for a repeat; an item of `N + 1`, in a first, a middle, and a last
option, and of `2^64 - 1`; the same item in two options, which is valid; an item equal to `N`; and
items with `N = 0`. -/
def validInputs : List (List UInt64) :=
  countInputs ++
    [[998], [999], [maxU], [999, 1, 0], [maxU, 1, 0], [3, 1, 2, 2, 0], [5, 1, 2, 3, 1, 0],
      [3, 1, 0, 2, 2, 0, 3, 0], [5, 1, 2, 3, 0, 4, 4], [65, 1, 65, 0], [3, 4, 0],
      [3, 1, 0, 2, 4, 0, 3, 0], [3, 1, 0, 4], [3, 1, maxU, 0], [2, 1, 0, 1, 0], [3, 3, 0],
      [0, 1, 0], [0, 0, 5, 0]]

end Library.Combinatorics.DancingLinks
