# Review of the specification

Two fresh agents reviewed [the specification](Spec.lean) and [the case inputs](../../../tests/TestSupport/Modules/DancingLinks.lean) against [the request](request.txt), from the files alone, with Python for exact covers, models of wrong programs, and the meaning of the library functions in the toolchain's source.  Each checked the expected values by an independent count: one by a recursion over the bit mask of covered items, and one by a memoized search that branches on the lowest uncovered item, each compared with a literal enumeration of index sets on the smaller inputs.  Every expected value agreed.

The first review found no input on which `countSpec` or `validSpec` differs from the request.  It found the comment silent on a last run without a zero after it, which the specification counts as an option, and the comment now says so.  It found "option `k` is the `k`-th run" ambiguous, since `k` counts from 0, and found that the comment's reason why covers are exact covers omitted the condition that no option repeats an item, and the comment now states both.  It found the docstrings incomplete: two invalid inputs and an option whose items are not in increasing order were not named, and the input `[1, 1, 0]` appeared twice.  The docstrings now name each input, and the duplicate is gone.  It named four classes of input that no case covered, each with a wrong program that agreed with every case, and the inputs now catch each:

| Wrong program | Inputs that catch it |
|---|---|
| A repeat check with a one-word bit set, in which items that differ by 64 share a bit | `[65, 1, 65, 0]` for `valid`, and 65 items with an option that holds the items 1 and 65 for `count` |
| A count kept in 16 bits | Seventeen items with two copies of each one-item option, `2^17` covers |
| A node table of fixed size, about 4,000 nodes | All subsets of 10 items, 1,023 options and `B(10) = 115,975` covers |
| A validity check of the first and last runs only | `[3, 1, 0, 2, 2, 0, 3, 0]` and `[3, 1, 0, 2, 4, 0, 3, 0]` |

The second review found no disagreement either, and it found every choice that the request leaves open recorded in the comment: the empty array as `N = 0`, the empty runs, a last run without a zero, and equal options as distinct.  It found the comment silent on the empty run that `List.splitOn` returns when nothing follows the first word, and the comment now names it.  It found the docstring of the inputs of `valid` overstated: no input paired the item count `2^64 - 1` with an option, and the only repeat whose two copies were not adjacent was in an input of one option.  The input `[2^64 - 1, 1, 0]` is now among the cases, and the docstring describes the repeats as they are.  It recorded these classes without inputs:

| Class | Why the cases leave it out |
|---|---|
| Counts of `2^32` or more, and of `2^64` or more | The search reaches each cover at a separate leaf, so such a count takes more than `4 × 10^9` steps.  A count kept in 32 bits, or one that stops at `2^64 - 1` in place of wrapping, would pass every case.  Only the proof excludes them. |
| Two items of one option that differ by a multiple of 128 | The largest such difference in the cases is 64, so a repeat check with a 128-bit set would pass every case. |
| A repeat whose copies are not adjacent and do not involve the option's first item | A check that compares each item with the one before it and with the first item would pass every case, as on `[3, 1, 2, 3, 2, 0]`. |
| Item counts and items of `2^32` or more, other than `2^64 - 1` | A check of the low 32 bits would pass every case, as on `[4294967296]` and `[3, 1, 4294967298, 0]`. |
| Inputs larger than 6,144 words or 1,023 options | A program with arrays of a fixed capacity above those sizes would pass every case. |

The specification states the count and validity and not the method, so the theorems that the program equals the specification say nothing about the dancing links, which only the program text shows.  The second review also noted that counting equal options as distinct agrees with Algorithm X, which keeps each option as its own row of nodes.
