# Review of the specification

Two fresh agents reviewed [the specification](Spec.lean) and [the case inputs](../../../tests/TestSupport/Modules/MultiPrecision.lean) against [the request](request.txt), from the files alone.

The first review found no input on which `addSpec`, `subSpec`, or `mulSpec` differs from the request on digit arrays.  It found that the comment did not say how the functions behave on other arrays or which length bounds the theorems assume, and did not name empty arrays or zero digits at the top.  The comment now states all of these.  It found that the pair `([1, 2, 3], [3, 2, 1])` has the larger first argument, against the docstring's description, and that consecutive arbitrary digits differed by one of two fixed amounts, because `rw` steps by a constant.  The docstring now describes that pair as a borrow through a digit where both arguments agree, and the arbitrary digits come from products of two arbitrary words.  For the classes it named without inputs, the inputs now include a longer argument with high zero digits, equal values of different lengths, a nonzero number with an empty one, an empty number with one of three digits, carry runs of 50 and 60 digits, long numbers of largest digits above zeros, and numbers of 150 and 120 digits.

The second review found no disagreement, and it found every choice that the request leaves open recorded in the comment.  It found three inaccurate clauses in the docstrings, an imprecise account of where the call theorems obtain their length bounds, a comment line far longer than the others, and a wrong length in the README, all now corrected.  It recorded these classes without inputs:

| Class | Why the cases leave it out |
|---|---|
| A nonempty zero number with a nonzero partner, such as `([0, 0], [5])` | Zero arrays appear only with other zero arrays or empty ones. |
| Differences `u - v` with `u < v` of three or more digits of equal length | Only `([5], [7])` and one arbitrary pair of two digits have the smaller first argument at equal length. |
| Carries past the end of the shorter argument through digits other than `2^32 - 1` | The arbitrary digits contain neither 0 nor `2^32 - 1`. |
| Arguments of 9 to 39 digits | The arbitrary pairs have at most 8 digits, and each long argument has 1 digit or at least 40. |
| Arrays outside the theorems | Words of `2^32` or more, or `2^64` or more words, lie outside the theorems, which compare nothing on them. |
