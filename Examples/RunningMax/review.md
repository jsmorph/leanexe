# Running maximum: review of the specification

Fresh agents reviewed [`Spec.lean`](Spec.lean) and [`Samples.lean`](Samples.lean) against [the
request](request.txt).  Each saw only the request, the two files, and the samples with the outputs
of `expected` that `tools/verified-request-check --spec runningMax` printed.

The first review, of 17 samples, found no disagreement with the request.  It confirmed that the
fold of `max` from 0 over a nonempty prefix gives the prefix's largest entry, and it read the
toolchain's `Max UInt64`, which is `maxOfLe`, and `UInt64.le`, which compares the bit vectors as
unsigned numbers, so the comparison is unsigned as the comment states.  It named four choices that
the request leaves open, all of which the comment records: unsigned words as the numbers, the empty
result for the empty input, any length, and an array as the list.  It computed all 17 outputs by
hand, including the two generated inputs of 20 and 100 entries, with the same results.  It noted
that "a new list" implies an unchanged input, which a pure specification cannot violate and which
matters only for the input's memory after a call.  The call theorem `Verified.CallSpec` states that
every array borrowed before the call stays borrowed, so the input keeps its words.

It named input classes that no sample covered: lengths that leave a remainder of 6 or 7 after
division by 8, which a loop unrolled by 8 could get wrong, and lengths of 4,096 or more, for which
the input and the result together exceed one page of memory.  Four samples were added: lengths 6,
7, and 15, and 5,000 entries of `i mod 1000`.

The second review, of the 21 samples, again found no disagreement.  It read the same definitions of
the toolchain, confirmed the four recorded choices, and checked every output, the three generated
inputs against their expressions with `awk`.  It agreed that the specification cannot state that
the input stays unchanged, and it named three classes that no sample covers.  A long input with
words of `2^32` or more, such as `#[2^63 − 1, 2^63, 1, 2, 3, 4, 5, 6, 7]`, would catch an
eight-entry loop that compares signed or 32-bit words.  In the 5,000-entry sample no entry after
index 999 changes the output, so a program that misread those entries as values of at most 999
would pass.  No sample has more than 8,192 entries, so no single array spans more than a page.
The stage ends with these notes, since the second review found no disagreement with the request,
and the specification and samples were frozen.
