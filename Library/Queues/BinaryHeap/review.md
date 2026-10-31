# Review of the specification

Two fresh agents reviewed [the specification](Spec.lean) and [the case inputs](../../../tests/TestSupport/Modules/BinaryHeap.lean) against [the request](request.txt), from the files alone.

The first review found no input on which `expected` differs from the request.  It found that the comment did not say which codes insert and which remove, or that a removal ignores its value, and the comment now states both.  It found two inaccurate clauses in the inputs' docstring: the input with a word without a partner holds three operations before that word, and the description of the 1,000-operation input did not parse.  It also found that `arbitrary` produced only odd codes and even values, because `rw i` is even exactly when `i` is odd and the generator read codes and values at indices of fixed parity.  The generator now takes the code of operation `i` from `rw (seed + i)` and its value from `rw (seed + count + i)`, so codes and values of both parities occur, and the docstring describes each input.  It named classes without inputs: removal codes whose low 32 bits are 0, insertion after the queue has emptied, and odd words in the arbitrary runs.  The inputs now include the codes `2^32` and `2^63`, an insertion after the queue empties, and arbitrary runs with words of both parities.

The second review found no disagreement, and it found every choice that the request leaves open recorded in the comment.  It found two more inaccurate clauses: the values of the removals in the 1,000-operation input are arbitrary words, and the codes of the removals in `arbitrary` are multiples of 3.  Both docstrings now state these facts.  It recorded these classes without inputs:

| Class | Why the cases leave it out |
|---|---|
| Long mixed runs in which the heap shrinks | The arbitrary runs remove about one operation in three, so their heaps grow.  Long shrinking runs appear only as removals after insertions. |
| Repeated emptying and refilling in a long run | Only the short inputs refill an emptied heap. |
| Repeated large words in long runs | Repeats in the long runs come from values below 10. |
| Heaps of more than 671 words | The longest run reaches 671 words. |
| An odd-length input whose last word is 0 | A word without a partner is no operation, and a trailing insertion could not change the outputs. |

Both reviews noted that the specification fixes the outputs and not the storage, so the theorem that the program equals `expected` says nothing about the binary heap, which only the program text shows.
