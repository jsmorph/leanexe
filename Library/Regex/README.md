# Regular expressions

The module `regex` decides whether a byte string belongs to the language of a regular expression given at run time.  Its export `matchWith` takes a pattern of `pn` words in postfix order and an input of `n` bytes, each in an `Array UInt64`, with the input packed eight bytes to a word as [the packed bytes](../Bytes/Packed.lean) describe.  It returns the code that `answer` of [the specification](Spec.lean) gives for the first `pn` words of the pattern and the first `n` bytes of the input: 2 when the pattern does not decode, 3 when it has more than 63 sets of bytes, and otherwise 1 when the whole input is in the pattern's language and 0 when it is not.  For `3 pn < 2^64` and a heap with room for `24 pn + 21,272` bytes, a call returns the code without a trap, leaves both arrays borrowed, keeps the bytes of every region of the caller's heap, and raises the heap's top by at most that number of bytes.  The file theorems of [`File.lean`](File.lean) state that `build/verified/regex.wasm` holds the module.

## Specification

[`Spec.lean`](Spec.lean) defines `Re`, a regular expression over bytes: `empty` matches no string, `eps` matches the empty string, `cls p` matches one byte `b` with `p b = true`, and `cat`, `alt`, and `star` form concatenation, alternation, and repetition.  `Re.lang` builds the language with the operations of Mathlib's `Language`, and `lang_eq_matches'` proves that it equals the language `matches'` of Mathlib's `RegularExpression` when each set of bytes is the sum of its bytes.  A match covers the whole input, as Python's `re.fullmatch` does [3].  A search for a match anywhere in the input is the match of the pattern that surrounds the expression with the star of the set of all bytes.

| Words | Effect on the stack |
|---|---|
| `0` | Pushes `empty`. |
| `1` | Pushes `eps`. |
| `2 w0 w1 w2 w3` | Pushes `cls` of the set of bytes `b` for which bit `b % 64` of word `b / 64` is set, where bit `i` has the value `2^i`. |
| `3` | Replaces the top two expressions `a` and `b`, with `b` on top, by `cat a b`. |
| `4` | Replaces the top two expressions by `alt a b`. |
| `5` | Replaces the top expression `a` by `star a`. |

`decode` runs the words from an empty stack.  A pattern decodes when every opcode is one of these six, every operator finds its operands, every opcode 2 has its four words, and one expression remains.  `answer` tests decoding first, so a pattern that does not decode gives 2 whatever its number of sets.  The limit of 63 sets comes from the program, which holds a state of its automaton in one word with bit 0 for the start, and `positions` counts the sets.  Membership is decidable through Mathlib's derivative matcher `rmatch`, so `answer` is computable and serves as the tests' oracle.

For example, `ab*` is the twelve words `2, 0, 2^33, 0, 0, 2, 0, 2^34, 0, 0, 5, 3`: the sets of the bytes 97 and 98, the star of the second, and their concatenation.

| Module | Export | Function | Arguments | Result | Call theorem |
|---|---|---|---|---|---|
| `regex` | `matchWith` | 8 | Pattern array, `pn`, input array, and `n`. | Code as one word. | `matchWith_call` |

A count beyond an array's words or bytes is accepted, and the missing words and bytes read as zero in both the program and the theorem.  A zero word past the end of the pattern pushes `empty`.

## Implementation

[The program](Program.lean) builds the position automaton of McNaughton and Yamada [1] and Glushkov [2].  Each set of bytes in the pattern is a position, numbered from 1 in the order of the pattern, and a state is a set of positions held in one word, with bit 0 for the start.  `scan` reads the pattern words once, keeping three words for each expression on its stack: 1 when the expression matches the empty string and 0 otherwise, and its sets of first and last positions.  For `cat a b`, `addFollow` adds the first positions of `b` to the follow set of each last position of `a`, and for `star a` it adds the first positions of `a` to the follow sets of `a`'s last positions.  The scan stores the four words of each of the first 63 sets in a table of 256 words.  A set past the 63rd still counts, and the scan still decodes the words after it, so a pattern that does not decode gives 2 at any number of sets.

After the scan, `matchWith` stores the pattern's first positions as the follow set of position 0, so the start acts as a position before the first byte.  `masks` builds 256 words, the positions whose set holds each byte, and `steps` builds 2,048 words, the union of the follow sets of the positions in each byte of a state for each of its 256 values.  `advance` computes the next state from eight reads of `steps` and one of `masks`, and `runInput` applies it to each byte of the input from state 1.  The input matches when the final state holds a last position of the pattern, or bit 0 when the pattern matches the empty string.

A call allocates at most five blocks and releases them before it returns: the scan's stack of `3 pn` words, its follow table of 64 words, and its 256 words of sets, and the tables of `steps` and `masks`, which a call that returns 2 or 3 does not build.  `scanStep`, `push`, and `combine` are `@[inline]`, so the verified compiler unfolds them into the loop of `scan`, whose state it updates in place.  A record parameter of a compiled function is borrowed, so compiled as functions they would copy the three arrays at every word.  `matchWith_bound` states the allocation bound of `24 pn + 21,272` bytes, each block with a header of 48 bytes and a length word.  The scan runs the 64 steps of `addFollow` at most once for each operator word, `steps` and `masks` take 16,384 and at most 16,128 steps, and each input byte takes nine table reads.

## Proof

| Module | Content |
|---|---|
| [`Glushkov.lean`](Glushkov.lean) | `nullable`, `First`, `Last`, `Follow`, and `Class` of an expression whose positions follow an offset `k`, the reading `Accepts` along `Follow` and `Class`, and `glushkov : w ∈ r.lang ↔ Matches r k w`. |
| [`Automaton.lean`](Automaton.lean) | Transitions `Next` and final states `Final` of the automaton, its runs `step` and `steps`, and `lang_iff_steps`: a word is in the language exactly when the states reached from state 0 hold a final state. |
| [`Bits.lean`](Bits.lean) | Bits of `\|\|\|`, `&&&`, `1 <<< p`, and test `(s >>> q) &&& 1 == 1` on bits 0 to 63. |
| [`RunProof.lean`](RunProof.lean) | `masks_bit`, `steps_bit`, `advance_bit`, and `runInput_bit`: the word that `runInput` returns holds the automaton's states after the input, when bit `q` of follow entry `p` holds `Next r p q` and bit `q` of mask entry `c` holds `Class r 0 q c`. |
| [`ScanProof.lean`](ScanProof.lean) | `Corr`, which relates the scan's state to the stack of expressions that `Spec.run` builds, its preservation by each kind of word, and `scan_run`, which follows the recursion of `Spec.run`. |
| [`Proof.lean`](Proof.lean) | `matchWith_eq`: when `3 pn < 2^64`, `matchWith pat pn msg n` is `answer` of the words `pat[j]!` for `j < pn` and the bytes `byteAt msg i` for `i < n`. |
| [`Compiled.lean`](Compiled.lean) | Verified compilation of `addFollow`, `scan`, `masks`, `steps`, `advance`, `runInput`, and `matchWith`. |
| [`Bytes.lean`](Bytes.lean) | `matchWith_export`, `matchWith_bound`, and `matchWith_call`, from `compiled.matchWith.trapFree` through `Verified.ImplementsTables.call`, the bound equations, and `matchWith_eq`. |
| [`File.lean`](File.lean) | The emitted file holds the module's encoding and decodes to the module. |

`scan_run` discharges the two hypotheses of `runInput_bit` from `Corr` for a stack of one expression, and `matchWith_eq` joins `runInput_bit` with `lang_iff_steps` and `glushkov`.  The hypothesis `3 pn < 2^64` keeps the size of the scan's stack from wrapping.  Every theorem listed above depends only on the axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Tests

[The native check](../../tests/TestSupport/Regex/Native.lean) compares `matchWith` with `answer` on 600 random pattern trees, each against all 341 strings of at most four bytes over 0, 1, 64, and 255, on 3,000 random word sequences, most of which do not decode, and on patterns of 62 to 65 and 80 sets.  The trees' sets hold the bytes 0, 1, 2, 63, 64, 128, 200, and 255, which reach every word of a set.  [The Python cases](../../tests/TestSupport/Regex/PythonCases.lean) are 34,500 patterns and inputs, which [`python_check.py`](../../tests/regex/python_check.py) translates to Python's syntax and compares with `re.fullmatch`.  The native check interprets the derivative matcher with `lean --run` and takes about an hour.

[The module cases](../../tests/TestSupport/Regex/Cases.lean) compare 280 calls in Wasmtime with native Lean: 40 pattern trees against six inputs each, thirteen short word sequences, patterns of 62 to 65 sets, counts past the end of each array, and the star of one set over 1,000 bytes.  Their codes are 137 zeros, 117 ones, 22 twos, and 4 threes.  Every case requires that the call release every block it allocates, leaving the host's pattern and input, and that it make at most five allocations of its own, or three when it returns 2 or 3.

```sh
tools/leanrun --timeout 3h lake build Library.Regex.Bytes TestSupport.Regex.CasesMain
tests/regex/run.sh
tests/verified/run.sh --cases regex
tools/leanrun --timeout 10m lake env lean Library/Regex/File.lean
```

## References

1. R. McNaughton and H. Yamada, [*Regular expressions and state graphs for automata*](https://doi.org/10.1109/TEC.1960.5221603), IRE Transactions on Electronic Computers EC-9(1), 39–47, 1960.
2. V. M. Glushkov, [*The abstract theory of automata*](https://doi.org/10.1070/RM1961v016n05ABEH004112), Russian Mathematical Surveys 16(5), 1–53, 1961.
3. Python Software Foundation, [`re.fullmatch`](https://docs.python.org/3/library/re.html#re.fullmatch), *The Python Standard Library*.
