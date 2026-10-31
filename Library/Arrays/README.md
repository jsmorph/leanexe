# Word arrays

The functions take `Array UInt64`.  Counts and indices use `UInt64`, and word arithmetic wraps
modulo `2^64`.  Each linked family has Lean definitions in `Program` and generated execution
proofs in `Compiled`.

| Family | Functions and behavior |
|---|---|
| [Search](Search/Program.lean) | `count` counts occurrences.  `firstAbove` returns the first index above a limit and a Boolean indicating success.  `firstZero` searches a specified prefix and returns the prefix length when no zero occurs.  Its default read returns zero past the array's end. |
| [Filter](Filter/Program.lean) | `removeAll` removes matching words while preserving order.  `below` collects at most a specified count of words below a limit.  `clearUntil` zeros the prefix preceding the first matching word. |
| [Repeat](Repeat/Program.lean) | `repeated` concatenates a specified number of copies. |
| [Range](Range/Program.lean) | `evens n` constructs the `n` words `2 * i`. |
| [Word operations](Word/Program.lean) | `scaled` multiplies every word by a scalar. |

`removeAll` searches and shifts repeatedly, taking quadratic time.  `tests/verified/run.sh` also
runs cases of the verified compiler's examples on these modules, as
`tests/verified/library-cases.txt` maps them.  [The search proof](Search/Proof.lean),
`firstZero_cases`, gives the first-zero prefix property that [the removal example's
proof](../../Examples/RemoveZero/Proof.lean) uses.
