# Word lists

[The native functions](Word/Program.lean) operate on `List UInt64`.  `listSum` folds from zero,
`sum` adds into a supplied accumulator, `range n` builds the words from zero through `n - 1`,
`reverse xs acc` reverses `xs` onto `acc`, and `increment` adds one to each word.  Addition wraps
modulo `2^64`.

[The compiled module](Word/Compiled.lean) generates execution, allocation, and trap-free theorems.
Summation and reversal use tail loops.  Increment uses guarded structural recursion.  The
[list-tail tests](../../Verified/Examples/ListTailCases.lean) cover lists beyond the guarded
recursion limit and check the allocation counts.

## Internal references

- [Verified Compiler Manual: Calls and recursion](../../docs/verified-manual.md#calls-and-recursion)
