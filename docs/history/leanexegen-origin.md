# Original `leanexegen` Request

This note preserves the initial prose request that led to the `leanexegen` orchestrator and prime-factor demonstration.  It predates the fixed array ABI, exact-artifact package format, structured LTG, annotations, and independent verification workflow.  The maintained interface appears in the [`leanexegen` reference](../leanexegen.md).

I want a tool like this:

```Shell
leanexegen -o myprogram.wasm myprogram.txt
```

Example `myprogram.txt`:

```
Input is an integer > 0 and output is the number of prime factors (not unique).
Pick convenient input and output types.
```

When `leanexegen` is run, it

1. Reads and understands `myprogram.txt`.  If it has serious questions,
   it prints those questions and exits with status 1.
1. Generates a formal specification that covers essential behavior.
   (To start, this spec can be pretty minimal.)
   problems here, it prints those problems an exits with status 2.
1. Generates the Lean program to implement `myprogram.txt` in a manner
   that can satisfy the spec.
1. Runs leanexe (in some form) to emit WASM: `myprogram.wasm`.
1. Proves that the WASM satisfies the spec.
1. Runs the WASM on some sample input. Prints each input/output pair.
1. Prints exactly how to invoke the WASM program so the user can run
   it.

At any stage, when `leanexegen` encounters a problem, it prints a
clear description to `stderr` and exits with a distinct exit code.

Unless `-s` (silent) is provided on the command line, `leanexegen`
prints updates about its processing to `stdout`.  The updates are
formatted in Markdown (but minimal formatting should be used).

Implementation language(s) for `leanexegen` is up to you.  Probably
Lean but could be Python with Lean.  If Python, the Python must be run
with `uv`.

The two generations (for the formal spec and the Lean program itself)
can be non-trivial and require iteration.  Let's try using codex
headless.
