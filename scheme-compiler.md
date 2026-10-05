# A small Scheme compiler for the VM

`tools/scheme-compile.scm` is a small R7RS host compiler. It reads Scheme forms
using the host's `read` and writes a JSON array of decimal word strings. This is
the existing VM wire format, with no additional intermediate language. The
compiler and the Scheme host run outside WASM; the resulting instructions run
on the LeanExe-compiled VM and collector.

The compiler supports unsigned 64-bit integers, booleans, variables, fixed-arity
`lambda`, `if`, `begin`, `set!`, ordinary `let`, top-level `define` (including
procedure shorthand), applications, binary `+`, `-`, `<`, `=`, and first-class
`call/cc`. Arithmetic follows the VM: unsigned words, wrapping addition and
subtraction, and unsigned comparison. Arithmetic procedures take exactly two
arguments. Only false is false. An omitted `if` alternative and an empty `begin`
produce the VM's unit value.

No lists, quotation, strings, macros, internal definitions, variadic parameters,
named let, or modules are included. Unsupported syntax and unbound variables
are rejected. Type and procedure-arity errors are reported by the VM. Top-level
definitions are unique; changing a binding uses `set!`. Referencing a global
before its initializer runs exposes its initial unit value; this is a test
subset, not a claim of full Scheme conformance.

## Compilation

Every binding receives a distinct integer ID, including shadowed bindings.
Compiling a lambda records accesses to bindings outside its parameters and puts
those IDs in its capture descriptor. Creating a nested lambda also counts as
using its captures in the enclosing lambda. The VM captures shared locations,
so mutation needs no additional boxing pass. `let` expands to a lambda application.

Top-level locations are allocated before evaluating any initializer. Closures
can therefore capture themselves or each other before the procedures are stored
in those locations. Initializers and other top-level forms run in source order.
Applications evaluate the operator and arguments from left to right.

The last expression of a procedure, either arm of a tail-position `if`, and the
last expression of a tail-position `begin` inherit tail position. An application
there emits `tailcall`; other applications emit `call`. Other tail expressions
emit `ret`. The top-level final expression also has tail position. `call/cc` is
an ordinary primitive procedure supplied by the VM, with no compiler CPS pass.

Instructions contain symbolic labels while being emitted. Assembly assigns PCs,
places descriptors after the instruction stream, and resolves both kinds of
reference. Function bodies follow the top-level terminating instructions.

## Running it

With a Chibi Scheme installation and the built `build/scheme/scheme.wasm`:

```sh
chibi-scheme tools/scheme-compile.scm countdown.scm > build/scheme/countdown.json
node tools/scheme-run.mjs build/scheme/countdown.json 32
```

For example, `countdown.scm` can contain:

```scheme
(define (countdown n)
  (if (= n 0) 7 (countdown (- n 1))))
(countdown 10000)
```

The result is `7`. The runner accepts capacity, execution fuel, and forced-GC
flag after the JSON filename. Defaults are 64 cells, 300000 transitions, and
normal collection. `SCHEME_WASM` selects another emitted module.

Run `SCHEME=chibi-scheme tests/scheme/run.sh` for the complete focused suite.
`SCHEME` selects the host executable; its invocation must accept a script and
arguments in that order. The Scheme file uses standard R7RS libraries. Validation
here used Chibi revision `c4e7367e867428889d8fe898a0b39f42e418b3f1`, built in scratch;
there is no new vendored language implementation or VM dependency.

`tests/scheme/source-cases.mjs` contains the source programs and expected results.
The driver compiles them, rejects malformed/unsupported examples, and adds them
to the existing bytecode corpus. Native Lean and the emitted WASM then execute
the same words with normal and forced collection. The suite compares their
complete post-collection arenas and checks heap reachability independently.
Short programs are also checked after each transition.

The complete driver passed on 2026-10-05: 27 source programs compiled, 22 invalid
programs rejected, 112 native executions and complete native/WASM arena comparisons,
and 159 total WASM checks. The compiled countdown completed 10,000 tail calls in
32 cells, with a forced-GC peak of 17 cells. Multi-shot `call/cc` returned 102 and
retained its counter mutation.

The compiler has no correctness proof yet. Its output and tests provide small
examples for a future LeanExe frontend while keeping parsing, binding IDs,
instruction emission, and label resolution easy to port.
