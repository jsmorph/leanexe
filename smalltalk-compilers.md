# Smalltalk compiler options

The compiler used by `tests/smalltalk/run.sh` is `tools/smalltalk-compile.mjs`.
It accepts workspace snippets, not class files. Its output runs in the native
Lean VM and the compiled WASM VM. There is no CSOM or PySOM adapter.

## Earlier upstream runs

CSOM and PySOM were tested before the workspace cleanup. Their checkouts and
logs were removed. This table records the earlier reported results; none of
these results establishes that our VM can run their compiled output.

| Implementation | Revision | Core library revision | Earlier reported result |
|---|---|---|---|
| [CSOM](https://github.com/SOM-st/CSOM) | `70c19092ac71bdd863e2e8ed76498e1ab314fb14` | `5eac3287df98d54a72e4f04e0f8b5f53077da9a2` | HelloWorld, compiler probe, 100 tests / 445 assertions |
| [PySOM](https://github.com/SOM-st/PySOM) | `50f0cee5684b11163243e39372b6d4617204bae2` | `a721b4ff6ecb1ade54e0afe0bd15a8e80e41af17` | HelloWorld, compiler probe, 221 tests / 1,197 assertions |

The earlier CSOM run reported five unsupported optional checks for shifts and
Unicode; PySOM reported two optional unsigned-shift checks. These runs have not
been repeated in the current checkout.

The recorded commands were serial `make` inside CSOM's checkout and
`PYTHON=python3 SOM_INTERP=BC ./som.sh` for PySOM. The earlier CSOM parallel build
failed on a generated-header dependency. PySOM ran with Python 3.12.14; its `-d`
bootstrap disassembly failed. These are records of past runs, not current build
instructions verified by this branch.

`tests/smalltalk/examples/CompilerProbe.som` tests fields, captured mutation,
nested non-local returns, class-side methods, and an ordinary block called after
its enclosing method returns. Our source compiler rejects this class syntax.

## Proposed CSOM adapter

Export CSOM's compiled instance methods, class-side methods, nested block
methods, selectors, argument/local counts, fields, and class relationships.
Translate supported operations to the VM's UInt64 instruction array. CSOM uses
separate argument and local indices; our VM places self, arguments, and locals
in one slot list.

| SOM operation | VM operation |
|---|---|
| DUP, POP | Duplicate, pop |
| PUSH_LOCAL, PUSH_ARGUMENT | Load combined slot at the given enclosing depth |
| POP_LOCAL, POP_ARGUMENT | Store combined slot at the given enclosing depth |
| PUSH_FIELD, POP_FIELD | Load/store receiver field |
| PUSH_BLOCK | Block method ID and captured activation |
| PUSH_CONSTANT, PUSH_GLOBAL | Supported value or class ID |
| SEND, SUPER_SEND | Selector ID, argument count, defining class |
| RETURN_LOCAL, RETURN_NON_LOCAL | Local return, checked enclosing-method return |

Define entry termination before translating HALT. Reject strings, symbols,
arrays, large integers, and other unsupported values explicitly. Compare each
translated example with upstream CSOM, native Lean, and WASM, using ordinary
and stress collection. This adapter has not been written or tested.

Loading an existing Squeak or Pharo image is a separate task. It requires that
system's object format, classes, methods, contexts, processes, primitives, and
image loader. None is implemented by this VM.
