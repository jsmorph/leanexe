# Smalltalk compilers

The VM currently uses `tools/smalltalk-compile.mjs`, a small temporary compiler
for workspace snippets. It does not compile SOM class files. The next compiler
integration remains an adapter for CSOM's compiled methods and bytecodes.

Two real SOM implementations were tested before workspace cleanup. Those
checkouts and logs were removed. The pins and results below record that earlier
work; they are not new tests of the reconstructed Lean/WASM VM.

| Implementation | Revision | Core library revision | Earlier result |
|---|---|---|---|
| [CSOM](https://github.com/SOM-st/CSOM) | `70c19092ac71bdd863e2e8ed76498e1ab314fb14` | `5eac3287df98d54a72e4f04e0f8b5f53077da9a2` | HelloWorld, compiler probe, 100 tests / 445 assertions |
| [PySOM](https://github.com/SOM-st/PySOM) | `50f0cee5684b11163243e39372b6d4617204bae2` | `a721b4ff6ecb1ade54e0afe0bd15a8e80e41af17` | HelloWorld, compiler probe, 221 tests / 1,197 assertions |

Both projects have MIT licenses. The earlier CSOM run had five unsupported
optional checks for large shifts, unsigned shifts, and Unicode; PySOM had two
optional unsigned-shift checks. These are useful compiler references, not claims
of complete Smalltalk compatibility.

Build CSOM with serial `make` from inside its checkout. Its generated platform
header dependency caused an earlier parallel build to fail. Run PySOM with
`PYTHON=python3 SOM_INTERP=BC ./som.sh`; the bytecode interpreter ran unchanged
under Python 3.12.14. Its `-d` bootstrap disassembly failed, while normal
compilation and execution worked.

The probe in `tests/smalltalk/examples/CompilerProbe.som` exercises fields,
captured mutation, nested non-local returns, class-side methods, and an ordinary
escaped block. It belongs to the upstream compiler tests; the temporary JS
frontend deliberately rejects SOM class syntax.

## CSOM adapter plan

CSOM's recursive-descent compiler emits sixteen classic SOM bytecodes. Export
its instance/class-side methods, nested block methods, selector literals,
argument/local counts, fields, and class relationships, then translate them to
our immutable wordcode. CSOM has separate lexical argument and local indices;
our VM combines them in slots with self at index zero.

| SOM bytecode | VM translation |
|---|---|
| DUP, POP | Duplicate, pop |
| PUSH_LOCAL, PUSH_ARGUMENT | Load combined slot with lexical depth |
| POP_LOCAL, POP_ARGUMENT | Store combined slot with lexical depth |
| PUSH_FIELD, POP_FIELD | Receiver-field load/store |
| PUSH_BLOCK | Anonymous method descriptor plus captured activation |
| PUSH_CONSTANT, PUSH_GLOBAL | Supported literal or class-global reference |
| SEND, SUPER_SEND | Selector ID, argument count, lexical defining owner |
| RETURN_LOCAL, RETURN_NON_LOCAL | Local return, checked home return |
| HALT | Controlled entry termination; specify before translating |

Reject unsupported string/symbol values, arrays, and large integers explicitly.
Compare adapted examples between upstream CSOM, native Lean, and actual WASM
with normal and stress GC. No adapter is implemented yet.

Existing Squeak/Pharo image compatibility is outside this development: it would
require their object formats, mutable classes/methods, contexts, processes,
primitive contracts, and image loading. Our own heap snapshots could be added
later if persistence becomes useful.
