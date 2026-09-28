# Verified WASM encoding

## Interface

Import `Project.Encoding` in the Talos proof workspace.  `Wasm.Encoding.encode`
accepts a `Wasm.Module` and returns `Except String ByteArray`.
`Wasm.Encoding.writeModule path module` writes a successful result and raises
an I/O error if encoding fails.

| Theorem | Statement |
| --- | --- |
| `encode_correct` | Every successful result satisfies `Encodes` for the input module. |
| `encode_complete` | Every input satisfying `Ready` succeeds and satisfies `Encodes`. |
| `encode_valid_complete` | `Ready` and `Spec.Validity.Module` imply success, representation, and `ValidBinary`. |
| `encode_behavior` | The same premises and any property of the input module imply an encoding representing a module with that property. |

`Ready` states the representable shapes and the format's size bounds.  It
checks function type indices against the preserved type table, numeric value
types, the instruction forms below, UTF-8 byte counts, vector counts, local
counts, and body and section sizes.  Its size functions count the specified
output form independently of module encoder success.

`Spec.Validity.Module` states scalar WASM typing, memory limits, resolved
function signatures, export bounds, and distinct export names.  `ValidBinary`
means that the binary represents a module satisfying this predicate.
Validity and application behavior remain input proof obligations.  The encoder
preserves the represented module, so the composition theorem applies to an
existing behavioral theorem about that module.

## Representation and specification

The grammar in [the specification directory](Spec) imports Talos syntax and
Lean's core library.  It defines binary relations without calling the encoder.
These definitions and their correspondence with the published WASM rules
form the trusted specification.  Lean checks proofs relative to those definitions.

The [binary specification review](BinaryReview.md) and
[typing specification review](ValidityReview.md) record the rule comparisons,
source revisions, and theorem premises.  The binary review also records
discrepancies in the cited Core 3 snapshot's UTF-8 formulas and integer aliases,
with the authoritative references used to resolve them.

| Part | Official rules | Lean definition |
| --- | --- | --- |
| Integers, vectors, and names | [Binary values](https://webassembly.github.io/spec/core/binary/values.html), [lists](https://webassembly.github.io/spec/core/binary/conventions.html#lists) | `Spec.Values` |
| Numeric and function types, limits | [Binary types](https://webassembly.github.io/spec/core/binary/types.html) | `Spec.Types` |
| Instructions and control delimiters | [Binary instructions](https://webassembly.github.io/spec/core/binary/instructions.html) | `Spec.Instructions` |
| Sections and complete modules | [Binary modules](https://webassembly.github.io/spec/core/binary/modules.html) | `Spec.Modules` |
| Typing and module validity | [Instruction validation](https://webassembly.github.io/spec/core/valid/instructions.html), [module validation](https://webassembly.github.io/spec/core/valid/modules.html) | `Spec.Validity` |

The scope follows LeanExe's emitted scalar language: `i32`, `i64`, `f32`, and
`f64` types, its integer and floating-point operations, direct calls, function
imports, integer globals, exports, and one optional 32-bit memory.  Functions
may return multiple values.  Structured controls have zero parameters and
zero or one result, with matching explicit Talos annotations.

The encoder retains duplicate and unused type entries and declared function
type indices.  Function imports select the first matching signature in that
table.  Each local uses a one-element declaration group.  Memory instructions
use alignment zero, which is a valid alignment hint for every emitted load and
store.  Every conditional includes an explicit `else`.  The module contains
the type, import, function, memory, global, export, and code sections, including
empty sections.  These choices select permitted binary forms.

The accepted Talos metadata includes canonical function `gcTypes`, integer
global initializers with matching declared types and constant `sourceInit`,
and empty memory data.  Unsupported syntax or inconsistent metadata produces
an error.  The theorem's subject is the returned Lean byte array.  Running
those bytes also depends on the external runtime and host environment.

## Tests

From the repository root, with `WASMTIME` and `WASM_TOOLS` configured as in
[Developing LeanExe](../../../../../DEVELOPING.md), run:

```sh
node test/encoding.js
```

The driver builds the proof and test modules through `tools/leanrun`, audits
six public theorem axiom sets, writes seven modules into a fresh directory
under `tmp`, validates them with wasm-tools, and runs Wasmtime checks.
Three inputs are the existing generated GCD, floating-point multiplication,
and ASCII-validator models.  The remaining inputs exercise integer boundaries,
UTF-8 export names, duplicate and unused types, mixed locals, multiple results,
WASI imports, memory, globals, and scalar operations.  Lean guards also check
rejection of oversized indices and inconsistent metadata.  Test output stays
in its temporary directory for inspection.
