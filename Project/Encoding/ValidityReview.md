# Typing specification review

## Scope and conclusion

Reviewed on 2026-09-27: [the validity predicate](Spec/Validity.lean), together
with the binary premises in `ValidBinary`.  For an encoding derivation and
contexts supplied by a module satisfying `Spec.Validity.Module`, each Lean
typing constructor has a derivation under the official scalar WASM rules.
The module conditions supply the required context, declaration, and export
checks.  The conditions are sufficient for the selected binary forms.

The comparison uses the official
[instruction rules][instructions], [type rules][types], and
[module rules][modules] at revision
`608711107b7f1edb13efd57b7d79b49477462d36`.  The
[binary review](BinaryReview.md) records the reference versions, resolved
reference discrepancies, Talos pin, and binary source identities.
The derivation arguments below are a manual review of the formal definitions.

## Instruction typing

### Context and stack order

The Lean typing lists place the stack top at the right.  Thus a store consumes
`[i32, valueType]`, and `br_if` consumes the label's values followed by its
`i32` condition.  This matches the official typing notation.  Talos's execution
stack has a separate representation.  This predicate classifies instruction
sequences, so its list order follows the WASM type rules.

The module premises make every function parameter and result numeric: a
defined function's declared type index resolves to its signature, while each
import's signature occurs in the validated type table.  Local types are
numeric by a separate premise.  `GlobalReady` fixes each global's declared
type to its integer initializer type.  Consequently, the fallback in
`globalTypes` is unreachable for a module satisfying the predicate.

The function context orders imports before defined functions and parameters
before declared locals.  It includes the function's result list as label
zero and as the return type.  Structured controls prepend their label,
preserving depth-zero lookup for the innermost control.

Numeric locals have default values.  The official Core 3 initialization
state is therefore `SET` for every local on function entry and throughout
execution.  Local assignment leaves that state set.  This justifies using
one fixed local-type context in `Program.cons`.

### Scalar, variable, and memory rules

Each entry of `Unary`, `Binary`, `Load`, and `Store` was compared with its
official instruction family.  The complete opcode inventory appears in the
binary review.

| Lean rule or family | Stack typing |
| --- | --- |
| `nop` | `[] -> []`. |
| `unreachable` | Any numeric input stack to any numeric output stack. |
| `drop` | `[t] -> []` for numeric `t`. |
| Integer constants | `[] -> [i32]` or `[] -> [i64]`. |
| Float constants | `[] -> [f32]` or `[] -> [f64]`, as the official rule `C \|- CONST nt c_nt : eps -> nt` gives (2026-10-03). |
| Integer comparisons and `eqz` | Consume the stated integer type and produce `i32`.  Binary comparisons consume two operands. |
| Integer binary arithmetic | `[iN, iN] -> [iN]`, for the declared width. |
| Float binary arithmetic | `[fN, fN] -> [fN]`. |
| Float unary arithmetic | `[fN] -> [fN]` for `f32.nearest`, `f32.sqrt`, and `f64.sqrt`. |
| Wrap and unsigned extension | `i64 -> i32` and `i32 -> i64`, respectively. |
| Signed byte extension | `i32 -> i32`. |
| Signed conversion and saturating truncation | `i32 -> f32` and `f32 -> i32`, respectively. |
| Demotion and promotion | `f64 -> f32` and `f32 -> f64`, respectively. |
| Four reinterpretations | Preserve width and change between the corresponding integer and float types. |
| `localGet`, `localSet`, `localTee` | Require a successful local lookup and use exactly that local's type. |
| `globalGet`, `globalSet` | Require a successful global lookup.  Assignment additionally requires mutability. |
| `call` | Requires a function lookup and consumes its parameters in declaration order, producing its results in declaration order. |
| Loads | Require memory and consume an `i32` address.  Results are `i32`, `i64`, and `i32` for the three load forms. |
| Stores | Require memory and consume an `i32` address followed by the value of the declared type. |
| `memorySize`, `memoryGrow` | Require memory and have types `[] -> [i32]` and `[i32] -> [i32]`. |

The load and store typing premises combine with `Spec.MemArg` in the
encoding derivation.  Its alignment bound gives the official access-width
condition.  Its `UInt32` offset gives `offset < 2^32`.  The module memory
premise supplies a 32-bit address type.  These checks cover all parts of the
official memory-instruction rules.

### Control and sequencing

| Constructor | Derivation under the official rules |
| --- | --- |
| `block` | Empty input, declared results, and a label expecting those results.  The body must produce the complete result list. |
| `loop` | Empty input and a label expecting the empty parameter list.  Normal exit still produces the declared results. |
| `iff` | Consumes `i32`.  Both branches start with an empty operand stack and must produce the same declared results.  The label expects those results. |
| `br` | Lookup fixes the target result list.  Those values must be on top of the input stack.  Extra values below them are discarded by the branch.  Its output stack is polymorphic. |
| `brIf` | Consumes the condition above the target values.  The fall-through stack retains those values. |
| `ret` | Requires the function results on top of the input stack, with arbitrary numeric values below them and arbitrary numeric output types. |
| `frame` | Adds the same numeric prefix below the consumed and produced values.  The official sequence-framing rule derives this for the single-instruction sequence. |
| `Program.nil` | Frame the official empty-sequence rule with the stated numeric type list. |
| `Program.cons` | Compose the head and tail derivations at their common intermediate stack. |

The restriction to zero control parameters and at most one control result
comes from `BlockForm`.  Function results may contain several values, including
mixed numeric types.  Function-label branches and returns retain the complete
result list.

A structural induction on `Instruction` and `Program` supplies the manual
correspondence argument.  Its target for an instruction is an official
single-instruction sequence judgment, allowing the `frame` case.  The
induction carries the numeric-context conditions.  The control cases preserve
them when adding labels, and local assignment preserves initialization.  Each
other case uses the corresponding official rule in the tables above.

## Module validity

Each field of `Spec.Validity.Module` was compared with the official module
rule and its declaration rules.

| Premise | Obligation discharged |
| --- | --- |
| `shape` | Selects the module components represented by the binary grammar and fixes canonical scalar type metadata. |
| `types` | Makes all parameter and result types valid numeric types.  With canonical metadata, each type is a valid singleton final function subtype. |
| `imports` | Provides an existing type for every imported function signature.  The encoding derivation supplies the chosen index and the two names. |
| `functions` | Connects each declared type index to the function signature, validates local types, bounds the combined parameter/local count, and types the body from an empty stack to the declared results. |
| `memories` | Requires 32-bit memory, minimum at most 65,536 pages, and any maximum between the minimum and 65,536. |
| `globals` | Supplies a numeric global type, mutability, and a matching constant initializer.  Integer constants are permitted constant expressions. |
| `functionCount` | Bounds the combined import and defined-function index set. |
| Function exports | Each index refers to an imported or defined function. |
| Global exports | Each index refers to a declared global. |
| Memory exports | Index zero exists and refers to the sole memory. |
| `distinctExports` | Names are distinct across all three export kinds together. |

Function bodies see all function signatures, allowing mutual recursion.
Global initializers contain one integer constant, so their validity is
independent of the preceding-global context.  The fixed empty fields discharge
the remaining table, element, data, tag, non-function-import, and start
obligations.

The combined claim uses both `Encodes m bytes` and `Spec.Validity.Module m`.
The encoding derivation supplies binary bounds on type vectors, names,
indices, declarations, expanded locals, function bodies, and sections.  The
typing predicate supplies the context lookups and stack constraints.  This
division is sufficient for `ValidBinary` as defined in the
[correctness module](Correctness.lean).

## Restrictions and theorem consequences

The predicates describe the chosen scalar representation.  They require
explicit function type indices, canonical type metadata and integer global
initializers, empty memory data, zero control parameters, and zero or one
control result.  `Function` additionally requires parameters plus locals to
total less than `2^32`, and `Module` places the same bound on imported plus
defined functions.  These are explicit restrictions of the stated theorems.

The checked validity theorem has the required implication under those
premises: `Ready m` establishes successful encoding, and an input validity
proof establishes `ValidBinary` for the result.  The reviewed binary grammar
and typing rules justify interpreting that conclusion as a valid encoding of
the represented scalar module.

For behavioral composition, the proof witnesses the represented module with
the original `m`.  Instantiating `P` with a Talos execution theorem retains
that theorem's quantified inputs and assumptions.  The correspondence of
Talos execution semantics with WASM execution remains an existing assumption
of those application proofs.  Applying the combined theorem to an application
requires its `Ready`, validity, and behavioral proofs.  The current concrete
premise proofs cover the constant example.

The proof target and six public axiom reports were checked again during this
review through `tools/leanrun`.  All six reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.  The specification and theorem sources
retain their reviewed contents.

The reviewed validity source has SHA-256:

```text
f37db1d2be31008d85698c1c983509259d590edadc55b956f354c0aad589527e  Spec/Validity.lean
```

[instructions]: https://github.com/WebAssembly/spec/blob/608711107b7f1edb13efd57b7d79b49477462d36/specification/wasm-3.0/2.3-validation.instructions.spectec
[types]: https://github.com/WebAssembly/spec/blob/608711107b7f1edb13efd57b7d79b49477462d36/specification/wasm-3.0/2.1-validation.types.spectec
[modules]: https://github.com/WebAssembly/spec/blob/608711107b7f1edb13efd57b7d79b49477462d36/specification/wasm-3.0/2.4-validation.modules.spectec
