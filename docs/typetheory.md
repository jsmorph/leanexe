# LeanExe Type Theory and Executable Dialect

LeanExe uses exact Lean 4.34.0-rc2 as its source theory, elaborator, and kernel checker.  It does not define a second surface type system or accept unchecked syntax.  Its own language begins after elaboration: an extractor reads a kernel-checked declaration, removes static material, recognizes a restricted executable fragment, and assigns concrete runtime layouts before lowering the result to a first-order IR and WebAssembly.

The phrase *LeanExe dialect* therefore names two related boundaries.  The checked boundary is Lean 4's dependent type theory, including propositions, universe-polymorphic definitions, dependent functions, inductive families, and proofs.  The executable boundary is the smaller set of elaborated terms for which LeanExe implements extraction, representation, evaluation order, memory management, and an ABI.  A source module may contain declarations outside the executable boundary when they do not contribute runtime behavior to the selected entry.

## Checked source theory

### Lean elaboration and kernel checking

Lean parses notation, resolves names, inserts implicit arguments and coercions, synthesizes type-class instances, elaborates pattern matching and `do` notation, and checks recursive definitions before LeanExe runs.  The Lean kernel checks each declaration's type and value, including universe constraints, dependent application, inductive declarations, and proof terms.  LeanExe imports the resulting environment from the built module and works on `Lean.Expr` values and `ConstantInfo` records rather than source text.

This division assigns different obligations to the two systems.  Lean decides whether a declaration is well typed in Lean's calculus and whether its proof establishes the stated proposition.  LeanExe decides whether the checked executable dependency graph belongs to its implemented subset and whether every retained value has an IR and WASM representation.  Acceptance by Lean is necessary for compilation, while acceptance by LeanExe supplies the additional executable-language judgment.

| Question | Enforcer |
|----------|----------|
| Is the source term well typed, with valid universes and dependent applications? | Lean elaborator and kernel |
| Is an inductive declaration well formed, and is a recursive definition accepted by Lean? | Lean elaborator and kernel |
| Does a theorem prove its proposition? | Lean kernel |
| Can every runtime type and term be represented by the LeanExe IR? | LeanExe extractor |
| Have type parameters, proof arguments, class evidence, and direct callbacks disappeared statically? | LeanExe specialization and extraction |
| Does the entry have an implemented public ABI, and does its reachable code use implemented primitives and recursion shapes? | LeanExe type, dependency, and term classifiers |

### Universes, dependent types, and propositions

The source theory retains Lean's hierarchy of `Sort u`, with `Prop` represented by `Sort 0` and `Type u` by `Sort (u + 1)`.  Dependent function types and universe-polymorphic declarations may occur in the checked module, and Lean checks their level instantiations.  LeanExe assigns no runtime representation to a universe, a sort, a type argument, or a type-level function.  Every type that determines an executable value's layout must reduce, after specialization, to one of the concrete runtime types recognized by the extractor.

Dependent information can influence elaboration and proofs when it disappears before runtime extraction.  Proof-indexed array access is accepted because the bounds proof occupies no runtime slot, and dependent `if` is accepted in recognized forms because each proof binder is erased before branch lowering.  Structure and constructor fields whose types are recognized as propositions are omitted from their runtime layouts.  Indexed inductives, proposition-valued match motives with runtime-dependent results, and branches whose results require different runtime layouts are rejected.

Lean's `Prop` remains the language for program specifications and theorems.  Theorems can describe an executable definition, and proof fields can establish invariants about data, but propositions and proofs cannot cross the public ABI or control computation through a retained proof value.  The extractor recognizes direct proposition sorts and fully applied declarations whose result is a proposition, discards recognized proof fields, and treats recognized proof and evidence arguments as static specialization inputs.  This erasure is implemented by the extractor and tested on proof-bearing structures, but the repository has no general mechanized proof that extraction preserves all accepted Lean terms.

### Inductive definitions and recursion

Lean checks the formation and recursive use of source inductive types.  LeanExe then imposes representation restrictions on the checked declarations.  A runtime structure must be a nonrecursive, non-indexed, single-constructor inductive with concrete supported type arguments and supported runtime fields.  A nonrecursive tagged inductive must be non-indexed, have at least one constructor, and have supported fields after type-parameter substitution.

Recursive inductive values are available only inside compiled code.  LeanExe accepts monomorphic self-recursive types, selected monomorphic instances such as `List α`, and mutual recursive families whose specialized members and fields fit the recursive layout rules.  Each recursive value occupies one heap-pointer slot, while constructors store tags and fields in the pointed-to object.  Recursive values may pass through helpers, local structures, tagged values, internal arrays, loops, and branch results, but no recursive value may occur anywhere in a public entry layout.

LeanExe recognizes specific elaborated recursion forms rather than implementing Lean's full recursor language.  It accepts direct structural recursion over supported recursive fields, selected expression-position structural traversals, closed list-shaped folds and predicates, first-`Nat` fuel recursion, one array-descent `WellFounded.fix` form, and one nested-`PSum` form generated for supported mutual structural recursion.  A direct callback or captured first-order value may become an explicit parameter of a synthetic helper, preserving a first-order call graph.  Arbitrary well-founded recursion, unsupported course-of-values projections, sparse recursive match helpers, and recursive functions whose generated form falls outside those recognizers are rejected even when Lean has proved them terminating.

## Executable fragment

### Static and runtime terms

LeanExe classifies elaborated material as static, erased, inline-specialized, or runtime.  Universe levels, type arguments, recognized proofs, class evidence, and selected direct lambdas can act as static inputs to specialization.  Retained runtime terms must lower to the first-order IR in `LeanExe/IR/Core.lean`, whose functions contain numbered scalar slots, direct function calls, expressions, statements, branches, loops, traps, allocation operations, and release operations.  The IR has no term constructor for a type, proof, closure, class dictionary, indirect call, or effect handler.

The following table records the runtime type constructors implemented by the IR and the main public-boundary restriction.  A supported field still depends on its position: internal layouts admit products and recursive pointers that the public ABI rejects.  Fixed-width means that the extractor can calculate a constant number of `i64` slots for every value of the type.

| Source type | Internal interpretation | Public entry use |
|-------------|-------------------------|------------------|
| `Unit`, `PUnit` | Erased sequencing value, represented by a zero scalar when a slot is required | Rejected as parameter or result |
| `Bool` | One constrained scalar, `0` or `1` | Parameter and result |
| `UInt8`, `UInt32`, `UInt64` | One unsigned scalar with the source width's arithmetic rules | Parameter and result |
| `Nat` | One bounded unsigned scalar | Parameter and result, subject to the bounded semantics below |
| `ByteArray` | Owner, data pointer, and length | Pointer and length at the public ABI |
| `Array α` | Owner and pointer to a length header plus fixed-width elements | One pointer when `α` has a supported public fixed-width layout |
| `Prod α β` | Concatenated internal layouts | Internal only |
| `PSum α β` | Tag followed by both payload layouts | Internal only |
| Nonrecursive structure | Runtime fields in Lean declaration order after proof erasure | Flattened fields when no recursive value occurs |
| Nonrecursive inductive, `Option`, `Except` | Constructor tag followed by constructor payload areas | Flattened tag and payloads when no recursive value occurs |
| Recursive inductive, including supported `List` instances | One pointer to a tagged heap object | Internal only |
| `String` | Compile-time ASCII expression in a small recognized set | No runtime value |

Arrays, structures, and tagged values can contain heap-bearing fields when their flattened layout remains fixed width.  Public arrays may contain byte arrays, nested arrays, structures, nonrecursive inductives, `Option`, and `Except`, including combinations of those types that contain no recursive inductive value.  Internal arrays additionally admit products and recursive pointers.  Recursive structures, indexed inductives, runtime `String`, runtime `Char`, signed integers, floating-point values, and an arbitrary-precision runtime representation of `Nat` have no LeanExe runtime type.

### Functions, lambdas, and specialization

An exported entry is a named, closed executable declaration whose runtime parameters and result have supported public layouts.  An ordinary retained helper has supported internal parameter and result layouts and becomes a direct IR function.  Helpers normally reside under the imported module's root namespace, while external calls compile only when LeanExe implements the declaration as a primitive.  An executable declaration marked `unsafe` or `partial`, or one without an inspectable executable value, is rejected.

Functions are not runtime values in this dialect.  A lambda used directly as a fold, map, predicate, monadic continuation, or specialization argument can be beta-reduced or copied into the corresponding first-order body.  Some expression-position structural recursion becomes a synthetic direct-call helper whose captured supported values are explicit parameters.  A lambda that escapes normalization, a function-valued field or accumulator, a named callback that remains data, or a function in an entry signature requires a closure or indirect call and is rejected.

Polymorphism follows the same static rule.  A parametric structure or inductive is accepted at a concrete supported instantiation, and a local first-order polymorphic helper can be inline-specialized when every runtime binder acquires a concrete supported type.  LeanExe substitutes static type, proof, evidence, and direct-lambda arguments, then extracts the specialized body.  It does not emit a shared generic function whose layout depends on runtime type arguments, and it rejects unspecialized polymorphic values.

Lean performs type-class instance synthesis before extraction.  LeanExe treats resolved class evidence as a static argument, substitutes the elaborated evidence term, and uses a bounded normalizer to reduce method projections to supported first-order code.  The accepted fixtures include `BEq`, `Inhabited`, a source-defined class, a dependent instance for `Option α`, and class methods inside direct array and list operations.  Runtime dictionaries, unresolved public constraints, dynamic method dispatch, and evidence whose function-valued fields survive normalization are rejected.

### Pure control, state syntax, and effects

The runtime fragment implements pure `let`, direct calls, conditionals, dependent conditionals with erased proof binders, constructor formation, projection, matching, and recognized recursion.  It also implements `Id.run` blocks whose mutable syntax elaborates to supported local bindings and first-order continuations.  `for` and `while` forms compile when Lean elaborates them to the recognized `ForIn.forIn` or `Lean.Loop` forms over byte arrays, fixed-width arrays, or legacy ranges, with `Id`, `Option`, or `Except ε` as the recognized monad.  The resulting mutation is local IR state and preserves the source value semantics of arrays and byte arrays through fresh allocation for updates.

`Option` and `Except` are tagged data, and their accepted `do` notation lowers to first-order matching and short-circuiting.  They do not introduce environmental effects.  LeanExe rejects executable dependencies on `IO`, `EIO`, `BaseIO`, `Task`, files, environment variables, clocks, randomness, concurrency, reflection, and FFI.  WASI command modes place fixed input, output, error, argument, and exit adapters around a pure accepted entry, so those imports belong to the generated wrapper rather than the Lean source function.

The definitions under `LeanExe.Runtime` form an explicit semantic exception.  Ordinary Lean evaluation treats the four counter reads and `release` as pure functions returning zero, while generated WASM reads or changes allocator state.  The IR reference interpreter also treats those operations as zero-valued no-ops.  Standard-Lean differential claims therefore exclude observable use of these intrinsics, and artifact proofs or Wasmtime execution must establish their generated behavior separately.

### Equality and decidability

Propositional equality remains Lean's `Eq` in `Prop`, and Lean checks every theorem about it.  A runtime branch on a decided equality compiles only when the compared type has an implemented equality operation and the required `Decidable` evidence specializes away.  Boolean equality through `BEq` follows the selected elaborated instance, including a source-defined instance whose behavior differs from structural equality.  The compiler must not replace such an instance with structural comparison unless specialization yields that implementation.

Implemented runtime equality includes supported scalars, byte arrays, fixed-width arrays with supported element equality, products, structures, internal sums, `Option`, `Except`, and nonrecursive tagged values whose retained fields support equality.  Structure comparison follows runtime field order, and tagged comparison checks the constructor tag before active payload fields.  Array and byte-array comparison checks lengths before scanning elements.  Recursive-inductive equality and arrays requiring recursive-inductive element equality are rejected.

Decidable propositions form a narrower executable set than Lean's `Decidable` type permits.  Recognized scalar comparisons, equality propositions, and selected combinations of `And`, `Or`, and `Not` lower to IR conditions, while proof terms and decision evidence remain static.  A dependent `if` may bind its proof for source typing, but the binding has no runtime identity or slot.  An arbitrary user decision procedure compiles only when specialization reduces it to otherwise accepted first-order operations.

## Runtime interpretation

### Numeric and value semantics

`UInt8`, `UInt32`, and `UInt64` retain their fixed-width unsigned meaning.  The narrow integers normalize at public entry and result boundaries, arithmetic wraps at their declared width, and shifts mask the shift count by that width.  `UInt64` occupies the native WASM `i64` bit pattern, including values whose command-line decimal presentation may appear signed in a host tool.

Lean's source `Nat` is unbounded, while LeanExe represents runtime `Nat` in one unsigned 64-bit slot.  Runtime literals must fit unless a directly consuming fixed-width conversion defines modulo reduction.  Subtraction saturates, division by zero returns zero, and remainder by zero returns the dividend.  Addition, multiplication, and successor trap on overflow, so a source theorem about arbitrary `Nat` transfers to compiled execution only under the representation and no-overflow conditions required by the compiled path.

Structures flatten their retained fields in declaration order.  A nonrecursive inductive stores its constructor index followed by payload slots reserved for every constructor, with inactive areas ignored.  A recursive inductive stores one pointer to a heap object that contains its tag and retained fields.  These representations erase source type identity at runtime except where layout, tag order, and direct-call signatures encode it.

### Memory, ownership, and the ABI

Every scalar ABI component uses a WASM `i64` slot.  Byte arrays cross the public boundary as a data pointer and length, arrays cross as a pointer to a length-prefixed element region, and structures and nonrecursive inductives use their flattened slot sequences.  Internal byte arrays and arrays add owner slots, while recursive objects live behind reference-counted pointers.  Public entry layouts reject every recursive pointer, even when nested inside a structure, tag, option, exception, or array.

The source language gives arrays and byte arrays persistent value semantics.  LeanExe implements updates by allocation and copying, preserves borrowed or owned roots through owner slots, and uses child-pointer masks so release can follow heap references.  The compiler inserts releases at conservative, type-directed points and validates explicit `LeanExe.Runtime.release` uses through provenance and final-use rules.  Lean's type theory does not express linear ownership here, and the repository has no mechanized soundness theorem for the ownership analysis.

The public ABI also defines behavior outside Lean's type system.  A host must provide correctly flattened values, valid pointers, sufficient memory, and the ownership discipline described in the [language specification](spec.md).  Malformed host values, stale pointers after `reset`, and unretained aliases after release lie outside the source semantics.  WASI adapters validate their configured byte and argument bounds, but they do not turn arbitrary external memory into a Lean-typed value.

### Evaluation, traps, and termination

LeanExe preserves source evaluation order for accepted expressions, including lazy projection, short-circuiting, and single evaluation of a multi-slot helper result.  Demand analysis determines when strict argument materialization is safe and when an unused field or branch must remain unevaluated because it may trap.  Bang indexing and other accepted partial operations lower failure to WASM `unreachable`, while safe indexing returns a tagged `Option` without reading an out-of-bounds payload.

Rejecting `partial` declarations does not supply a general artifact termination theorem.  Structural and well-founded recursive definitions have passed Lean's termination checks, fuel recursion makes exhaustion part of the source behavior, and a generated `while` loop follows its checked elaborated form.  A behavioral artifact theorem can prove termination for an entry under stated input and memory premises.  The general compiler has no theorem proving termination or semantic preservation for every accepted entry.

## Rejection boundary and assurance

LeanExe rejects a declaration when any runtime-relevant dependency lacks a recognized type, term form, primitive, specialization, recursion shape, effect policy, ownership judgment, or ABI layout.  The rejection boundary applies to the selected executable graph rather than every declaration in the imported module.  The `report` command classifies the entry and its reachable declarations, while `compile` performs the complete body and lowering checks.  A successful Lean check followed by a LeanExe rejection means the program is valid Lean outside this executable dialect.

| Rejected category | Current boundary |
|-------------------|------------------|
| Dependent runtime data | Indexed inductives, dependent runtime result layouts, proposition-valued runtime motives, and public proof values |
| Higher-order runtime behavior | Closures, indirect calls, escaping lambdas, function-valued fields or accumulators, and function-valued entry parameters or results |
| Generic runtime behavior | Unspecialized polymorphism, runtime type representations, runtime class dictionaries, and dynamic method dispatch |
| Effects | `IO`, `EIO`, `BaseIO`, `Task`, environmental access, concurrency, reflection, and FFI |
| Untrusted executable declarations | `unsafe`, `partial`, opaque executable constants, executable axioms, and quotient dependencies |
| Unsupported data and arithmetic | Runtime `String`, runtime `Char`, signed integers, floating point, arbitrary-precision runtime `Nat`, recursive structures, indexed inductives, and public recursive values |
| General recursion and libraries | Recursor shapes outside the implemented recognizers and external Lean or Std declarations without a primitive or successful specialization |

The implementation provides three distinct kinds of evidence.  Lean kernel checking establishes the well-typedness of the imported source declarations and their proofs.  Differential tests compare many accepted programs with standard Lean execution, subject to the bounded `Nat`, trap, ABI, and runtime-intrinsic qualifications.  Exact-artifact Talos theorems establish properties of identified WASM binaries, but the repository has no general theorem connecting every accepted Lean declaration to the emitted artifact.

All source and proof claims inherit the trust properties of their pinned Lean kernel.  The compiler root and artifact proof workspace now pin exact Lean 4.34.0-rc2, and the proof workspace pins pre-floating-point Talos revision `fda69ca67a81ea4f1fa4e376bdc5861d9fe5479a`.  The known Lean 4.31.0 kernel-unsoundness record described in the [artifact verification format](artifact-format.md) remains historical evidence for the earlier release inputs, not evidence for this migration.  The aggregate proof and conformance gates must be refreshed before the migrated inputs support a release claim.

The implemented dialect is therefore precise at the extraction boundary but incomplete as a formal metatheory.  Its type recognition, erasure, specialization, evaluation-order analysis, ownership decisions, IR lowering, and WASM emission are executable compiler code with extensive tests.  Lean proves source theorems, and the artifact verifier proves selected binary theorems, while a general `extract_correct` or source-to-WASM refinement theorem remains future work.
