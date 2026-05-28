# Type Classes

This note records the compilation context for Lean type classes and a staged implementation plan for LeanExe.  The target feature is support for ordinary type-class-constrained Lean code when all runtime uses specialize to concrete first-order code.  The first implementation should not add runtime dictionaries, witness tables, dynamic dispatch, closure allocation, or a public ABI for class evidence.

## Implementation Status

The first specialization slice is implemented.  LeanExe now recognizes class evidence through Lean's imported class-extension entries without enabling imported initializer execution, treats that evidence as static in inline-specialized helpers, and runs a bounded normalizer over specialized bodies so method projections reduce to ordinary first-order expressions.  The comparison suite covers built-in `BEq`, a custom `BEq` instance whose method disagrees with structural equality, built-in `Inhabited`, a source-defined `TypeclassScore` class over scalars and structures, a dependent `Option` instance, and a class method inside `Array.foldl`.

Runtime dictionaries remain unsupported.  The generated WASM for this slice should contain ordinary specialized code, and no exported or internal function should receive class evidence as a runtime argument.  If evidence does not normalize to accepted first-order code, the program must reject rather than compile a partial dictionary representation.

## Literature Context

Wadler and Blott introduced type classes as a typed mechanism for ad-hoc polymorphism in Hindley-Milner languages.  Their paper presents type classes as a way to overload operations such as arithmetic and equality while preserving type inference and a formal static account.  The relevant compilation lesson is that overloading can be represented by explicit evidence rather than by untyped name lookup or runtime reflection.  Source: [How to make ad-hoc polymorphism less ad hoc](https://www.research.ed.ac.uk/en/publications/how-to-make-ad-hoc-polymorphism-less-ad-hoc/).

The standard Haskell implementation model is dictionary translation.  A class constraint becomes an extra hidden argument, an instance becomes a dictionary value or a dictionary-building function, and a method call becomes a projection from that dictionary.  Hall, Hammond, Peyton Jones, and Wadler describe Haskell type-class programs as transformed programs that ordinary Hindley-Milner inference can type-check, and they note that the formal rules gave them a compiler blueprint.  Source: [Type Classes in Haskell](https://ropas.snu.ac.kr/lib/dock/HaHaJoWa1996.pdf).

Mark Jones generalized this view through qualified types.  A qualified type carries predicates, and a semantic notion of evidence explains how those predicates compile.  This matters here because Lean elaborates type-class constraints into evidence terms; our compiler can treat those terms as static specialization inputs instead of adding a separate type-class language.  Source: [A theory of qualified types](https://web.cecs.pdx.edu/~mpj/pubs/esop92.html).

GHC keeps dictionary passing as the semantic model but specializes overloaded functions when concrete instances are visible.  Its user guide says functions may be considered for specialization when GHC sees an overloaded function used with concrete type-class instances or when the programmer asks through specialization pragmas.  It also records visibility limits: imported functions need available unfoldings and the right optimization conditions before specialization can happen.  Source: [GHC User’s Guide: When does GHC generate specializations](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/hints.html#when-does-ghc-generate-specializations).

Rust uses monomorphization for ordinary generic code.  The Rust compiler collects concrete instantiations before code generation and emits concrete copies of generic functions; the Rust compiler guide states that assembly is not generic, so the compiler must determine concrete generic types before code can execute.  Rust’s dynamic alternative is a trait object, which pairs a data pointer with a vtable pointer and dispatches through that table at runtime.  Sources: [Rust compiler guide: Monomorphization](https://rustc-dev-guide.rust-lang.org/backend/monomorph.html) and [Rust Reference: Trait object types](https://doc.rust-lang.org/reference/types/trait-object.html).

Go 1.18 uses a hybrid design for generics: dictionaries plus GC-shape stenciling.  A dictionary is statically defined at compile time for a call site and concrete type arguments, and the dictionary supplies information needed by the shape-based instantiation.  This design addresses separate compilation, binary-size, and runtime-shape concerns in Go’s compiler, but LeanExe does not need that machinery for the first type-class slice because it already compiles a closed dependency graph from a checked Lean environment.  Source: [Go 1.18 Implementation of Generics via Dictionaries and Gcshape Stenciling](https://go.googlesource.com/proposal/+/master/design/generics-implementation-dictionaries-go1.18.md).

Lean changes the implementation problem.  Lean’s elaborator already performs instance synthesis, including priority rules, output parameters, and tabled resolution for diamonds and cycles.  The compiler should consume the elaborated declaration and its evidence terms; it should not reimplement instance search or guess which instance a source program meant.  Sources: [Lean Language Reference: Instance Synthesis](https://lean-lang.org/doc/reference/4.22.0-rc4/Type-Classes/Instance-Synthesis/) and [Tabled Typeclass Resolution](https://arxiv.org/abs/2001.04301).

## Design Direction

The first type-class implementation should use static dictionary specialization.  Class evidence should enter extraction as a static argument, in the same broad category as type parameters, proof arguments, and direct lambdas that disappear during specialization.  Method calls should compile only after the evidence term has reduced to a concrete method implementation or to a first-order expression that the existing extractor already accepts.

This design fits the current compiler.  LeanExe already specializes concrete type arguments, erases proof content, inlines some same-root helpers, and rejects higher-order runtime values.  Type classes should extend that specialization path rather than introduce a new runtime representation.  When specialization succeeds, the generated WASM should contain ordinary first-order code with no type-class dictionary argument.

Runtime dictionaries should stay outside the initial design.  They would require dictionary layouts, function-valued fields, indirect calls, ABI rules, ownership rules, and a decision about equality between evidence values.  Those mechanisms solve dynamic dispatch and separate-compilation problems, but they would enlarge the runtime model before we need them.

## Supported First Slice

The first accepted source programs should use concrete, statically known instances.  They should cover built-in classes such as `BEq` and `Inhabited`, plus one source-defined class whose methods return supported values.  They should also cover instances that depend on other instances, because useful Lean code often derives or builds instances compositionally.

Good initial examples include:

| Example | Purpose |
| ------- | ------- |
| `def same [BEq α] (x y : α) : Bool := x == y` called at `UInt64`, `ByteArray`, and a supported structure | Proves method projection through class evidence compiles to the existing equality path. |
| `def contains [BEq α] (needle : α) (xs : Array α) : Bool := xs.any (fun x => x == needle)` called at scalar and structure types | Proves class methods inside direct-lambda array callbacks specialize before extraction. |
| `def defaultOr [Inhabited α] (flag : Bool) (x : α) : α := if flag then x else default` called at `UInt64` and a supported structure | Proves field projection from a class dictionary can produce a supported first-order value. |
| `class Score (α : Type) where score : α -> UInt64` with instances for scalars, structures, and `Option α` | Proves source-defined classes and instance dependencies work without compiler knowledge of the class name. |
| `def total [Score α] (xs : Array α) : UInt64 := xs.foldl (fun acc x => acc + Score.score x) 0` | Proves class methods combine with existing array-fold extraction. |

The first rejection tests should make the boundary precise.  Exported generic entries with unresolved class parameters should reject.  Explicit runtime dictionary parameters whose fields contain functions should reject under the existing higher-order-value rule.  Locally constructed dictionaries that close over runtime values should reject unless the dictionary is fully eliminated by specialization before extraction.  Class methods that return unsupported runtime types should reject at the method result, not at the class declaration.

## Implementation Plan

### 1. Recognize Static Class Evidence

Add a classifier for instance-implicit evidence arguments in extracted declarations and applications.  In Lean, classes are structures, so the implementation should use Lean environment metadata where available rather than match names such as `BEq` or `Inhabited`.  The classifier should treat a parameter as static when its domain is a class application or proof-like evidence and when the parameter is not part of the public ABI.

This step should not compile any new runtime behavior.  It should improve diagnostics by distinguishing unsupported runtime dictionaries from static evidence that the compiler intends to specialize.  The report command should say that class evidence is accepted only as a static specialization input.

### 2. Normalize Evidence Applications

Add a bounded evidence-normalization path for specialized calls.  The normalizer should beta-reduce, unfold transparent same-root helpers, unfold instance constants when needed, reduce structure projections, and reduce class method projections after static evidence is substituted.  It should stop before exposing arbitrary recursive computation or runtime dictionaries.

This normalizer should be reusable by the existing inline-specialization path.  The recent dependent-result beta-reduction work moved in this direction: the classifier must inspect the result after static arguments are substituted and reduced.  Type-class support should apply the same principle to instance evidence and method projections.

### 3. Add Specialization Keys

Extend dependency collection and function extraction so a concrete call can request a specialized version of a generic helper.  The specialization key should include the original declaration name plus normalized static arguments: type parameters, proof arguments that affect reduction, class evidence, and direct-lambda arguments that the compiler treats as static.  Runtime arguments should remain ordinary parameters in the specialized function signature.

The first version can keep specialization intra-module and same-root, matching the current compiler’s conservative dependency model.  Cross-module specialization can come later if the environment exposes enough transparent bodies and the report can explain missing unfoldings.  A useful diagnostic is “class evidence did not specialize to first-order code,” followed by the evidence expression or method projection that remained.

### 4. Lower Method Calls After Specialization

After evidence normalization, a class method call should be an ordinary expression.  It may reduce to a known primitive path such as structural equality, to a source-defined helper call, or to a lambda body that can be inlined at the call site.  The extractor should not contain class-specific cases for `BEq`, `Ord`, `Inhabited`, or source-defined classes unless a built-in primitive already has a generic non-class lowering.

This keeps type classes from becoming a parallel dispatch system inside the compiler.  The compiler’s job is to remove the class abstraction when the checked Lean term supplies static evidence.  Once the abstraction is gone, existing type, value, function-call, pattern-match, and loop extractors decide whether the resulting program belongs to the subset.

### 5. Build Comparison Tests

Every accepted case should compare standard Lean execution with generated WASM under Wasmtime.  The tests should include scalar results, byte-array serialization of structured results, array folds, and a source-defined class with an instance depending on another instance.  The rejected cases should cover unspecialized public class parameters, escaping dictionary values, unsupported method return types, and evidence normalization fuel exhaustion.

The examples should avoid class names in compiler logic.  A source-defined `Score` class is a useful guard because it proves that the implementation handles class evidence generally.  The tests should also include one class method used inside a direct callback, because callback specialization is where dictionary evidence most often leaks into runtime form.

### 6. Update Public Documentation

Update `spec.md` and `manual.md` after the implementation compiles real examples.  The documentation should state that type classes are accepted only when Lean has resolved the instance and the compiler can specialize the resulting evidence away.  It should also state that runtime class dictionaries, exported generic class-constrained functions, and dynamic dispatch remain unsupported.

The user-facing guidance should recommend ordinary Lean style.  Users should write type-class-constrained helpers when that is natural, but the selected WASM entry must still be monomorphic after elaboration.  If the compiler rejects a helper because evidence did not specialize, users should add a concrete wrapper or make the relevant helper body visible to extraction.

## Later Options

Runtime dictionaries would support dynamic evidence values and separate compilation, but they would also add first-class function fields and indirect calls.  Witness tables would give a similar model, with a table per concrete conformance and method dispatch through function pointers.  Either design should wait until a real program requires dynamic dispatch, because the current project goal is checked first-order Lean compiled into small WASM modules.

Cross-module specialization is a better likely next extension than runtime dictionaries.  It would let a program call generic helpers from another module when their unfoldings are available and their instances are concrete.  The GHC experience suggests this needs explicit visibility rules and diagnostics, because specialization depends on whether the compiler can see the overloaded function body and the concrete instance evidence.

## Acceptance Criteria

The first type-class slice is complete when a generic source-defined class and at least two built-in classes compile through concrete wrappers, with standard Lean output matching Wasmtime output.  No generated WASM function should take a class dictionary parameter in this slice.  The report command should classify accepted static evidence and rejected runtime evidence with exact reasons.

The implementation should leave unsupported code rejected rather than partially compiling dictionary records.  It should not add a class-name whitelist.  It should not add a runtime function-table ABI.  It should not implement Lean instance search.
