# Type Theory of the LeanExe Fragment

## Scope and judgments

LeanExe accepts checked Lean declarations through a representation and extraction discipline.  This document gives that discipline mathematical notation, runtime type-formation rules, and a typed first-order presentation.  The [Formal Specification](leanexe-formal-specification.md) defines compilation, memory, numeric behavior, and execution.  The [Language Specification](spec.md) and [User Manual](manual.md) describe the source forms.

The definitions below combine independently stated runtime typing rules with an implementation-indexed acceptance relation.  Central acceptance premises, including recursor recognition and expression extraction, refer to implementation function graphs.  The document therefore specifies the implementation while leaving an independent formalization and its equivalence proof open.  It has no accompanying mechanized metatheory.  A rule marked “implemented” names the executable predicate that fixes its premises.  A proposed preservation statement appears only under proof obligations.

Let `E` be a checked Lean environment, `Γ` a Lean local context, `Ξ` a first-order function-signature context, and `Δ` a context of runtime variables.  Let `v` identify the exact compiler source and pinned Lean toolchain.  The judgments have distinct subjects:

| Judgment | Meaning |
|----------|---------|
| `E; Γ ⊢Lean e : A` | The pinned Lean kernel accepts the term and its type. |
| `E ⊢v A ⇝ τ` | LeanExe recognizes `A` as runtime type `τ`. |
| `E ⊢v A erase` | The extractor's proof-type recognizer accepts `A` for erasure. |
| `E ⊢v A static(a)` | Argument `a` is an accepted static specialization input for domain `A`. |
| `τ ∈ I`, `τ ∈ P`, `τ ∈ Apub` | `τ` has an internal, public entry, or public array-element representation. |
| `Ξ; Δ ⊢ e : τ` | An abstract first-order term has runtime type `τ`. |
| `E; C; B; n ⊢v e ⇝ V; n′` | The expression extractor returns value description `V` and next local index `n′`. |
| `E ⊢v (m, f, mode) ⇝ M` | Complete extraction of entry `f` from module `m` returns IR module `M`. |

`C` contains the root namespace, function indices, synthetic helpers, ownership summaries, and inline stack.  `B` is the extractor's binding list.  `V` is an `ExtractedValue`, which may retain deferred expressions and multi-slot bindings.  These objects are defined by [Extractor Data](../LeanExe/Extract/Types.lean), declarations `Context`, `Binding`, and `ExtractedValue`.

The abstract typing judgment gives the type structure of runtime computation.  The implemented extraction judgment adds syntactic, dependency, specialization, demand, recursion, and ownership premises.  Abstract typing alone is insufficient for compilation.

## Lean foundation

### Kernel terms

Lean supplies dependent function types, universes, inductive declarations, recursors, definitional equality, and propositions.  Its elaborator supplies explicit type arguments, instance terms, generated matches, and checked recursion to the imported environment.  This document takes the pinned kernel judgment as a parameter.  The [Lean Type-System Reference](https://lean-lang.org/doc/reference/latest/The-Type-System/) describes that judgment.  The exact toolchain is recorded in [Toolchain Pin](../lean-toolchain).

The familiar kernel rules remain available when constructing and proving the source program.  In schematic form:

```text
x : A ∈ Γ                         E; Γ ⊢Lean f : (x : A) → B
──────────────                    E; Γ ⊢Lean a : A
E; Γ ⊢Lean x : A                  ───────────────────────────
                                  E; Γ ⊢Lean f a : B[a/x]

E; Γ, x : A ⊢Lean b : B           E; Γ ⊢Lean a : A
────────────────────────          E; Γ, x : A ⊢Lean b : B
E; Γ ⊢Lean (fun x => b)           ───────────────────────────
             : (x : A) → B        E; Γ ⊢Lean (let x := a; b) : B[a/x]
```

The usual well-formed-context and well-formed-type premises are implicit in this display.  Conversion uses the pinned kernel's definitional-equality check.  Its algorithm is separate from LeanExe's bounded normalization and type recognition.

A Lean theorem can mention types and terms that have no runtime representation.  LeanExe extracts one executable dependency graph, so unrelated proofs and definitions in the imported module impose no runtime type requirement.  Executable source declarations must satisfy the checks in `supportedEntryFunction?`, `supportedFunction?`, and the body extractor.  These include safety, the absence of `partial`, and the availability of `ConstantInfo.value?`.  Lean's default `value?` excludes opaque bodies.

### Recognition and erasure

The implemented recognition judgments are function graphs:

```text
E ⊢v A ⇝ τ       iff  typeAtom? E A = some τ
E ⊢v A erase     iff  isProofType? E A = true
E ⊢v A static(a) iff  staticInlineArg E A a = true.
```

All three functions occur in [Type Recognition](../LeanExe/Extract/Types.lean).  These definitions retain the implementation's syntactic boundary.  Kernel-definitional equality of `A` and `B` does not establish that both recognizers return the same result.

`isProofType?` consumes metadata, recognizes `Sort 0`, follows the result of `forallE`, and recognizes sufficiently applied constant heads whose declared result is a proposition.  It is a specific recognizer for erased fields and specialization domains.  An assertion that it recognizes every kernel proposition would require a separate completeness theorem.

For a constructor field list `A₁, …, Aₙ`, define:

```text
eraseFieldsE([]) = []
eraseFieldsE(A :: As) = eraseFieldsE(As)             if E ⊢v A erase
eraseFieldsE(A :: As) = τ :: eraseFieldsE(As)        if E ⊢v A ⇝ τ
```

The first applicable clause has priority.  Failure of both premises rejects the layout.  The real constructor recognizers also check parameter count, constructor identity, and field count.  Proof fields therefore occupy zero runtime slots, while `Unit` occupies one slot when it survives as a runtime value.

## Runtime types

### Syntax and formation

The grammar follows `LeanExe.IR.Ty` in [IR Definition](../LeanExe/IR/Core.lean):

```text
τ ::= Unit | Bool | U8 | U32 | U64 | Nat64 | Bytes
    | Array τ | τ × τ | PSum τ τ
    | Struct S τ̄ [τ̄fields]
    | Variant D τ̄ [τ̄₀; …; τ̄k−1]
    | Rec D τ̄.
```

`Nat64` names the bounded runtime interpretation of Lean `Nat`.  `S` and `D` retain the Lean declaration name.  The type-argument list `τ̄` identifies a concrete specialization.  `Option τ` abbreviates `Variant Option [τ] [[]; [τ]]`, and `Except ε τ` abbreviates `Variant Except [ε, τ] [[ε]; [τ]]`.  `Unit` also represents recognized `PUnit` sequencing.

Primitive recognition has the following rules:

```text
E ⊢v Unit ⇝ Unit        E ⊢v PUnit ⇝ Unit
E ⊢v Bool ⇝ Bool        E ⊢v UInt8 ⇝ U8
E ⊢v UInt32 ⇝ U32       E ⊢v UInt64 ⇝ U64
E ⊢v Nat ⇝ Nat64        E ⊢v ByteArray ⇝ Bytes

E ⊢v A ⇝ τ             E ⊢v A ⇝ τ    E ⊢v B ⇝ υ
────────────────       ─────────────────────────
E ⊢v Array A ⇝ Array τ  E ⊢v Prod A B ⇝ τ × υ
```

The analogous two-premise rules form `PSum` and `Except`.  `Option` has one premise.  `typeAtom?` also recognizes a generated `PSum.casesOn` type expression when its two one-binder arms both yield the same recognized runtime type.  That narrow rule supports generated mutual-recursion machinery.

For a structure application `S Ā`, formation requires all of the following:

1. `S` is registered as a structure, has no indices, has one constructor, and has `isRec = false`.
2. `S` is neither a registered class nor an excluded evidence-carrier name.
3. The number of arguments equals the declared parameter count, and every `Aᵢ` is recognized as `τᵢ`.
4. Substituting those concrete parameters into the constructor fields succeeds.  Every field erases or has a recognized runtime type.  Field counts agree with the structure metadata.

Then `E ⊢v S Ā ⇝ Struct S τ̄ eraseFieldsE(fields)`.  The executable premises are `structureInductiveInfo?`, `structureCtorInfo?`, `ctorFieldDomainsWithParams?`, and `structureFieldKindsWithParams?`.

A nonrecursive inductive follows the same parameter and field rules, requires at least one constructor and no indices, and records every constructor's runtime fields in declaration order.  It uses `userInductiveInfo?` and `variantLayoutWithParams?`.  Built-in types handled by dedicated rules are excluded from the generic recognizer.

### Recursive families

A recursive type uses one pointer slot.  `recursiveFamilyNames?` requires every family member to name the same family, have the same parameter count, have no indices, and satisfy `userRecursiveInductiveInfo?`.  Each occurrence of a family member must use the same concrete parameter list.

The field recognizer `typeAtomRecursiveField?` descends through `Array`, `Prod`, `PSum`, `Option`, and `Except`.  A direct family occurrence becomes `Rec D τ̄`.  Other field expressions fall back to `typeAtom?`, with a directly returned recursive type from another family rejected by that fallback.  The exact recognizer governs compound fields recognized by the fallback.  This statement avoids assuming closure under arbitrary new type constructors.

Lean has checked inductive formation and recursive definitions before these representation checks.  A successful recursive layout supplies constructor tags and pointer fields.  Accepted traversal still requires one of the recursor shapes in the term-extraction rules.

### Position-sensitive representation

Define `I` as the internal layout domain, `Apub` as the public array-element domain, and `P` as the public parameter/result domain:

```text
τ ∈ I     iff valueLayout? τ returns a layout
τ ∈ Apub  iff supportedPublicArrayElementType τ = true
τ ∈ P     iff supportedParamAbiType τ = true.
```

`supportedResultAbiType` defines the same public grammar in this revision.  Internal array elements use `arrayElementLayout?`, whose grammar has the same constructors as `valueLayout?`.  Public and internal rules are:

| Type | `I` | `Apub` | `P` |
|------|-----|--------|-----|
| `Unit` | Yes | No | No |
| `Bool`, `U8`, `U32`, `U64`, `Nat64` | Yes | Yes | Yes |
| `Bytes` | Yes | Yes | Yes |
| `Array τ` | `τ ∈ I` | `τ ∈ Apub` | `τ ∈ Apub` |
| `τ × υ`, `PSum τ υ` | Both components in `I` | No | No |
| `Struct S τ̄ fs` | Every field in `I` | Every field in `Apub` | Every field in `P` |
| `Variant D τ̄ cs` | Every constructor field in `I` | Every constructor field in `Apub` | Every constructor field in `P` |
| `Rec D τ̄` | Yes | No | No |

The quantification over fields includes inactive constructors.  Thus a public tagged type is rejected if any constructor contains an internal-only field.  Empty runtime field lists satisfy the universal field condition and contribute zero payload slots.

Let `wI` and `wP` count internal and public slots.  For supported positions:

```text
wI(Unit) = wI(Bool) = wI(U8) = wI(U32) = wI(U64) = wI(Nat64) = 1
wI(Bytes) = 3                    wP(Bytes) = 2
wI(Array τ) = 2                  wP(Array τ) = 1
wI(Rec D τ̄) = 1
wI(τ × υ) = wI(τ) + wI(υ)
wI(PSum τ υ) = 1 + wI(τ) + wI(υ)
wX(Struct S τ̄ fs) = Στ∈fs wX(τ)
wX(Variant D τ̄ cs) = 1 + Σfs∈cs Στ∈fs wX(τ),  X ∈ {I, P}.
```

Every public scalar has width one.  Public array contents use `wI` for element storage, including owner slots inside elements.  The entry's array pointer has public width one regardless of element width.  `internalSlots`, `abiSlots`, and the layout recognizers implement these equations.  A numeric result from `abiSlots` on an unsupported type supplies no public-type derivation.

## First-order terms

### Typed presentation

The following abstract syntax presents the runtime computations recognized after specialization:

```text
e ::= x | literalτ(n) | unit
    | let x = e in e | if c then e else e
    | constructD,k(ē) | projectS,j(e) | pair(e,e) | projectPairj(e)
    | match e with { k(x̄k) => ek }k
    | call f(ē) | primitivep(ē)
    | foldκ(ē; x̄ => e) | recurseκ(ē) | trapτ
c ::= true | false | equalτ(e,e) | lessτ(e,e) | lessEqualτ(e,e)
    | not c | and c c | or c c.
```

`κ` is a recognized collection, loop, or recursion shape.  Its body binder denotes code substituted into a first-order body.  This notation has no runtime function-value constructor.  A complete application uses the signature context `Ξ(f) = (τ₁, …, τₙ) → τ`:

Runtime contexts satisfy `[] wf` and `Δ wf ∧ τ ∈ I ∧ x ∉ dom(Δ) ⇒ Δ,x:τ wf`.  A well-formed `Ξ` assigns each distinct function name one finite parameter list and result in `I`.  An exported signature additionally requires every parameter and its result in `P`.  Every judgment below assumes these context conditions.

```text
x : τ ∈ Δ                         Ξ; Δ ⊢ ai : τi  for every i
──────────────                    Ξ(f) = (τ₁, …, τₙ) → τ
Ξ; Δ ⊢ x : τ                      ─────────────────────────
                                  Ξ; Δ ⊢ call f(ā) : τ

Ξ; Δ ⊢ a : τ                     Ξ; Δ ⊢ c : Bool
Ξ; Δ, x : τ ⊢ b : υ              Ξ; Δ ⊢ t : τ    Ξ; Δ ⊢ u : τ
────────────────────             ────────────────────────────
Ξ; Δ ⊢ let x = a in b : υ         Ξ; Δ ⊢ if c then t else u : τ
```

Constructor, projection, and match rules use explicit contexts.  Write `fields(S) = [τ₁,…,τₙ]`, and write `ctors(D)[k] = [τk,1,…,τk,nk]` for a concrete recognized specialization.  For recursive data, that list may contain family-member pointer types.  The rules are:

```text
fields(S) = [τ₁,…,τₙ]           Ξ; Δ ⊢ ai : τi  for every i
───────────────────────────────────────────────────────────
Ξ; Δ ⊢ constructS(a₁,…,aₙ) : Struct S τ̄ fields(S)

Ξ; Δ ⊢ a : Struct S τ̄ fields(S)       fields(S)[j] = τj
──────────────────────────────────────────────────────────
Ξ; Δ ⊢ projectS,j(a) : τj

0 ≤ k < length(ctors(D))         Ξ; Δ ⊢ ai : τk,i  for every i
────────────────────────────────────────────────────────────
Ξ; Δ ⊢ constructD,k(ā) : Dτ̄

Ξ; Δ ⊢ a : Dτ̄                  τ ∈ I
Ξ; Δ, xk,1 : τk,1, …, xk,nk : τk,nk ⊢ ek : τ  for every constructor k
───────────────────────────────────────────────────────────────────
Ξ; Δ ⊢ match a with { k(x̄k) => ek }k : τ

Ξ; Δ ⊢ a : τ     Ξ; Δ ⊢ b : υ       Ξ; Δ ⊢ p : τ × υ
──────────────────────────────       ──────────────────
Ξ; Δ ⊢ pair(a,b) : τ × υ              Ξ; Δ ⊢ projectPair1(p) : τ
```

Here `Dτ̄` is the recognized `Variant` or `Rec` type.  Pattern variables are fresh and local to their arm.  The second product projection has result `υ`.  `PSum` has constructors with one field and the corresponding two-arm match rule.  Unit and Boolean constructors have no field binders.  Nat matching has a zero arm in `Δ` and a successor arm in `Δ,x:Nat64`.  These Nat arms describe one case split; recursive use adds a recognized recursion premise.

The Boolean condition forms require their declared scalar comparison types or an implemented equality type.  `trapτ` is a terminal failure at any represented result type, with rule `τ ∈ I ⇒ Ξ; Δ ⊢ trapτ : τ`.  [Value Operations](../LeanExe/Extract/Values.lean), `trapValue`, constructs the corresponding extraction shape.

These rules state typing, including the necessary branch agreement.  Accepted source syntax is fixed by the extraction graph below.  A generated sparse matcher, dependent motive, or recursor must satisfy its own recognizer even when its abstract translation has a typing derivation.

### Primitive signatures and code binders

Let `Num = {U8,U32,U64,Nat64}`.  Define `EqTy` as the least family containing `Unit`, `Bool`, all numeric types, and `Bytes`, closed under arrays, products, `PSum`, structures, and nonrecursive variants when all components belong to `EqTy`.  This is the structural-equality type domain.  A source `BEq` call also carries its selected elaborated instance: a custom instance requires successful specialization to its own body.  [Demand Analysis](../LeanExe/Extract/Demand.lean), `structuralEqValueExpr`, and [Expression Extraction](../LeanExe/Extract/Core.lean), `structuralBEqEvidence?`, fix that distinction.

The table gives runtime signatures after erasing static type and proof arguments.  `τ,υ,α,ε ∈ I`, and array element layouts must be supported.  A `code` argument denotes a binder in the following rule, not a runtime function slot.

| Primitive family | Runtime signature or code-binder signature |
|------------------|---------------------------------------------|
| Numeric add, subtract, multiply, divide, remainder | `ν × ν → ν`, `ν ∈ Num` |
| Numeric less and less-or-equal | `ν × ν → Bool`, `ν ∈ Num` |
| Structural equality | `τ × τ → Bool`, `τ ∈ EqTy` |
| Boolean conjunction, disjunction, XOR | `Bool × Bool → Bool` |
| Boolean negation | `Bool → Bool` |
| Fixed-width bitwise AND, OR, XOR, shifts | `Uw × Uw → Uw`, `w ∈ {8,32,64}` |
| Fixed-width complement | `Uw → Uw` |
| Numeric conversions | `ν → υ` for distinct `ν,υ ∈ Num`, through the implemented `ofNat`, `toNat`, and fixed-width conversion names |
| Boolean conversion | `Bool → Nat64` |
| Nat successor and predecessor | `Nat64 → Nat64` |
| Numeric minimum and maximum | `ν × ν → ν`, `ν ∈ Num`, through recognized `Min.min` and `Max.max` applications |
| Binary64 add, subtract, multiply, divide | `U64 × U64 → U64` |
| Binary64 square root | `U64 → U64` |
| Array size and emptiness | `Array τ → Nat64` and `Array τ → Bool` |
| Array read, safe read, default read | `Array τ × Nat64 → τ`, `Array τ × Nat64 → Option τ`, and `Array τ × Nat64 × τ → τ` |
| Array set and insert | `Array τ × Nat64 × τ → Array τ` |
| Array modify | `Array τ × Nat64; code(x:τ) : τ → Array τ` |
| Array erase | `Array τ × Nat64 → Array τ` |
| Array push, pop, append | `Array τ × τ → Array τ`, `Array τ → Array τ`, and `Array τ × Array τ → Array τ` |
| Array extract, swap, reverse | `Array τ × Nat64 × Nat64 → Array τ`, and `Array τ → Array τ` for reverse |
| Array replicate | `Nat64 × τ → Array τ` |
| Array map | `Array τ; code(x:τ) : υ → Array υ` |
| Array filter, find, optional find-index, any, all | `Array τ; code(x:τ) : Bool → Array τ`, `Option τ`, `Option Nat64`, `Bool`, or `Bool`, respectively |
| Byte size, empty, read, safe read | Array signatures specialized to bytes, with `Bytes` as collection and `U8` as element |
| Byte push, append, set, extract | Corresponding byte-sequence signatures, with `U8` payloads and `Nat64` indices |
| Byte copy slice | `Bytes × Nat64 × Bytes × Nat64 × Nat64 → Bytes` |
| Eight-byte endian conversion | `Bytes → U64` |
| Pure left fold | `Array τ × α; code(a:α,x:τ) : α → α`; byte fold uses `Bytes` and `U8` |
| Pure right array fold | `Array τ × α; code(x:τ,a:α) : α → α` |
| Monadic left fold | `Array τ × α; code(a:α,x:τ) : F α → F α`, `F ∈ {Option, Except ε}`; byte fold is analogous |
| Option map and bind | `Option τ; code(x:τ) : υ → Option υ`, or `code(x:τ) : Option υ → Option υ` |
| Option filter, any, all | `Option τ; code(x:τ) : Bool → Option τ`, `Bool`, or `Bool`, respectively |
| Option default, tests, and elimination | `Option τ × τ → τ`; `Option τ → Bool`; `Option τ × υ; code(x:τ) : υ → υ` |
| Except map and bind | `Except ε τ; code(x:τ) : υ → Except ε υ`, or `code(x:τ) : Except ε υ → Except ε υ` |
| Except map-error | `Except ε τ; code(x:ε) : υ → Except υ τ` |
| Except conversion and tag test | `Except ε τ → Option τ` and `Except ε τ → Bool` |
| Option/Except fallback | `F τ; code(unit:Unit) : F τ → F τ`, `F ∈ {Option, Except ε}` |
| Runtime counter reads | `() → U64` |
| Explicit runtime release | `Array τ → U64` or `Rec D τ̄ → U64`, with the ownership judgment |

Optional fold/search bounds contribute `Nat64` arguments in the recognized source form.  The table groups wrappers with the same payload signature; a wrapper's exact bounds and failure behavior appear in the [Formal Specification](leanexe-formal-specification.md#collections-and-iteration).  `extractPrimitivePairFrom` in [Expression Extraction](../LeanExe/Extract/Core.lean) selects numeric operators, while `extractValueFrom` contains conversion and collection dispatch.

For any registered code-bearing operation `p` with ordinary argument types `τ̄`, code-binder types `ῡ`, code result `α`, and result `β`, its typing rule is:

```text
Ξ; Δ ⊢ ai : τi  for every i
Ξ; Δ, x₁:υ₁,…,xk:υk ⊢ body : α
──────────────────────────────────────────
Ξ; Δ ⊢ p(ā; x̄ => body) : β.
```

The callback variables are fresh.  The body may use variables in `Δ`; later specialization or synthetic-helper construction must account for those captures.  This rule covers a typed code block without introducing a runtime arrow type.  `foldκ` and `recurseκ` remain schematic families for elaborated shapes whose complete independent inference rules are future work.  Their implemented acceptance is fixed by the recognizers in the coverage table.

### Specialization

Let a helper type be `(x₁ : A₁) → … → (xₙ : Aₙ) → B`, with arguments `ā`.  The implemented specialization processes the binders in source order.  Before classifying binder `i`, it substitutes `a₁, …, aᵢ₋₁` into `Aᵢ` and applies `betaReduceExpr 32`.

```text
E ⊢v Ai[a<i/x<i] ⇝ τi     τi ∈ I
──────────────────────────────────  Runtime binder
(xi : Ai, ai) ↦ runtime(τi, ai)

type recognition fails     E ⊢v Ai[a<i/x<i] static(ai)
────────────────────────────────────────────────────  Static binder
(xi : Ai, ai) ↦ static(ai)
```

The implementation applies the same bounded reduction to the substituted result and requires its runtime type to lie in `I`.  `specializedInlineCall?` records the ordered classification.  `specializeInlineValue` substitutes static arguments and retains runtime binders.

Static domains include sorts, recognized proofs, and class evidence.  A function domain is static only for a direct lambda argument.  Resolved evidence is substituted, and `normalizeClassEvidenceExpr` reduces recognized method projections with a fuel bound.  `betaSpecializeExpr` performs a separate bounded normalization, including selected nonlocal transparent applications with a direct lambda argument.  `blocksTransparentSpecialization` protects explicit primitive, recursor, matcher, and monad families from this path.

The first-order signature judgment therefore applies after specialization.  A polymorphic helper may have several accepted concrete inline uses without having a retained polymorphic runtime signature.  A captured runtime value in a substituted callback remains an ordinary local binding.  Captures moved into a synthetic structural helper become explicit first-order parameters.

### Extraction and demand

Define the exact expression judgment by successful evaluation of `extractValueFrom` in [Expression Extraction](../LeanExe/Extract/Core.lean), with its current argument order, context, bindings, and local-index state.  Define the module judgment by successful evaluation of `compileEnvironmentWithEntryMode`.  The full result and first-error behavior belong to these function graphs.  This inclusion of the recognizers makes the boundary precise for the pinned elaborated syntax, including cases the abstract term grammar alone cannot classify.

Internal products, structures, tagged values, and local bindings may contain deferred expressions.  [Demand Analysis](../LeanExe/Extract/Demand.lean) records possible demand, necessary demand, and possible traps.  Its direct-call tests include:

```text
strictCallSafe(f, ā)
  = ∀i. ¬mayTrap(ai) ∨ mustDemand(f,i)

strictCallMaterializationSafe(τ̄, ā)
  = ∀i. wI(τi) = 1 ∨ ¬mayTrap(ai).
```

These equations describe executable analyses, rather than proved semantic facts.  When a path uses a strict call, its recognizer must accept the relevant tests.  Inline extraction can retain lazy bindings.  [Storage Lowering](../LeanExe/Extract/Storage.lean), including `materializeStrictInternalSlotsWithSummaries` and `materializeStrictArrayElementSlotsWithSummaries`, fixes single evaluation and source ordering when values become strict slot sequences.

### Control and recursion coverage

| Family | Required checked shape | Source declarations |
|--------|------------------------|---------------------|
| Boolean, Nat, product, structure, option, exception, and tagged matches | Recognized scrutinee and arms, erased proof binders where supported, and common runtime result shape | `Patterns.boolMatcherArgs?`, `natMatcherArgs?`, `productMatcherArgs?`, `structureMatcherArgs?`, `optionMatcherArgs?`, `exceptMatcherArgs?`, `variantMatcherInfo?` |
| Sparse matches | Supported generated option or nonrecursive variant matcher with recognized fallback arguments | `Patterns.optionMatcherArgs?`, `variantMatcherInfo?` |
| Pure and monadic sequencing | `Id`, `Option`, or concrete `Except ε`, with accepted direct continuations | `Patterns.idBindArgs?`, `supportedMonadType?`, and `Core.extractValueFrom` |
| Collection and range loops | `ForIn.forIn` over `ByteArray`, supported `Array`, or `Std.Legacy.Range`, with a supported accumulator and direct step | `Patterns.forInArgs?`, `forInStepBody?`, `Types.supportedLoopAccumulatorType` |
| While loops | Recognized `Lean.Loop` iterator and `ForInStep` body | `Patterns.isLeanLoopType`, `forInArgs?`, `Core.extractValueFrom` |
| Fuel recursion | First parameter `Nat`, recognized generated predecessor handle, accepted base case and step | `Core.parseNatRecShapeMatcher?`, `parseRecMatcher?`, `extractNatRecFunc` |
| Direct structural recursion | Supported recursive first parameter and recognized `brecOn` constructor arms and below projections | `Core.extractStructuralRecFunc`, `StructuralRec.structuralRecStepMatcher?`, `structuralBelowForFields` |
| Expression-position structural recursion | Supported recursive application, result, post-arguments, and captured first-order values | `StructuralRec.expressionStructuralRecShapeWithLocalTypes?`, `structuralExpressionSyntheticValue?` |
| Closed list-shaped folds | Recognized single-recursive-field step and hidden first-order accumulator | `Core.closedStructuralFoldShape?`, `extractClosedStructuralFoldFunc` |
| Closed structural predicates | Recognized recursive field combined through Boolean conjunction or disjunction, with the matching terminal identity | `StructuralRec.closedStructuralPredicateShape?` |
| Array descent | Recognized `WellFounded.fix` arm using attached array elements and the generated recursive handle | `Core.extractWellFoundedRecFunc`, `Patterns.arrayAttachValue?` |
| Mutual structural recursion | Recognized `WellFounded.Nat.fix` dispatch through nested `PSum`, immediate family-member matching, and accepted descent | `Core.extractWellFoundedNatSumFunc`, `extractWellFoundedNatRecFunc`, `extractWellFoundedNatMemberBranch` |

The names in this table belong to [Pattern Recognition](../LeanExe/Extract/Patterns.lean), [Structural Recursion](../LeanExe/Extract/StructuralRec.lean), and [Expression Extraction](../LeanExe/Extract/Core.lean).  Every row requires successful body extraction and the appropriate position-sensitive types.  Lean's acceptance of a termination argument supplies no missing extractor premise.

## Ownership and IR typing

### Ownership judgment

Ownership is an additional static analysis over checked source and extracted values.  It does not follow from the runtime type `Array τ` or `Rec D τ̄` alone.  Define:

```text
C; B ⊢v release(a) at b : provenance
  iff validateReleaseAt C declaration B args b = ok judgment
      and judgment.provenance = provenance.
```

[Release Checking](../LeanExe/Extract/ReleaseCheck.lean) recognizes direct fresh allocation, fresh helper results, and statically owner-zero arrays.  For a bound variable, `validateReleaseAt` additionally requires no use in the continuation, no recorded escape, and accepted provenance.  `validateModuleReleases` checks the reachable declarations after the first extraction pass has supplied fresh-result summaries.  Explicit release has its required enclosing-let shape in `validateReleaseExpr`.

Automatic releases use separate owner-source, result-root, liveness, and accumulator-replacement analyses in [Value Operations](../LeanExe/Extract/Values.lean).  Thus successful explicit-release validation alone does not establish correctness of every automatic release or every heap alias.

### IR slots

`IR.Ty` records source representation during extraction.  `IR.Expr` and `IR.Stmt` are not indexed by that type.  An IR function stores parameter count, local count, a body, and scalar result expressions.  Every materialized value occupies an ordered sequence of `i64` slots.

A candidate IR well-formedness predicate `SlotWF(M)` can require all local indices to be in range, every direct call to name an existing function, argument and result arities to match, and each fixed-width operation's widths and slot offsets to agree.  A stronger predicate would also relate slots to source values and owner roots.  This document states these as proof obligations.  It does not identify either predicate with an existing checked IR type system.

WebAssembly supplies its own stack-typing judgment after lowering.  It checks operand types and control-flow stack shapes.  An `i64` stack type alone establishes neither a `Bool` invariant, a narrow-integer invariant, nor a valid heap pointer.

## Proof obligations and unresolved boundaries

The following statements describe a possible mechanization.  They are unproved here:

| Statement | Required content |
|-----------|------------------|
| Recognition soundness | A recognized runtime type has the stated representation and preserves the relevant specialized Lean field types. |
| Erasure soundness | Erased fields and arguments cannot affect the represented result of an accepted computation. |
| Specialization preservation | Static substitution and bounded normalization preserve the selected source computation. |
| Extraction typing | Successful extraction produces `SlotWF(M)` and the represented entry signature. |
| Demand soundness | Necessary-demand and possible-trap summaries justify every strict materialization and discarded expression. |
| Ownership soundness | Retains, transfers, releases, and escaped references preserve a stated heap representation invariant. |
| Operational preservation | Represented inputs produce related source and compiled outcomes under explicit numeric, memory, and effect premises. |
| Progress and termination | A represented configuration takes a step, returns, or reaches a specified trap, and terminates only under a stated termination premise. |

The executable recognizers fix acceptance at a revision, so completeness means agreement with that explicit boundary.  Completeness for all Lean terms satisfying a semantic property would be a different claim.

Two current distinctions require care in such proofs.  The bounded `Nat64` interpretation has overflow traps, and `LeanExe.Runtime` intrinsics have generated allocator effects despite zero-valued ordinary Lean definitions.  The [Formal Specification](leanexe-formal-specification.md) records these distinctions, the limited IR evaluator, and source/documentation differences found during this survey.
