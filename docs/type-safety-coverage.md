# Language coverage ledger

This ledger compares the independent language development with the operation
families inventoried in the [type-theory reference](leanexe-type-theory.md#primitive-signatures-and-code-binders)
and [implementation specification](leanexe-formal-specification.md). Those files
identify coverage obligations; they are not premises of the language proof.

“Checked” means the independently specified forms are included in the maintained
language gate. It does not mean that existing Lean source, an extractor output,
or a WebAssembly artifact has been proved to implement them. Strict evaluation
and relevance are normative choices recorded in [the language contract](runtime-language.md).

| Family | Checked independent language | Remaining obligation |
|--------|------------------------------|----------------------|
| Scalars and ordinary binding | Unit, Bool, bounded naturals, explicit 8/32/64-bit words, variables, strict lets, conditionals, complete product patterns, Unit elimination. | Any frontend syntax translation remains separate. The profile rejects projections and unused binders. |
| Binding transport | Capture-avoiding renaming and algebra; raw/profile typing transport and weakening; exact occurrence images and internal relevance invariance; exact environment and branch lookup support; raw step correspondence and both finite-execution directions; exact return/overflow/stuck-reachability equivalences. | These same-program laws do not establish frontend translation, signature changes, or usage of newly inserted parameters. |
| Sequencing | Continuation extension for successful steps/traces; exact finite decomposition at the empty-return boundary; first-step inversion at no-successor endpoints; return/overflow/stuck sequencing equivalences. | Individual derived-form expansions and their exact behavior still need proofs. No termination claim. |
| Sums and nominal data | Annotated sums; monomorphic nominal tables; formation, strict construction, exhaustive matching, finite recursive values. | Account for specialization and any intended type-level generalizations. Empty nominal types are permitted; formation does not prove inhabitance. |
| Calls and recursion | Fixed global signatures, exact arguments, fresh callee environments, recursive and mutually recursive calls. | General call safety does not prove closure conversion, recognizer coverage, or termination. |
| Bounded naturals | Add/sub/mul/div/mod/min/max, comparisons, successor/predecessor, Bool-to-Nat, tagged overflow, zero/successor case analysis. | Other unbounded-Lean-Nat operations are not implicitly included. |
| Fixed-width words | Modular arithmetic, unsigned comparisons, conversions, AND/OR/XOR, complement, masked logical shifts. | No raw-binary64 semantics or compiler correspondence follows from the word theorem. |
| Boolean operations | Bool literals and elimination; proved NOT and strict AND/OR/XOR/equality expansions, typing, inference, relevance, staging, and supplied-value truth tables. | Compiler recognition/correspondence remains separate. Short-circuit evaluation uses `ifE`. |
| Structural equality | Strict homogeneous source equality, exact raw comparison, independent EqTy domain/checker, full metatheory and final-step result laws. | Bytes remain absent. Recursive source types are excluded from EqTy; comparing finite recursive raw values does not expand that domain. Arbitrary selected BEq functions and frontend correspondence remain separate. |
| Persistent arrays | Empty, size, checked get/set/push/append; homogeneous elements, bounded lengths, exact failure/read/update laws. | Literals/replicate, emptiness, defaults/back/pop, slicing, insert/erase/swap/reverse, and other wrappers need complete rules or proved expansions. Existing trapping and conditional wrappers are not silently covered by the checked forms. |
| Array callbacks | No dedicated callback form. | Map/filter/modify/find/find-index/any/all and their bounds/early exits need binding and execution rules or proved expansions. |
| Folds and loops | Ordinary recursion supplies an implementation ingredient. | Specify accumulator/element/index binders, captured environments, traversal order, bounds, done/yield/failure behavior, and range-step arithmetic; prove each primitive or expansion. |
| Option/Except APIs | Sums and nominal patterns supply representation and elimination ingredients. | The [derived-sum plan](../plans/type-safety-derived-sums.md) specifies a first constructors/map/bind/map-error increment; its definitions and proofs remain pending. Filters/defaults/tests/fallback/conversion APIs still need contracts and proofs. Payload-discarding observers need an explicit policy consistent with relevance; dummy uses are not a solution. Hygienic renaming and general sequencing are proved; each callback expansion still needs its own execution laws. |
| Bytes | Words and arrays supply possible representation ingredients. | State the byte representation, operation signatures, copy/slice semantics, length bounds, and endian conversion failures; prove primitive or derived behavior. |
| Binary64 | Raw 64-bit words are available. | Define permitted floating results, including NaNs and exceptional values, before proving primitive safety. A word-valued signature alone is insufficient. |
| Generic traps and trapping wrappers | Only justified addition/multiplication overflow is a machine failure terminal. Checked array failures are ordinary sum data. | Generic typed traps and bang wrappers are absent. If included, give them explicit rules; do not reclassify arbitrary malformed states as permitted failures. |
| Counter reads and release | No abstract effects, heap, or ownership permissions. | Either exclude these explicitly from the target language or define their state and permission discipline and prove its soundness. Relevance is insufficient. |
| Static strings and source libraries | No static string evaluator or library translation theorem in this development. | Separate compile-time admission/desugaring from runtime safety. ASCII/JSON library correctness is an additional property of admitted implementations. |

For every added primitive, the required work is its actual mathematical behavior,
binding and failure rules, extrinsic typing, and extensions of formation,
canonical forms, progress, preservation, reachable-state safety, exact executable
admission, and type uniqueness. Operation laws and semantic examples check that
the chosen rules express the intended behavior.

A derived form needs an explicit hygienic expansion and proofs of its typing,
admission, and evaluation behavior. General expressibility in the core is not a
substitute for those results. Termination, failure-freedom, model adequacy, and
compiler refinement remain distinct from operational type safety.
