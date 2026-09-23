# Type-safety development journal

2026-09-23: Created the `typesafety` branch at
`a4655383ee80d3d80830b6bddfb6248a9d5c2b4b` after the user selected Track 1.
The parent agent owns integration, review, verification setup, and publication;
the dedicated type-safety agent owns the independent Lean modules. The first
milestone separates untyped syntax from typing and states a bounded-natural
invariant. An environment-and-continuation machine was selected to make lexical
binding and evaluation order explicit; its environment lemmas replace syntactic
substitution in the safety argument.

The initial container has no Lean installation or systemd user scope. The user
explicitly authorized direct Lean execution during this session. We will retain
the repository runner's lock and timeout through its local mode while preparing
the exact `4.34.0-rc2` toolchain. The initial Core module is a source checkpoint,
not yet kernel-checked. No Lean process has run at this checkpoint.

2026-09-23: Downloaded the exact official Linux Lean release and matched its
SHA-256 against the release metadata:
`3d011041203acacf300d343a39673f7d233743397993797c941346ae9e5df1a8`.
The runner reported Lean `4.34.0-rc2`, commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`. Both the focused Core target and the
complete `LeanExe.TypeSafety` target passed in authorized local mode. The initial
diagnostics exposed a namespace-shadowed lookup reference and a reserved local
identifier; qualifying/renaming them sufficed. The proof statements were not
weakened. The completed machine proves progress, preservation, safety of all
finite reachable states, final-value typing, and arithmetic justification of
the sole overflow failure. No source-to-core or compiler theorem is claimed.
The first full build completed all five jobs; the safety proof job took 892 ms.
Direct-call extension, focused examples, and public-theorem axiom audits follow.

2026-09-23: Extended the core and all safety theorems to direct first-order calls
with arbitrary finite arity, including self-recursion and mutual recursion.
The program premise checks each body under its declared parameter context and
the same global signature table. It does not assert safe execution or
termination. The call-frame invariant relates accumulated values and remaining
arguments to the exact parameter list. Calls enter fresh environments; captured
continuations restore caller bindings. The dedicated agent completed the proof
extension and returned the Lean execution slot to the parent for verification.

The parent reviewed the runtime/typing separation, every transition and frame
invariant, program/signature alignment, recursive-call reasoning, and the final
theorem statements. The review found no circular safety premise. It also
confirmed that malformed eliminations and missing bindings remain observably
stuck, while overflow requires actual bounded operands and the overflow
inequality. The agent identified a scope nuance: unannotated sums intentionally
have multiple typings, so type uniqueness is not a consequence of this result.
This limitation is now documented.

Added 26 kernel-checked semantic examples. They cover lexical binding, selected
branches, strict pairs, checked arithmetic boundaries, malformed states, argument
order and arity, fresh call environments, continuation restoration, and safe
recursive looping. Initial example diagnostics required unfolding Terminal
before deciding the arithmetic proposition and exposing the empty argument
constructor before simplifying the arity contradiction. Those repairs changed
proof presentation, not the expected behavior or theorem statements.

Added the repeatable tools/type-safety.js gate. It verifies the pinned version,
builds the independent core, checks semantic examples, and prints transitive
axiom dependencies of seven public theorems. The first full gate passed: every
audited theorem uses only propext. The allowlist was tightened to that observed
set; missing audit output and every additional axiom fail the gate. Examples
and audit compilation treat warnings as errors. The source and docs now state
both the checked result and the remaining source/extraction/heap/compiler gaps.

The final gate also passed after the dependency allowlist was tightened, warning
failures enabled, and theorem signatures wrapped for review. All five build jobs
completed, all 26 examples checked, and all seven dependency audits reported
only propext. Node syntax, whitespace, changed documentation links, and the core
source scan passed. This completes the checked first-order core milestone;
abstract arrays and the extraction correspondence are explicitly future work.

2026-09-23: The user challenged the parent's repeated conflation of language
soundness with compiler correctness. A fresh review of the source judgments,
runtime typing rules, operational specification, and checked theorem statements,
with a separate read-only critique from the type-safety agent, confirmed the
error. A compiler bridge is not required for language type soundness. The current
calculus already has that theorem; the full runtime language still lacks complete
independent syntax, typing, dynamics, and the corresponding metatheory.

The review identified a concrete model-adequacy issue: strict pairs in the core
evaluate an unused overflowing component during projection, while the dialect
documentation describes lazy projection and deferred fields. The core is a
proved related calculus, not an established semantics-preserving fragment of
that documented language. Its proof remains valid for its stated semantics.
The next language task is to resolve and document the intended semantics before
expanding coverage. Prior chat advice making an extractor bridge the next
prerequisite for Track 1 is withdrawn.

Updated the reference and plan to keep Lean logical consistency, runtime-language
type safety, model adequacy, and compiler correctness distinct. Split language
preservation, progress, compiler refinement, and termination in the original
type-theory document. The review also separates a declarative ownership/effect
discipline for explicit runtime operations from correctness of its compiler
implementation. Only documentation and the plan changed; no theorem statement,
proof, semantics, or verification gate was modified.

2026-09-23: Reviewed maintained lazy-let, ignored-argument, product projection,
and constructor-tag fixtures, plus thunk capture, inline-call selection, and
materialization definitions. Initially drafted a pure deferred/strict calculus
contract. Before implementation, the user explicitly suggested prohibiting
unused lets and fields, asked for first-principles design, and stated that source
will be machine-written. The deferred proposal was withdrawn. The agent confirmed
that it had created no Demand files, edited no Lean source, and started no Lean
process. The unpublished contract checkpoint was revised to record this choice.

The selected design retains strict evaluation and adds a separate decidable
syntactic relevance profile. Every let, parameter, product-pattern field, and
sum-pattern payload binding must occur in its scope. Product elimination uses
both field bindings, and the profile rejects unrestricted fst/snd. A Unit
eliminator handles its zero-field constructor without a fabricated binding.
Repeated uses are permitted; this is not a linearity or ownership rule.
Syntactic occurrence is not all-path use or semantic necessity. Current compiler
compatibility is not asserted or needed for the language soundness theorem.

Assigned the agent the split/Unit elimination semantics, extensions of the
existing safety proofs, and a Profile module combining ordinary typing with
admission checks. The parent owns the contract, gate, tests, and publication.
At this specification checkpoint those new cases have not yet been checked;
the previously published strict-calculus theorem remains the checked baseline.
