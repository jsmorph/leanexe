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

2026-09-23: Completed product-pattern and Unit elimination, including expression
typing, captured frames, environment extension, canonical forms, and all existing
safety proofs. Profile admission checks every nested binding and every function
parameter. Its safety results use ordinary configuration typing; they do not
claim that syntactic relevance survives runtime reduction. Added explicit check
characterizations and a program lookup theorem. No all-path usage, linearity,
ownership, termination, or compiler correspondence claim is made.

Added 41 semantic examples covering product binding order, nested lexical shifts,
Unit elimination, ignored lets/fields/payloads/parameters, nested projection
rejection, duplicated uses, and syntactic use in an unselected branch. They also
separate admission from typing and exhibit malformed eliminations as stuck.
Together with the existing 26 examples, all 67 passed.

The first expanded gate caught Quot.sound in profile helper proofs, while core
and profile safety results still depended only on propext. The agent traced this
to standard library helper proofs, including Bool.or_eq_true_iff, and replaced
them with direct equations and membership induction. Parameter checking now uses
equivalent Nat recursion with its universal-index characterization proved
directly. No statement or axiom allowlist was weakened. The final full gate
passed: six build jobs, both example files with warnings as errors, and 20
transitive theorem audits, each reporting only propext.

2026-09-23: Specified the next persistent-array increment before completing its
implementation. The six forms are explicitly typed empty construction, size,
checked get, checked set, checked push, and checked append. Checked operations
return sum Unit payload, with inl Unit for failure and inr for success. Every
operand evaluates left to right, even when an earlier operand determines that
the index will be invalid. Value typing requires homogeneous elements and length
strictly below 2^64; growth either preserves that invariant or returns failure.
The agent owns pure operation laws and machine/proof integration. Parent-owned
examples exercise behavior independently. At this specification checkpoint those
array examples and proofs have not yet been checked.

2026-09-23: Completed the six-form persistent-array increment. Array values have
an extrinsic homogeneous-list judgment and a length bound. ArrayValues defines
total raw operations without typing premises, then proves their exact failure
conditions, checked success and length characterizations, read-after-write,
unchanged other reads, and append/push ordering laws. The machine evaluates all
operands strictly and carries element, length, index, and captured-environment
invariants in its frames. Existing progress, preservation, reachable-state,
result-type, overflow, and profile theorems now include these forms.

The first focused operation proofs needed explicit Nat normalization and a
recursive index argument. Lean's direct induction tactic did not support the
mutual value/list-typing judgment in the attempted form; induction on the raw
list followed by typing inversion gave the required proofs. A reserved pattern
identifier in the machine was renamed. No theorem statement was weakened.
The parent reviewed the raw operations, exact failure/result laws, runtime
transitions, and typing invariants independently of the agent's implementation.

All 46 new array examples passed on their first gate run. They cover endpoint
and large invalid indices, unchanged original arrays after set, nested arrays,
failure order including invalid-set replacement evaluation, restored lexical
environments, direct array calls, rejected heterogeneous values and wrong index
types, and malformed array frames. The full gate passed all seven build jobs,
113 examples with warnings as errors, and 52 transitive theorem audits. Four
audited array/list lemmas use no axioms; the other 48 results use only propext.
Node syntax, whitespace, and the source scan for proof holes and unsafe shortcuts
also passed. These are abstract array results; no storage or compiler theorem
was added.

Updated the older compiler-dialect overview to remove an unconditional claim
that source evaluation order is preserved for every accepted expression. The
replacement distinguishes implemented demand behavior and example coverage from
the absent general preservation theorem. The older type-theory and compilation
specifications now link the strict normative contract and identify the compiler
compatibility boundary explicitly.

2026-09-23: The parent stopped after publishing the array milestone even though
the user had authorized continued Track 1 work. The user challenged that stop.
There was no technical blocker requiring it. Resumed the next declaration and
recursive-data increment with the existing dedicated agent; publishing future
milestones is a checkpoint within the continuing task.

Workspace maintenance had removed the local checkout and toolchain since the
last run. Re-cloned the published typesafety branch at ed83fce and restored the
exact official Lean archive, again matching SHA-256
3d011041203acacf300d343a39673f7d233743397993797c941346ae9e5df1a8.
The container cannot restore archive owner IDs, so extraction was repeated with
--no-same-owner. The restored baseline passed the full gate: seven build jobs,
113 examples, and 52 theorem audits. No source or proof changed during recovery.

2026-09-23: Agreed the nominal-data design after a read-only review. Declarations
are finite tables of constructor field lists; references are bounded nominal
indices, so formation terminates without unfolding recursive definitions. Empty
types, empty constructors, and arbitrary mutual recursion are permitted. There
are no negative field occurrences in the first-order type grammar. Runtime
values remain finite trees. Case expressions carry explicit result types and
branch arities; typing enforces exact branch coverage and declared field counts,
and execution checks nominal identity and selected arity before binding fields.

The review rejected checking only a term's outer type: an invalid empty-array
annotation can disappear under size, and an invalid absent sum summand can
disappear under case. Sum introduction and empty arrays therefore receive
formation premises in expression and value typing. An empty nominal match also
requires its explicit result type to be well formed. Program typing now needs
declaration and signature formation as well as body typing; no safe-execution
premise is introduced.

The agent's focused Formation target passed, including exact Boolean-checker
characterizations. Its focused Core target then passed with nominal syntax,
canonical forms, exhaustive branch typing, and expression/argument/value/
environment formation theorems. Machine, array, and profile integration and the
expanded gate are still in progress at this contract checkpoint. The parent has
migrated existing examples and is adding independent nominal boundary examples.

2026-09-23: Completed nominal-data integration through the operational semantics,
array typing lemmas, source relevance, and all safety proofs. During review the
agent identified that introducing nominal references also requires formation in
the raw runtime result type: an inherited polymorphic overflow rule would permit
an undeclared result label. Strengthened empty-continuation and overflow typing
with explicit formation evidence and proved formation transfer through frames,
continuations, and states. Execution is unchanged by that strengthening.

The agent's focused builds and all-module audit passed. The parent reviewed the
actual declaration/type rules, constructor accumulation, nominal and arity guards,
branch coverage/lookup, and formation premises, then ran the maintained gate.
All 113 existing examples passed after explicit declaration/formation migration;
all 57 new examples passed on their first gate run. They include rejection of
invalid hidden types and malformed whole-program tables, valid empty elimination
and empty arrays of an empty type, exact constructor/branch arity and coverage,
an empty-type no-value result, runtime formation rejection, strict field order,
captured environments, nominal mismatch stuckness, and a typed recursive list sum.

The gate now audits every one of the 103 declared theorems in the six development
modules, including helpers. All passed with no axioms beyond propext. Eight build
jobs and 170 examples passed with the pinned Lean version. The source scan,
whitespace check, and Node syntax check passed. Declaration-checker soundness and
completeness are proved; a general expression/program type checker remains next.

2026-09-23: Continued immediately after publishing the nominal milestone. Sum
introductions now carry the other summand type before the payload. This is an
explicit source-syntax choice for machine-written programs; runtime sum values
and evaluation behavior are unchanged. The parent migrated the affected source
examples while the agent migrated the calculus and proofs. The maintained gate
passed eight build jobs, all 170 examples, and all 103 audits. Typing.lean is being
developed separately and is not yet imported by the umbrella or included in this
annotation checkpoint. Its intended public boundary includes full ambient
formation; raw structural inference alone will not be called source admission.


2026-09-23: Completed the algorithmic typing increment. Raw inference and
argument/branch checkers are proved sound and complete against the raw judgments.
Explicit sum annotations give expression type uniqueness. Public expression,
program, and profile checks have exact characterizations including all ambient
formation obligations. Checker-accepted closed entries inherit arbitrary-finite-
execution safety under checker-accepted programs; no termination premise is added.

The focused audit initially found an unnecessary Quot.sound dependency from
simplifying monadic bind continuations. Replacing those continuations with direct
structural option matches removed that dependency without changing the accepted
terms or weakening any statement. The allowlist remains unchanged.

The parent reviewed the definitions and theorem boundaries, added 65 independent
checker/admission examples, and ran the full maintained gate. Nine build jobs,
235 examples with warnings as errors, and all 120 theorem audits passed. Each
new theorem uses only propext. The next coverage increment concerns the remaining
bounded-natural operations; fixed-width words, bytes, additional collection forms,
and effects remain explicit unfinished language obligations.


2026-09-23: Selected the next numeric boundary from the documented primitive
inventory and reviewed recognition/lowering code only as coverage evidence.
It supplies no language-to-compiler correspondence theorem. The bounded-natural
increment uses explicit binary-operation and comparison tags, with a separate
addition/multiplication overflow tag. This avoids treating multiplication failure
as an addition error or giving total operations spurious permitted failures.
The implementation and its proof extensions are now in progress; the new numeric
contract is explicitly marked unproved at this checkpoint. Word operations,
natural pattern matching, bytes, collection forms, and effects remain tracked.
