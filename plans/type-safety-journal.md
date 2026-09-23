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
