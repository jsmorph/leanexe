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
