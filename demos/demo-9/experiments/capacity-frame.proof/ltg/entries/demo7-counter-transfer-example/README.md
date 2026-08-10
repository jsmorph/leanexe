# Demo 7 counter-transfer composition

This example composes three checked boundaries.  A semantic recognizer proves that the scalar callee returns its input while preserving the store, the singleton-wrapper theorem consumes that summary, and residual normalization closes the generated expected-result equations.  The resulting 67-line proof contains no artifact-local loop invariant or transition witnesses.

The first version still started Codex, whose only work was running Lean and returning the unchanged starter.  Direct acceptance now runs the full artifact check once and publishes the starter when every byte, declaration, and axiom check succeeds.  Three measured runs reduced median Stage 5 time from 204.537 seconds to 125.103 seconds.

The task catalog excludes this entry from a measured proof of the same artifact digest.  The counter theorem and wrapper theorem remain independently available through their canonical entries.  A related artifact may consult this organization, but its own generated summary and exact region equalities must pass Lean.
