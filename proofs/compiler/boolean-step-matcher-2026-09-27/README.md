# Generated Boolean step matches

Candidate `416b8ec868fabd56d02b334c32cbbbe11f780bd7` compiles ordinary matches over ForInStep Bool results,
including nested matches, helper scopes, captured values and standard Id results.
Recognition checks the actual declaration type, body, safety, totality and universe
parameters. A canonical dispatcher with an ordinary name is accepted too.

The independent environment/source relation records checked declaration expansion
and expression congruence before scalar evaluation. Normalization is proved sound
and complete for its source grammar. The public theorem covers decoding, validation,
export lookup and terminating source-equal execution of the emitted WASM.

- All 29 compiler axiom audits pass; the native forwarding identity has no axioms.
- Native Lean/V8 agree on 1,221 inputs across 61 declarations, including 38 ranges.
- All 52 prior modules retain identical bytes.
- New tests pass 312 native/IR comparisons and 20 invalid-input checks.
- Recognition accepts four generated references and one named dispatcher, rejecting six unsupported declarations.
- Prior tests pass 32,688 comparisons and 18,816 invalid-input checks.
- Four fixed production probes now compile; the native corpus contains 1,632 declarations.

[verification.json](verification.json) records commands and source/module hashes.
The [journal](journal.md) includes failed attempts and their corrections.
Full-dialect compiler correctness remains unfinished.
