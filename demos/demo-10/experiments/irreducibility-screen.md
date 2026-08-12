# Local-irreducibility screen

This screen kept Demo 10's primary proof and exact artifact unchanged.  The first variant added `attribute [local irreducible] LeanExeGen.GeneratedRa8e90ffc5781d113.func0Def` after the namespace and imports.  The standard runner rejected the `Behavior` target at the first length-dispatch tactic after 4.3 seconds of target work and 6.836 seconds of wall time.

```text
LeanExeGen/GeneratedRa8e90ffc5781d113/Behavior.lean:68:2:
'change' tactic failed

pattern:
  wp ?module
    (Project.ProofKit.FixedArrayLengthDispatch.leProgram 7 8
      ?validBranch ?invalidBranch ++ ?rest)
    ?Q ?store ?frame ?env

target:
  wp module func0Def.body ?publicPost initial
    (func0Def.toLocals
      (List.take func0Def.numParams [Wasm.Value.i64 inputPtr]).reverse)
    env
```

The second variant changed the attribute target from `func0Def` to `func0`.  It failed at the same source location after 5.2 seconds of target work and 7.804 seconds of wall time.  The narrower attribute permits the function-record projections to reduce, but the dispatch tactic still cannot compare the irreducible program name with `FixedArrayLengthDispatch.leProgram`.

```text
tools/leanrun --timeout 15m lake \
  -d ./tmp/demo10-irreducible-workspace --no-ansi build \
  LeanExeGen.GeneratedRa8e90ffc5781d113.ArtifactResult
```

Both variants produced direct source diagnostics and therefore were not rerun unchanged.  Neither variant reached a branch theorem, and neither changed the formal specification, compiler output, annotation package, proof body, or artifact digest.  The result rejects a standalone irreducibility attribute and motivates a checked entry/dispatch package whose accessor theorems expose the named branch programs without unfolding `func0`.
