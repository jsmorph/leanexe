# Scalar Prime-Factor Artifact

## Summary

This directory preserves the first complete prose-to-Lean-to-WASM-to-proof example produced before `leanexegen` adopted its current array interface and package schema.  The scalar export maps one `UInt64` to the number of prime factors counted with multiplicity, so `60` returns `4`.  Current `leanexegen` programs use `Array UInt64 -> Array UInt64`; the [Demo 1 array benchmark](../../benchmarks/leanexegen/demo1-array/README.md) contains the corresponding modern proof packages and proof-support experiments.

The retained files remain useful as a small readable example of the theorem boundary.  The behavioral proof concerns the Talos module generated for the 1,348-byte WASM artifact, and the final artifact theorem connects that behavior to bytes decoded and validated in Lean.  The source and compiler explain artifact production without becoming premises of that exact-artifact result.

## Program and specification

The [request](request.txt) asks for the number of prime factors with multiplicity.  The [formal specification](spec.lean) defines the result from `Nat.primeFactorsList`, while the [source program](program.lean) implements bounded trial division with explicit fuel.  The source does not import the formal specification.

```lean
def expected (input : UInt64) : UInt64 :=
  UInt64.ofNat (Nat.primeFactorsList input.toNat).length

def compute (input : UInt64) : UInt64 :=
  countPrimeFactorsFuel input.toNat input 2 0
```

The formal artifact property resolves the exported `compute` function and quantifies over every `UInt64` input.  It requires termination with one `i64` result equal to `expected input`.  [Behavioral proof](proof.lean) establishes that proposition over the generated Talos module.

## Artifact and proof support

The retained [WASM module](program.wasm) is the exact executable described by the [WAT rendering](program.wat).  The proof develops a trial-division invariant, a decreasing measure, and the number-theoretic connection between the final counter and the formal result.  Its final artifact theorem applies the same specification to the validated Talos translation of the embedded binary.

Two diffs record the first ProofKit experiments.  [ProofKit refactoring](proof-kit.diff) replaces mechanical entry and one-call wrapper setup with shared control-flow tactics, while [controlled reproof](controlled-reproof.diff) also applies the block-loop entry tactic.  These tactics contain no prime-factor definitions or generated program constants; the [modern Demo 1 benchmark](../../benchmarks/leanexegen/demo1-array/README.md) records later fixed-artifact measurements and compiler-annotation work.

## Execution

The retained artifact can run directly through the pinned Wasmtime installation.  Its public interface is scalar because it predates the current `leanexegen` array ABI.  The command returns `4` for the four factors `2`, `2`, `3`, and `5`.

```sh
build/tools/wasmtime/current/wasmtime run \
  --invoke compute \
  demos/demo-1/program.wasm \
  60
```

The original from-scratch process streams remain available as evidence.  [Standard output](stdout.txt) and [standard error](stderr.txt) record the baseline generation, while [ProofKit standard output](stdout-with-proof-kit.txt) and [ProofKit standard error](stderr-with-proof-kit.txt) record the first live shared-tactic run.  Their old absolute workspace paths are observations from those runs rather than current command examples.

## Retained files

| File | Contents |
|------|----------|
| [Generation request](request.txt) | Original scalar prime-factor request. |
| [Formal specification](spec.lean) | Mathematical result and Talos artifact property. |
| [Lean program](program.lean) | Bounded trial-division implementation compiled by LeanExe. |
| [WASM module](program.wasm) | Exact executable artifact. |
| [WAT rendering](program.wat) | Textual representation used for the original Talos model. |
| [Behavioral proof](proof.lean) | Trial-division invariant and artifact behavior theorem. |
| [ProofKit refactoring](proof-kit.diff) | Checked replacement of entry and wrapper boilerplate. |
| [Controlled reproof](controlled-reproof.diff) | Checked use of the additional loop-entry tactic. |
| [Baseline standard output](stdout.txt) | Original generation stages and sample execution. |
| [Baseline standard error](stderr.txt) | Original warnings and runtime notices. |
| [ProofKit standard output](stdout-with-proof-kit.txt) | Live ProofKit generation and verification stream. |
| [ProofKit standard error](stderr-with-proof-kit.txt) | Warnings and runtime notices from that run. |
