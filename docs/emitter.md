# Emitter Restructuring

This document specifies the next planned compiler task: split the WASM emitter so the compiler produces the Talos module representation directly, and remove `wasm-tools` and the WAT parser from the semantic path between the compiler and the proofs.  The task stands on its own and is also phase 0.5 of the [compiler verification plan](../proofs/talos/compiler-verification.md).  It begins after the proof-infrastructure overhaul and the aggregate and execution gates close.

## Problem

The semantic path today has two unverified translations in it.  The compiler emits a binary `ByteArray` through `LeanExe.Wasm.Binary.encode`, which fuses code generation and byte serialization in about 3,650 lines.  `wasm-tools print`, an external Rust binary pinned at 1.251.0, renders the bytes as WAT text.  Talos parses that text into the Lean `Wasm.Module` value that every artifact theorem is about.  Wasmtime, meanwhile, executes the bytes.

The theorems therefore attach to the output of a translation chain that nothing verifies.  A mis-rendered instruction in `wasm-tools` or a mis-read one in the WAT parser would make the proved model diverge silently from the executed binary, and only the differential execution suite could catch it.  Both tools sit in the trusted base of every artifact theorem.

## Design

Split `encode` into two functions with an explicit intermediate value:

```
emit      : IR.Module → Wasm.Module
serialize : Wasm.Module → ByteArray
encode    := serialize ∘ emit
```

`Wasm.Module` is the Talos model type, an ordinary Lean type in the interpreter package.  The code-generation half of the current `encode` becomes `emit`; the byte-writing half becomes `serialize`.

Three consequences follow.  The generated `Project/<Case>/Program.lean` model becomes a value computed inside Lean from `emit`, so `wasm-tools` and the WAT parser drop out of the proof-generation loop.  The external round trip becomes a checked equality instead of a trust: at artifact-generation time the tool asserts `decode (print (serialize m)) = m`, where modules are literal data with decidable equality, so the serializer, `wasm-tools`, and the Talos parser cross-validate on every regeneration and a regression in any of the three fails the gate.  The residual semantic trust shrinks to one question — whether `serialize` writes bytes that mean what the model says — checked by that round trip against two independent implementations and by differential execution.

## Value

The task shrinks the trusted base of every existing artifact theorem, removes one pinned external tool from the proof path, removes a subprocess from regeneration, and installs a permanent three-way cross-check.  It also prepares the compiler verification work: a back-end theorem must be stated over `emit`, and this split creates that function.

## Validation Plan

The refactor must not change behavior.  Validation follows the pattern the two-tool workflow migration used:

1. Byte-identical `encode` output for all twenty registered cases against the pre-refactor compiler.
2. The full differential execution suite under its outer resource scope.
3. The new round-trip gate on all twenty cases: `decode (print (serialize (emit m))) = emit m`.
4. The aggregate proof gate, which must be unaffected because the generated models are unchanged.

The model-generation switch in `tools/talos-artifact.js` — writing `Program.lean` from `emit` instead of from the Talos WAT decode — lands as a separate increment after the equality gate has held across all cases, so any divergence is observed before the proof path depends on the new source.

## Risks and Preconditions

The main risk is behavioral change while splitting the fused encoder; the byte-identical requirement contains it.  The one precondition to confirm early is that the Talos module type represents everything the emitter produces; the evidence is that Talos already decodes all twenty generated modules, and any gap would surface in the first round-trip check.  `wasm-tools` remains in the repository for the cross-check gate and for human-readable WAT; its removal from the semantic path does not remove it from the toolchain.

Rough effort is weeks.  The work is compiler-side Lean with Node tool changes, ordinary test gates, and no new dependencies.
