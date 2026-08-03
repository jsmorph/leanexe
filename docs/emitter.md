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

## Implementation Survey

Reading `LeanExe.Wasm` changes the effort picture: the split is half done.  The compiler already lowers every function body through a structured instruction type, `LeanExe.Wasm.Instr`, whose doc comment states the design intent — one lowering target that the binary encoder and the text printer both serialize, so the two cannot diverge in content.  `Binary.lean` divides into three layers: about 30 byte-level primitives (`u32leb`, `vec`, section framing), about 120 code-generation functions producing `List Instr` (the `emit*` family, the refcount-header helpers, the address calculators), and about 20 module-assembly functions that still build section bytes directly.  A per-instruction serializer, `encodeInstr : Instr → List UInt8`, already exists.

What is missing: a structured module value (sections as data rather than bytes), the serializer factored over it, and the bridge to the Talos model type.  The bridge is a small total translation, because the two instruction types differ only in presentation: the Talos `Instruction` carries numeric block arities where `Instr.iff` carries a result flag and an optional else, `UInt64` constants where `Instr` carries `Nat`, and explicit load and store offsets where `Instr` bakes the offset into the constructor.  Roughly fifty structural cases.

One correction to the problem statement: the WAT-to-`Program.lean` generation is performed by the external Talos binary, so the current semantic path trusts two external tools — `wasm-tools print` and the Talos generator — and the equality gate cross-checks both at once.

## Increments

| Step | Work | Check |
|------|------|-------|
| 1 | Define the structured module value: functions with types, locals, and `List Instr` bodies, plus globals, memory, and exports as data.  Rebuild module assembly as `assemble : IR.Module → StructModule`. | Compiler builds; no output change yet. |
| 2 | Factor `serialize : StructModule → ByteArray` over the existing byte primitives and `encodeInstr`; redefine `encode := serialize ∘ assemble`. | Byte-identical `encode` output for all twenty cases against the pre-refactor compiler, plus the differential suite. |
| 3 | Define `toTalos : StructModule → Wasm.Module` (the interpreter package's type) as the structural translation. | Requires the dependency decision below; compiles. |
| 4 | Add the equality gate to `tools/talos-artifact.js`: after generating `Program.lean` through the external tools as today, check the decoded module equals `toTalos (assemble m)` by decidable equality. | Gate holds for all twenty cases; a mismatch in the serializer, `wasm-tools`, or the Talos generator now fails regeneration. |
| 5 | Optional, later: generate `Program.lean` by pretty-printing `toTalos`'s output and demote the external tools to the cross-check role. | Generated models byte-identical to the current ones. |

Step 4 delivers the trust reduction; step 5 removes the external tools from the generation loop but changes generated-file provenance and can wait.

## Dependency Decision

`toTalos` targets the interpreter package's `Wasm` types, which today only the proof workspace depends on.  Three options: the compiler workspace adds the interpreter package as a dependency; the model types move to a small shared package; or the compiler defines a clone type and the gate compares through the clone.  The first is simplest and the dependency is internal, but it couples compiler builds to the interpreter package.  This decision belongs to the project owner before step 3.

## Validation Plan

The refactor must not change behavior.  Validation follows the pattern the two-tool workflow migration used:

1. Byte-identical `encode` output for all twenty registered cases against the pre-refactor compiler.
2. The full differential execution suite, whose Lean children use the machine-serialized runner.
3. The new round-trip gate on all twenty cases: `decode (print (serialize (emit m))) = emit m`.
4. The aggregate proof gate, which must be unaffected because the generated models are unchanged.

The model-generation switch in `tools/talos-artifact.js` — writing `Program.lean` from `emit` instead of from the Talos WAT decode — lands as a separate increment after the equality gate has held across all cases, so any divergence is observed before the proof path depends on the new source.

## Risks and Preconditions

The main risk is behavioral change while splitting the fused encoder; the byte-identical requirement after step 2 contains it, and the instruction layer's existing structure keeps the refactor mostly mechanical.  The precondition that the Talos module type represents everything the emitter produces is supported by the existing `Instr` type's coverage and by Talos decoding all twenty modules today; any residual gap surfaces in the step 4 equality check.  `wasm-tools` remains in the repository for the cross-check gate and for human-readable WAT; its removal from the semantic path does not remove it from the toolchain.

Rough effort is weeks.  The work is compiler-side Lean with Node tool changes, ordinary test gates, and no new dependencies.
