# Self-Hosted WebAssembly Emitter

LeanExe has an experimental self-hosted binary-emitter boundary for ordinary library modules.  The native compiler remains the production path: it loads and checks Lean modules, extracts the accepted subset, performs ownership analysis, lowers to structured WebAssembly instructions, selects the runtime, and resolves indices.  It can then freeze that result as a canonical byte image.  `emitImage`, compiled by LeanExe itself, validates the image and emits the complete WebAssembly binary.

This supports the specific claim that LeanExe has a self-hosted WebAssembly binary emitter.  It does not make LeanExe a source-self-hosted or IR-self-hosted compiler, remove Lean or native Stage 0 from the trust boundary, or prove compiler correctness.

## Image schema

Schema version 2, library profile 1, has the following ordered wire fields.  All integers, counts, byte lengths, tags, and indices use canonical unsigned LEB128.  Alternate encodings, unknown versions or profiles, trailing bytes, and invalid semantic references reject.

| Field | Encoding |
|-------|----------|
| Magic | Six literal ASCII bytes `LXEIMG`. |
| Schema and profile | Version `2`, then library profile `1`. |
| Memory | Minimum page count. |
| Globals | Count, then mutable flag and initial `i64` bit pattern for each global. |
| Functions | Count, then parameter count, result count, additional-local count, and a length-delimited instruction stream for each function. |
| Exports | Count, then an ASCII name byte string, kind tag, and resolved index for each export. |

Function bodies are linear instruction records rather than Lean runtime objects.  Tags 0 through 40 encode scalar, indexed, memory, return, and drop instructions.  Tags 41 through 44 open block, loop, `i64`-result `if`, and `i32`-result `if` records.  Tags 45 and 46 encode `br` and `br_if`; tag 47 is `else`; and tag 48 closes structured control.  The validator checks local, global, function, branch, export, and mutable-global references before emission.

The library profile limits inputs to 64 MiB, one function body to 32 MiB, output to 128 MiB, functions and exports to 65,536 each, globals to 256, locals to 1,048,576, instructions per body to 1,048,576, nesting depth to 256, and export names to 4,096 bytes.  An incompatible wire change requires a new schema version.  A compatible new module family requires a distinct profile when its assumptions differ from library profile 1.

## Native and host boundaries

`LeanExe.Wasm.Binary.CoreWasm.moduleBytes` uses the direct native serializer.
`moduleBytesFromImage` constructs a final module image and invokes the pure emitter
used by the self-hosted entry, providing an independently callable differential
oracle.  WASI command adapters retain their dedicated native assembly paths and
are not part of this self-hosted profile.

The diagnostic command writes an image without exposing Lean runtime representation:

```sh
tools/leanrun .lake/build/bin/lean-wasm compile-image \
  --module LeanExe.Wasm.Image.Emit \
  --entry LeanExe.Wasm.Image.emitImage \
  --out build/emitter.image
```

The exported entry has source type `ByteArray -> Except ByteArray ByteArray`.  Its library ABI takes the input pointer and length in two `i64` parameters.  The flattened result has five `i64` slots: tag, error pointer and length, then success pointer and length.  Tag 0 selects the error bytes and tag 1 selects the emitted module.  A host obtains input storage through `alloc`, calls `emitImage`, and copies the selected result before calling `reset` or discarding the instance.

The module has no imports.  Hosts must provide standard WebAssembly multi-value results, `i64`, linear-memory growth, and enough memory for the configured image and output limits.  The bootstrap harness uses the repository's Wasmtime C host.  Direct JavaScript WebAssembly execution remains outside repository tests; a browser adapter is follow-on work rather than evidence for this milestone.

## Bootstrap receipt

The retained 2026-09-02 receipt was rechecked from tracked `selfhost` commit `9036991f812ddd0212f0d905056eb2481b100a37`, tree `69f96946e75bd2ed5208d8acc338fd92ef32a409`.

| Item | Identity |
|------|----------|
| Stage 0 source checker | Lean 4.31.0, commit `68218e876d2a38b1985b8590fff244a83c321783`. |
| Stage 1 and Stage 2 | 568,484 bytes; SHA-256 `b2b511025d4f56f5b2fb8e106072fe149cfe0d1c39c83405659020223d0f0d69`. |
| Canonical self image | 519,107 bytes; SHA-256 `6e9144427e9bc74b32cd16c018812239b421b7790a7f0bb0c6f9246cbd1b8215`. |
| Stage 1 host | Wasmtime 44.0.0, build `af382d7d9`, x86_64 Linux C API. |
| Stage 2 host | A fresh instance under the same Wasmtime 44.0.0 C host. |
| Harness | Pinned Node.js v24.13.0 orchestrates files and the external host without executing WebAssembly itself. |
| Registered corpus | 20 of 20 native, Stage 1, and Stage 2 outputs match the frozen artifact bytes. |
| Error corpus | Five malformed images return the pinned diagnostics under both WebAssembly stages. |

Stage 0 compiles `emitImage` to Stage 1 and separately writes the canonical image of that complete module.  Wasmtime invokes Stage 1 on the image to produce Stage 2, then invokes Stage 2 in a fresh instance on the same image.  Both outputs are compared without normalization and have the Stage 1 length and digest above.  The same two stages emit every case in `proofs/talos/cases.json`; each output is compared with the exact binary selected by `proofs/artifacts/registry.json`.

`test/selfhost_emitter.js` owns this receipt as an optional executable regression check.  Running it without arguments rebuilds the self image, both compiler outputs for every registered case, and all comparisons.  `--use-existing` reruns the hosts and byte comparisons against artifacts already present under `.lake/build/selfhost`.  This experiment does not block native compiler or floating-point development unless a change explicitly targets the image boundary.

An optional 2026-09-03 migration run under Lean 4.34.0-rc2 reproduced a
570,300-byte Stage 1/Stage 2 artifact with SHA-256
`9a4934f9268dc9574f1ec84bf94370ba95ba80d4556adba4fc2fd66b7e448d76`
from a 520,923-byte image with SHA-256
`2344bc92929c1918a78c9f07e6ebf388fa6788747dddec10afcd9564b96f1a2d`.
All twenty registered artifacts and five malformed-image cases still matched.
These values supplement rather than replace the retained 4.31 receipt.

The recorded work-mode run used the user's explicit direct-Lean exception instead of `tools/leanrun`; a local process-path compatibility shim was required only to start Lean in that container and is not an emitter or runtime dependency.  The repository's Node 24.13.0 and `wasm-tools` 1.251.0 version checks passed, and direct execution of the nine-case WAT round-trip gate matched every binary.  The aggregate artifact-proof, semantic-conformance, and cold-checkout release gates remain separate because this session intentionally does not invoke `tools/leanrun`.
