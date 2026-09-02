# Self-Hosted WebAssembly Emitter

Status: active.  This document expands phase 6 of the root [Development Plan](../plan.md).

## Decision and scope

The first self-hosting increment is a self-hosted binary emitter.  It does not move Lean parsing, elaboration, type checking, declaration loading, extraction, specialization, ownership analysis, or IR lowering into WebAssembly.  The existing native compiler performs those stages and freezes their result as a canonical final module image.  A pure LeanExe program decodes that image and serializes the exact WebAssembly module.

The public entry has the accepted source shape:

```lean
def emitImage (input : ByteArray) : Except ByteArray ByteArray
```

A successful result is a complete library-mode WebAssembly module.  An error result is a stable ASCII byte payload identifying a malformed or unsupported image.  The entry contains no `IO`, runtime `String`, `Lean.Environment`, `Lean.Expr`, `Lean.Name`, reflection, FFI, or host calls.

The initial milestone is deliberately narrower than a portable-IR compiler.  It is still material because compiler-owned LEB128, opcode, body, section, export, memory, and global serialization run inside WebAssembly; the generated component reproduces its own complete artifact; and the module-image boundary can later move upward without discarding this work.

## Claims and nonclaims

Completion permits the precise claim that LeanExe has a self-hosted WebAssembly binary emitter.  It does not permit the unqualified claim that LeanExe is self-hosting.

The first milestone does not:

- accept Lean source, `.olean` files, checked declaration bundles, or `LeanExe.IR.Module`;
- perform source-language validation, extraction, ownership decisions, or IR-to-instruction lowering;
- support arbitrary WebAssembly modules outside the profile emitted by LeanExe;
- emit WAT, annotations, or WASI command adapters;
- establish compiler correctness or remove the native Stage 0 compiler from the trust boundary.

A byte-for-byte fixed point establishes deterministic self-reproduction.  It does not show that the reproduced program implements the intended source semantics, and it does not defeat a malicious or systematically incorrect Stage 0 compiler.  Existing differential tests and independent exact-artifact theorems retain their current roles.

## Final module-image boundary

The image is captured after compiler policy and lowering have finished but before any binary bytes are serialized.  It contains every item needed to emit one complete library-mode module, including the runtime functions rather than an instruction to synthesize an implicit runtime.

The first schema records:

- a fixed magic value, schema version, and profile identifier;
- function type information and canonical type indices;
- parameter, result, and local declarations for every function;
- export names as length-prefixed ASCII bytes and their resolved indices;
- the memory and mutable globals used by the LeanExe runtime;
- every user and runtime function body as structured instruction records;
- canonical section ordering and any profile constants required for exact emission.

Names used only for diagnostics, compiler source identities, annotations, or proofs do not enter the image.  Function and global references are already resolved numeric indices.  There are no timestamps, filesystem paths, host-dependent ordering decisions, ignored extension fields, or semantically equivalent alternate encodings.

The first profile covers only the library-mode modules produced by the ordinary `compile` command.  WASI adapters, imports, WAT rendering, and annotation documents remain outside the image until the fixed point and registered-corpus comparisons pass.

## Wire representation

The wire format is compact, deterministic, and owned by LeanExe.  It is not a serialization of Lean runtime objects.  Multibyte counts use one documented canonical encoding, records appear in emission order, and every list has an explicit length or byte extent.

Instruction bodies use a linear record stream with explicit structured delimiters or body extents.  The decoder may construct internal recursive values when that improves clarity, but recursive values never cross the public ABI.  Unknown schema versions, unknown record tags, truncated fields, invalid indices, invalid nesting, non-ASCII export names, duplicate exports, and trailing bytes reject before emission.

Decoder limits cover input bytes, functions, locals, exports, instructions, nesting depth, and output size.  Limits are explicit profile data rather than host-dependent allocation failures.  Malformed input must return `Except.error` instead of trapping wherever the accepted LeanExe language can represent the failure.

## Native refactoring

The native compiler first gains an internal final-module-image type and two paths:

1. construct the image from the current lowered module and runtime definitions;
2. serialize the image through the same pure emitter used by the self-hosted entry.

The ordinary `CoreWasm.moduleBytes` API remains stable while its implementation delegates through the image boundary.  A diagnostic command writes the canonical image for a selected module and entry.  This command is development infrastructure, not a new accepted source-language feature.

Before compiling the emitter to WebAssembly, the refactor must preserve the exact bytes of every registered compiler artifact.  A byte change blocks the phase unless separately reviewed as an intentional compiler change with the normal artifact and proof workflow.

## Accepted-subset implementation

The emitter source stays within the current documented LeanExe language.  Implementation choices should favor direct recursion, first-order helpers, `ByteArray`, supported arrays, supported internal inductives, explicit `Except` errors, and resolved numeric identifiers.

The implementation begins with the smallest complete profile rather than copying all of `LeanExe.Wasm.Binary`.  It reuses the existing LEB128 definitions where their accepted-subset behavior already has tests and proofs.  Opcode serialization has one authoritative definition.  Section construction is deterministic and computes each body or payload length before prefixing it.

The first working version may buffer one encoded function body at a time.  A two-pass size computation or dedicated byte builder is introduced only when retained measurements show excessive copying, allocation, or peak memory.  Performance changes must preserve output bytes and malformed-input behavior.

## Host and execution boundary

The first bootstrap uses the existing library ABI and the Node/Wasmtime host harness.  The host allocates the module-image bytes in exported memory, invokes `emitImage`, decodes the `Except ByteArray ByteArray` result, copies the result before reset, and reports the artifact or diagnostic.

This avoids changing the bounded WASI stdin adapter during the initial experiment.  A WASI stdin-to-stdout compiler wrapper is a follow-on only after self-reproduction succeeds and image sizes, memory growth, output lifetime, and error transport are measured.  Browser execution can use the same library ABI without waiting for that wrapper.

At least two independent WebAssembly hosts run the final corpus.  The initial choices are Wasmtime and the JavaScript `WebAssembly` implementation used by the test harness.

## Bootstrap sequence

Stage 0 is the native `lean-wasm` executable built by the pinned Lean toolchain.

1. Stage 0 builds the emitter source and compiles `emitImage` to `emitter-stage1.wasm`.
2. The native image command writes the canonical image that describes the complete Stage 1 module, including all reachable emitter helpers and runtime functions.
3. The host invokes Stage 1 on that image to produce `emitter-stage2.wasm`.
4. Stage 1 and Stage 2 must be byte-identical, with matching SHA-256 digests.
5. Stage 2 repeats the operation on the same image and must remain at the same fixed point.
6. Both stages emit every registered corpus image, and their bytes must match native emission.
7. The retained receipt records the source revision, tool pins, image-schema version, self-image digest, Stage 1 and Stage 2 artifact digests, host identities, commands, and results.

The comparison operates on complete artifact bytes.  Normalizing or ignoring custom sections, names, order, lengths, or metadata is not permitted.  If future profiles intentionally contain build identity, that identity must itself be deterministic input recorded in the image.

## Implementation progress

- [x] Define the version 1 library-profile data model and canonical unsigned-LEB wire encoding.
- [x] Round-trip every structured instruction record, including nested block, loop, i64-result if, i32-result if, and optional else bodies.
- [x] Reject truncated fields, noncanonical or overflowing integers, unsupported versions and profiles, unknown instruction and export tags, non-ASCII export names, profile-limit violations, and trailing bytes with stable byte diagnostics.
- [x] Add module-level semantic validation for indices, duplicate exports, memory bounds, branch depth, and function-local references.
- [ ] Construct complete images from lowered modules, including the four runtime functions and runtime exports.
- [ ] Emit exact WebAssembly from decoded images and route native library emission through that path.

The first three items are covered by `LeanExe.Wasm.ImageTest`, built directly with the pinned Lean 4.31.0 toolchain under the explicit session exception for the repository runner.

## Work sequence

### 1. Freeze the boundary

- Inventory every datum consumed by current library-mode type, function, memory, global, export, and code section emission.
- Materialize runtime functions in the same final image as user functions.
- Define the schema, limits, canonical ordering, and diagnostic taxonomy.
- Add native image construction, validation, rendering, and malformed-image unit tests.
- Route native library-mode emission through the image and preserve all registered bytes.

### 2. Compile the emitter

- Implement `emitImage` without unsupported runtime features.
- Add focused accepted-source fixtures for its decoder, instruction loop, nested control, body sizing, and section assembly.
- Compile the entry with Stage 0 and execute representative images through Wasmtime.
- Compare native and WebAssembly errors for every malformed-image class.

### 3. Establish self-reproduction

- Generate the Stage 1 self image from the exact artifact-producing revision.
- Require complete Stage 1/Stage 2 byte equality and a stable Stage 2 repeat.
- Run the fixed-point check through both required hosts.
- Preserve failure-stage, exit-status, digest, and resource measurements.

### 4. Cover the repository corpus

- Export images for all registered compiler cases.
- Require native emitter, Stage 1, and Stage 2 byte equality for every case.
- Run the existing execution comparisons, WAT round trip, source-driven Talos checks, and exact-artifact checks required by affected compiler changes.
- Confirm that image support does not alter annotation or proof-package identities.

### 5. Document the resulting boundary

- Add the module-image schema and compatibility rules to maintained reference documentation.
- Describe the library host ABI, result lifetime, limits, and error behavior.
- State the exact self-hosting claim and retain the larger compiler and artifact trust boundaries.
- Remove this detailed plan after completed facts enter reference documentation and any remaining work returns to the root queue.

## Required evidence

During implementation, the repository's normal source-language and compiler gates remain mandatory.  The retained self-hosting evidence additionally includes:

- `git diff --check`, documentation checks, and command review;
- focused Lean builds through `tools/leanrun`;
- native-image round trips and malformed-image tests;
- unchanged registered artifact bytes before the bootstrap is attempted;
- Stage 1/Stage 2 complete byte equality and stable repeat;
- registered-corpus equality across native, Stage 1, and Stage 2 emission;
- successful execution under Wasmtime and the JavaScript host;
- the full execution suite and WAT byte round trip;
- all affected source-driven and exact-artifact proof gates;
- recorded input, output, revision, tool, host, and digest identities.

No gate may silently refresh expected artifacts.  A mismatch retains both candidates and reports the earliest divergent section, function, instruction record, and output byte when available.

## Completion conditions

This phase is complete when one checked-in schema and implementation satisfy all of the following:

- native library-mode emission delegates through the canonical final module image;
- the emitter source compiles under the documented LeanExe subset;
- the WebAssembly emitter reproduces its own complete artifact byte for byte;
- the fixed point repeats under two WebAssembly hosts;
- every registered compiler case is byte-identical across native and both self-hosted stages;
- malformed images reject deterministically without unclassified traps;
- maintained documentation states the resulting capability and nonclaims;
- required compiler, execution, WAT, Talos, artifact, and documentation gates pass.

## Follow-on boundary lifts

After this phase, a separate root-plan decision may move the input boundary upward:

1. serialize `LeanExe.IR.Module` without runtime `Lean.Name` or `String`;
2. run IR-to-structured-instruction lowering inside the WebAssembly component;
3. define a portable checked-declaration bundle and port extraction away from `Lean.Environment`;
4. optionally implement parsing and checking for a deliberately restricted LeanExe surface language.

Each lift retains the final module image as a diagnostic, compatibility, and differential-testing boundary.  None is a prerequisite for the first self-hosted emitter.
