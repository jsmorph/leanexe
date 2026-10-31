# Test suites

## Selecting tests

| Change or question | Checks and their scope |
|---|---|
| Documentation or repository layout | [`tools/check-doc-links.mjs`](../tools/check-doc-links.mjs) checks local links, section anchors, and reachability from the root README.  [`tools/source-layout`](../tools/source-layout) checks source imports and the verified module registry. |
| Runtime or pipeline | [`tests/verified/run.sh`](verified/run.sh) runs the cases of every registered module, and through [`tests/modules/run.sh`](modules/run.sh) the module cases of `euler` and of `shapes`.  [`tests/modules/chunks.py`](modules/chunks.py) runs command streams through the verified `clob.wasm` whole, in chunks, and one command at a time.  [`tools/full-check`](../tools/full-check) runs both drivers and the sessions. |
| Verified compiler or a pure program it compiles | [`tests/verified/run.sh`](verified/run.sh) builds its targets, emits modules, validates them, and compares their cases with native Lean.  Cases can state retained blocks and allocation limits as well as results.  [The Verified Compiler Manual](../docs/verified-manual.md#module-cases) describes focused runs. |
| Encoding or decoding | [`tests/decoder/DecodeTest.lean`](decoder/DecodeTest.lean) decodes the official WebAssembly testsuite.  [`tests/decoder/TableProfile.lean`](decoder/TableProfile.lean) covers the narrow table and export forms used by WASI.  [The encoding guide](../LeanExe/Encoding/README.md#tests) gives their setup. |
| Talos, the WebAssembly semantics of the theorems | [`tests/talos/run.sh`](talos/run.sh) runs the testsuite runner of the pinned CodeLib revision over the official WebAssembly testsuite.  It fails on a failed command, an interpreter error, or exhausted fuel, and on any difference from the report that CodeLib commits.  It needs CodeLib's `vendor/testsuite` submodule and `wasm-tools` 1.251.0, and its outputs lie in `build/talos/`. |
| Numerical algorithms | [`tests/verified/run.sh`](verified/run.sh) checks numerical byte and file theorems and runs the native accuracy checks under [test support](TestSupport/Numerics).  The [algorithm guides](../Library/README.md) state test inputs, reference comparisons, and the scope of the proved results. |
| Hash functions or their fixtures | [`tests/TestSupport/Hashing`](TestSupport/Hashing) compares implementations with their specifications and the vectors described in [Test inputs](../data/README.md). |
| Packed bytes, WASI compilation, or stream effects | [`tests/wasi/run.sh`](wasi/run.sh) checks proofs, reflection, decoding, ownership, Lean action execution, and Wasmtime behavior.  `--foundations-only` selects its proof and semantic checks.  [The WASI manual](../docs/wasi.md#tests) explains the groups. |
| Integer or binary64 running sum | [`tests/running-sum/run.sh`](running-sum/run.sh) and [`tests/running-sumfp/run.sh`](running-sumfp/run.sh) check the applications' arithmetic, stream behavior, and compiled execution.  The [integer](../Demos/RunningSum/README.md) and [binary64](../Demos/RunningSumFp/README.md) guides state the output and termination premises. |
| Translation to C | [`tests/native/run.sh`](native/run.sh) compares translated calls with Talos.  [`tests/native/verified.sh`](native/verified.sh) compares registered modules with Wasmtime.  [`tests/native/clight.sh`](native/clight.sh) compares the Lean semantics with CompCert's interpreter.  [The translator design](../docs/native-translator.md#trust-argument-and-validation) explains what each comparison covers. |
| Aligned native translation | [`tests/native/aligned.sh`](native/aligned.sh) tests the requirement for aligned theorems.  `tests/native/verified.sh --aligned` runs the corpus modules that meet that requirement. |
| Bare-metal programs | [`tests/baremetal/programs.sh`](baremetal/programs.sh), [`inputs.sh`](baremetal/inputs.sh), and [`verified.sh`](baremetal/verified.sh) run AArch64 images under QEMU and check output, status, and stack use.  [The Rocq check](../rocq/README.md) checks the separate proof composition. |
| WGSL kernels | [`tests/wgsl/run.sh`](wgsl/run.sh) compares output words with native Lean on SwiftShader and llvmpipe.  By default it runs the verified compiler's binary32 and GPT-2 kernels, and `--verified` selects the verified compiler's kernel examples.  `--emit-only` writes kernels and cases, and `--drivers-only` runs existing outputs.  [The browser guide](web/README.md) explains the interactive comparisons. |
| Application behavior | Guides for [GPT](../Demos/Gpt/README.md), [GPT32](../Demos/Gpt32/README.md), [drone planning](../Demos/Drone/README.md), [slew planning](../Demos/Slew/README.md), and [regular expressions](../Library/Regex/README.md) identify their reference comparisons and additional drivers. |

## Builds, inputs, and outputs

Run commands from the repository root.  Lean and Lake commands use `tools/leanrun`, and the
repository test drivers call that runner themselves.  [The resource instructions](../AGENTS.md#lean-process-limits)
and [cold numerical build procedure](../docs/verified-manual.md#memory-heavy-numerical-proofs)
give the required memory settings and build order.  The full numerical suite can take hours.

The [verified module registry](verified/modules.txt) identifies the source module, module
constant, and emitted name.  [The numerical registry](verified/numerics.txt) names the
emitted module, its byte-theorem module, and its file-theorem module.  The file checks run after
emission because elaboration reads the generated file.  The file theorems state that its bytes
equal the expected encoding and decode to the module.  [Shared test support](TestSupport)
holds case generators, result formatting, and numerical reference calculations.

Default output directories lie under `build/`.  The native execution drivers recreate
`build/native/run/` and `build/native/verified/`.  The verified driver adds to `build/verified/`
without clearing it, and its byte check writes `build/byte-check/verified/`.

`tests/verified/run.sh --check-bytes DIR` reads reference modules from `DIR`, writes fresh emissions
to `build/byte-check/verified/`, and fails at the first module whose bytes differ.  It leaves
`build/verified/` unchanged.  [The full check](../docs/verified-manual.md#the-full-check) gives the
order of the steps.

The native tests require CompCert 3.18's `ccomp` and `clightgen` from one configured tree.
Bare-metal execution also requires `qemu-system-aarch64`.  The Wasmtime and WebGPU tests use
the hosts built by [the host tools](../tools/README.md#execution-hosts).

## Documentation tests

```sh
tools/check-doc-links.mjs
node tools/check-doc-links.test.mjs
```

The checker reads Git's tracked and unignored untracked file inventory, so the checker covers new
documentation before staging.  Ignored build outputs cannot satisfy a missing repository link.  The
tests use temporary documents to check parsing, path membership, anchors, and traversal, including
an isolated group of documents that link to one another.

## Internal references

- [LeanExe: Commands](../README.md#commands)
- [Verified Compiler Manual: The full check](../docs/verified-manual.md#the-full-check)
