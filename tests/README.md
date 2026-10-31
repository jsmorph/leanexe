# Test suites

## Selecting tests

| Change or question | Checks and their scope |
|---|---|
| Documentation or repository layout | [The documentation checker](../tools/check-doc-links.mjs) checks local links, section anchors, and reachability from the root README.  [The layout checker](../tools/source-layout) checks source imports and the module registries. |
| LeanExe compiler, runtime, or pipeline | [The module driver](modules/run.sh) reads existing files at `build/NAME/NAME.wasm`, compares their cases with native Lean, and checks release counts and the depth guard.  [The full-check procedure](../docs/leanexe-manual.md#the-full-check) gives the build and emission order. |
| Verified compiler or a pure program it compiles | [The verified driver](verified/run.sh) builds its targets, emits modules, validates them, and compares their cases with native Lean.  Cases can state retained blocks and allocation limits as well as results.  [The Verified Compiler Manual](../docs/verified-manual.md#module-cases) describes focused runs. |
| Encoding or decoding | [The decoder test](decoder/DecodeTest.lean) uses the official WebAssembly testsuite.  [The table-profile checks](decoder/TableProfile.lean) cover the narrow table and export forms used by WASI.  [The encoding guide](../LeanExe/Encoding/README.md#tests) gives their setup. |
| Talos, the WebAssembly semantics of the theorems | [Talos's conformance driver](talos/run.sh) runs the testsuite runner of the pinned CodeLib revision over the official WebAssembly testsuite.  It fails on a failed command, an interpreter error, or exhausted fuel, and on any difference from the report that CodeLib commits.  It needs CodeLib's `vendor/testsuite` submodule and `wasm-tools` 1.251.0, and its outputs lie in `build/talos/`. |
| Numerical algorithms | The verified driver checks numerical byte and file theorems and runs the native accuracy checks under [test support](TestSupport/Numerics).  The [algorithm guides](../Library/README.md) state test inputs, reference comparisons, and the scope of the proved results. |
| Hash functions or their fixtures | [Hashing tests](TestSupport/Hashing) compare implementations with their specifications and the vectors described in [Test inputs](../data/README.md). |
| Packed bytes, WASI compilation, or stream effects | [The WASI driver](wasi/run.sh) checks proofs, reflection, decoding, ownership, Lean action execution, and Wasmtime behavior.  `--foundations-only` selects its proof and semantic checks.  [The WASI manual](../docs/wasi.md#tests) explains the groups. |
| Integer or binary64 running sum | [The integer driver](running-sum/run.sh) and [binary64 driver](running-sumfp/run.sh) check the applications' arithmetic, stream behavior, and compiled execution.  The [integer](../Demos/RunningSum/README.md) and [binary64](../Demos/RunningSumFp/README.md) guides state the output and termination premises. |
| Translation to C | [Native execution](native/run.sh) compares translated calls with Talos.  [The corpus driver](native/verified.sh) compares registered modules with Wasmtime.  [The Clight test](native/clight.sh) compares the Lean semantics with CompCert's interpreter.  [The translator design](../docs/native-translator.md#trust-argument-and-validation) explains what each comparison covers. |
| Aligned native translation | [The aligned checks](native/aligned.sh) test the requirement for aligned theorems.  `tests/native/verified.sh --aligned` runs the corpus modules that meet that requirement. |
| Bare-metal programs | [Program tests](baremetal/programs.sh), [input tests](baremetal/inputs.sh), and [corpus tests](baremetal/verified.sh) run AArch64 images under QEMU and check output, status, and stack use.  [The Rocq check](../rocq/README.md) checks the separate proof composition. |
| WGSL kernels | [The kernel driver](wgsl/run.sh) compares output words with native Lean on SwiftShader and llvmpipe.  By default it runs the verified compiler's binary32 and GPT-2 kernels, and `--verified` selects the verified compiler's kernel examples.  `--emit-only` writes kernels and cases, and `--drivers-only` runs existing outputs.  [The browser guide](web/README.md) explains the interactive comparisons. |
| Application behavior | The guides for [GPT](../Demos/Gpt/README.md), [GPT32](../Demos/Gpt32/README.md), [drone planning](../Demos/Drone/README.md), [slew planning](../Demos/Slew/README.md), and [regular expressions](../Library/Regex/README.md) identify their reference comparisons and additional drivers. |

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
`build/native/run/` and `build/native/verified/`.

`tests/verified/run.sh --check-bytes DIR` reads reference modules from `DIR` and writes fresh
emissions to `build/byte-check/verified/`.  `tests/modules/run.sh --check-bytes DIR` writes fresh
emissions to `DIR` and compares them with `build/NAME/NAME.wasm`.  The
[full-check procedure](../docs/leanexe-manual.md#the-full-check) gives the build, emission,
comparison, and execution order.

The native tests require CompCert 3.18's `ccomp` and `clightgen` from one configured tree.
Bare-metal execution also requires `qemu-system-aarch64`.  The Wasmtime and WebGPU tests use
the hosts built by [the host tools](../tools/README.md#execution-hosts).

## Documentation tests

```sh
tools/check-doc-links.mjs
node tools/check-doc-links.test.mjs
```

The checker reads Git's tracked and unignored untracked file inventory, so new documentation
can be checked before staging.  Ignored build outputs cannot satisfy a missing repository link.
The tests use temporary documents to check parsing, path membership, anchors, and traversal,
including an isolated group of documents that link to one another.

## Internal References

- [LeanExe: Commands](../README.md#commands)
- [Verified Compiler Manual: The full check](../docs/verified-manual.md#the-full-check)
