# Status

[`tools/full-check`](tools/full-check) wrote this record of the full check of the commit below.  The record covers the tree of that commit with the paths listed as differing from it, and no later commit.  The check builds every module of the six libraries and the test executables, runs the drivers of the verified compiler's modules, of their translations to C and to bare-metal AArch64, of the WASI modules, and of the GPU kernels, and checks the VKB and the Rocq proof.  Each count comes from the output of the step's driver, which the checkout that ran the check keeps in `build/full-check/`.

| Item | Value |
|---|---|
| Commit | [Correct the program guides](https://github.com/jsmorph/leanexe/commit/ce10e13c4c23637e27691316cc4d50d134bc9c49), committed 2026-10-31 06:54 UTC |
| Paths that differed from the commit | None |
| Run | 2026-10-31 06:55 UTC to 2026-10-31 09:31 UTC |
| Lean toolchain | `leanprover/lean4:v4.34.0-rc2` |
| Platform | Linux on AArch64 |

| Step | Status | Duration | Counts |
|---|---|---|---|
| `lake build` of the six libraries and the four test executables | passed | 9 s | 15,226 jobs; 4,710 axiom reports, 4,709 of them with no axiom beyond `propext`, `Classical.choice`, and `Quot.sound`; no `sorry` warning |
| `tests/verified/run.sh` | passed | 54 min | 41,462 cases passed, 0 failed; 2,733 GPT cases passed, 0 failed; 3,096 Euler cases passed, 0 failed; 226 sums cases passed, 0 failed; 100,000 slew edges agree; 130 file theorems with the permitted axioms; 808 theorems in 3 axiom audits; 131 modules written and validated |
| `tests/drone/run.sh` | passed | 40 s | 1,975 calls passed, 0 failed; 116 terrains passed, 0 failed; expected results from the reference implementation |
| `tests/modules/chunks.py` | passed | 8 s | 360 cases passed, 0 failed |
| `tests/native/verified.sh` | passed | 10 min | 41,462 cases passed, 0 failed, 0 not run; 3,322 module cases passed, 0 failed, 0 not run; 0 modules without a translation |
| `tests/native/verified.sh --aligned` | passed | 5 min | 1,024 cases passed, 0 failed, 40,438 not run; 3,096 module cases passed, 0 failed, 226 not run; 0 modules without a translation; 125 modules without aligned theorems |
| `tests/native/aligned.sh` | passed | 9 s | `crcaligned` built with 8 exports; `libwordarray` and `literals` refused |
| `tests/native/run.sh` | passed | 52 s | 20 programs, whose 1,701 calls agree with Talos |
| `tests/native/bytes.sh` | passed | 8 s | 84 of 84 cases agree with Wasmtime; 2 trap cases run |
| `tests/native/clight.sh 7 300 aarch64` | passed | 18 s | 921 programs agree with `ccomp -interp`, 371 of them undefined, 300 of them trace programs, and 300 input programs; 0 differ; 0 out of fuel |
| `tests/wasi/run.sh` | passed | 3 min | 4,372 cases passed in 19 groups; 906 theorems in 21 axiom audits |
| `tests/baremetal/run.sh` | passed | 1 s | probe, unaligned, guard, nofp, entry at EL1, EL2, and EL3, and the device tree pass |
| `tests/baremetal/programs.sh` | passed | 19 s | 5 programs passed, 0 failed |
| `tests/baremetal/inputs.sh` | passed | 10 s | 13 inputs passed, 0 failed |
| `tests/baremetal/verified.sh` | passed | 61 min | 44,784 cases passed, 0 failed, 0 not run, in 110 modules; 0 modules without a translation; 0 modules that do not build |
| `VKB/Check.lean` | passed | 4 s | 29 entries, no problem reported |
| `rocq/check.sh` | passed | 20 s | `Clight2Asm.v` checks, with the assumptions of `transf_c_program_correct` and `ClassicalEpsilon.constructive_indefinite_description` |
| `tests/wgsl/run.sh --verified --emit-only` | passed | 99 s | 9 kernels and 347 cases written |
| `tests/wgsl/run.sh --verified --drivers-only` | passed | 29 s | SwiftShader: 347 cases passed, 0 failed; llvmpipe: 347 cases passed, 0 failed |
| `tests/wgsl/run.sh --emit-only` | passed | 8 min | 17 kernels and 694 cases written |
| `tests/wgsl/run.sh --drivers-only` | passed | 62 s | SwiftShader: 694 cases passed, 0 failed; llvmpipe: 694 cases passed, 0 failed |
| `tests/gpt32/native.sh` | passed | 45 s |  |
| `tests/talos/run.sh` | passed | 8 min | 64,751 commands passed, 0 failed, 346 skipped; report equal to CodeLib's |

These axiom reports of the dependencies' files name an axiom beyond `propext`, `Classical.choice`, and `Quot.sound`:

- `CodeLib.IEEE64.arithmetic_examples` in `CodeLib/IEEE64/Operations.lean` of a dependency: `arithmetic_examples._native.native_decide.ax_1_1`

Every step ran.  The check leaves out `tests/native/subset.sh`, whose result is the count of modules without a translation that `tests/native/verified.sh` reports, `tests/native/bench.sh`, which measures time, the decoder test, which needs the WebAssembly test suite converted by `wasm-tools`, and the bare-metal tests under KVM, which need an AArch64 machine with KVM, while TCG emulates the processor on any machine.
