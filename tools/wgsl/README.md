# Native WGSL test harness

`run.py` executes the exact UTF-8 WGSL file with wgpu-native through pinned
wgpu-py. It needs no browser and prefers a CPU adapter when one is available.
The initial ABI is row-major binary32 A/B/C storage buffers and the `gemm_f32`
entry point described by the generated JSON manifest. The harness accepts
arbitrary supported binding indices/groups and two-dimensional workgroups.

## Generate and run on this ARM Mac

The checked local CPU route is `run.py → wgpu-native → Vulkan → SwiftShader`.
It runs as a command-line process, without a browser, Metal or virtual machine.
Generate the supported Lean GEMM candidate and run its exact emitted shader:

```sh
source tools/macos-env.sh
tools/leanrun --timeout 60s lake env lean --run tools/wgsl/Generate.lean build/wgsl/my-gemm 3 5 2 separate
tools/wgsl/run-macos-cpu.sh build/wgsl/my-gemm/kernel.wgsl build/wgsl/my-gemm/manifest.json \
  --report build/wgsl/my-gemm/execution.json
```

Choose fresh artifact/report paths; previous results are retained. The generator
uses the existing checked `gemmCandidate` interface and fixed GEMM template.
The `3 5 2` arguments mean a 3×2 matrix times a 2×5 matrix.

The installed defaults use the isolated environment
`build/wgsl/macos-venv-20260916` and SwiftShader's libraries from the existing
Chrome 152.0.7977.84 installation. Chrome itself is never launched. Override
`LEANEXE_WGPU_PYTHON`, `LEANEXE_WGPU_NATIVE_LIB` or `LEANEXE_SWIFTSHADER_DIR`
to select another installation explicitly. There is no automatic backend fallback.

The standard wgpu-native macOS binary does not enable Vulkan. The optional
`tools/wgsl/build-macos-cpu.sh` setup command installs checksum-pinned Rust 1.90.0
inside `build/tools`, then builds wgpu-native commit
`768f15f6ace8e4ec8e8720d5732b29e0b34250a8` with its locked dependencies and one
build job. The pinned release needs **both** `vulkan-portability` and
`wgc/vulkan-portability`; the outer feature alone fails to enable Vulkan in its
core library. No upstream source modification is needed. This setup requires
Apple command-line build tools already installed on the host.

The approved Python environment uses the five versions in `requirements.txt`
and macOS transitive dependency `rubicon-objc==0.5.6`. To prepare another isolated
Python 3.14 environment, install that set there and select it with
`LEANEXE_WGPU_PYTHON`. The setup script does not install Python or SwiftShader.

Recorded [CPU execution evidence](../../test/wgsl/evidence/macos-swiftshader/)
includes all 15 rectangular GEMM outputs plus fusion-sensitive, signed-zero and
subnormal cases. Every checked word belongs to its manifest's reference relation.
`runtime.json` identifies the source revision, build features, toolchain archives
and actual native/driver library hashes. These runs do not prove universal
runtime conformance to either restricted profile.

## Other native environments

Create an isolated environment, then install the pinned dependency set:

```sh
python3 -m venv /tmp/leanexe-wgsl-venv
/tmp/leanexe-wgsl-venv/bin/python -m pip install -r tools/wgsl/requirements.txt
```

For the checked Linux x86_64 / CPython 3.14 environment, use
`tools/wgsl/requirements-linux-cp314.lock` instead; it additionally requires the
recorded SHA-256 hashes of all five dependency wheels.

Given an emitted artifact and manifest, run:

```sh
tools/wgsl/run.py build/wgsl/gemm.wgsl build/wgsl/gemm.json \
  --python /tmp/leanexe-wgsl-venv/bin/python \
  --report build/wgsl/execution.json
```

Use `--backend Vulkan --adapter llvmpipe` to require Mesa Lavapipe, or
`--backend OpenGL --adapter llvmpipe` for Mesa's native software OpenGL adapter.
No matching adapter, missing dependencies, invalid shader, timeout, and numerical
mismatch all produce a nonzero exit code and an evidence report. Driver
diagnostics are preserved. Adapter discovery/compilation/dispatch/readback run in
a child process with a default 30-second timeout (`--timeout`, maximum 300).
The parent imposes bounded buffer sizes, GEMM work, and exhaustive reference
enumeration. These engineering limits are narrower than generation limits.

The default input generator is a specified 32-bit LCG with finite normal values
and signed zeros. `--seed` reproduces it. `--vectors path.json` instead loads exact
eight-digit hexadecimal binary32 words in `{ "a": [...], "b": [...] }`; values
must be finite with magnitude at most 16. Example 1x1x2 inputs are checked in at
`test/wgsl/vectors/` for fusion, signed-zero accumulation, and subnormals.

The two supported profile ids, both at revision 1, are:

* `leanexe-f32-rne-separate-v1`: source-ordered separate multiplication/addition,
  round-to-nearest ties-to-even, preserved subnormals, IEEE signed zero.
* `leanexe-f32-rne-fusion-v1`: each source-ordered accumulation step may use either
  a separate multiply/add or one fused multiply-add, with the same scalar rules.

The Python reference uses exact rational arithmetic and integer nearest-even
rounding. The fusion profile exhaustively propagates the permitted accumulator
set; exceeding its state/work cap is an error, never an approximate acceptance.
The checker compares bit patterns, including signed zero. It supports neither
general reassociation nor flushing subnormals. Native implementations may fail
these deliberately restricted profiles even when conforming to WGSL.

Reports capture shader text and SHA-256, manifest and hash, exact input/output
words, permitted output sets, profile/WGSL revisions, dispatch/bindings, timeout,
native library hash/version, Python packages, adapter/device information,
selected driver environment variables, and diagnostics. Successful membership
is evidence only for the tested execution. Neither a successful test nor these
identifiers prove universal runtime conformance or a Lean artifact theorem.
The formal scalar model must be connected independently to these numerical
policies. There is currently no proved real-valued error bound in this harness.

The dependency-free regression suite covers IEEE rounding boundaries, signed
zero, subnormals, fusion-sensitive results, rectangular indexing, deterministic
buffers, manifest rejection, and preservation of error evidence:

```sh
python3 test/wgsl/reference_test.py
```

The native API follows the upstream
[wgpu-py 0.31.1 compute example](https://github.com/pygfx/wgpu-py/blob/v0.31.1/examples/compute_noop.py).
The numerical-policy source is the pinned
[17 August 2026 WGSL floating-point evaluation draft](https://www.w3.org/TR/2026/CRD-WGSL-20260817/#floating-point-evaluation).
