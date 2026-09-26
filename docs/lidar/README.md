# Deterministic 2D lidar

Lidar is being developed as successive complete Lean → WASM/WGSL → WebGPU
examples. The [development journal](journal.md) records the agenda, figures,
checked results and actual execution evidence.

The first implementation uses four cardinal beams and four closed axis-aligned
rectangles with integer coordinates in `[0,4095]`. One shader invocation owns
one beam result. The scene, directions and results remain in device buffers;
WASM supplies a 16-byte parameter block and a second shader computes a requested
hit-count/nearest-range summary. The host reads only that 4-byte summary.

![First cardinal scan](figures/cardinal.svg)

## Build and run

Use the repository's pinned Lean toolchain and `tools/leanrun` configuration
from [DEVELOPING.md](../../DEVELOPING.md). Install a Vulkan driver on Linux
(`libvulkan1` and `mesa-vulkan-drivers` provide a software adapter on Debian),
or use a supported native WebGPU backend on your platform. Python dependencies
are isolated in an environment:

```sh
uv venv build/lidar/venv
uv pip install --python build/lidar/venv/bin/python -r tools/lidar/requirements.txt
python3 tools/lidar/build.py
build/lidar/venv/bin/python tools/lidar/run.py
python3 tools/lidar/plot.py
```

If local execution without systemd limits has already been authorized, prefix
the build command with `LEANRUN_LOCAL=1`. The build driver uses the repository
runner for every Lean process and checks proofs sequentially. It recognizes the
repository-local pinned toolchain; `LEANRUN_TOOLCHAIN` overrides that selection.

`build/lidar/bundle` contains the emitted shaders, WASM controller, generated
certificates and, after all checks pass, a receipt identifying their bytes.
`build/lidar/run.json` records adapter details, known geometric answers,
observed summaries, transfer counters and artifact digests. Build logs are
under `build/lidar/checks`. The original run is retained in
[evidence/cardinal-run.json](evidence/cardinal-run.json).

The pinned Lean release crashes in its import-memory optimization on the large
compiler proof graph in this environment. [Check.lean](../../tools/lidar/Check.lean)
uses Lean's standard frontend with `leakEnv := false` to avoid that optimization.
It retains ordinary elaboration and kernel checking; the build separately audits
the final theorem dependencies for unexpected axioms.

## Geometry and requests

Directions are east, west, north and south. A four-bit mask selects which beams
contribute to a summary. The hit count is the number of selected beams that hit
any rectangle within range. The maximum range is inclusive. Tangency counts as a
hit, and an origin inside or on an obstacle returns zero. No selected hit
returns `nearest: null`. The demonstration includes an occluded obstacle,
range-boundary hits, a tangent ray, rejected parameters, and repeated scans with
changing sensor positions and request masks.

The first domain is exact integer geometry. It has no Monte Carlo sampling,
sensor noise, trigonometric approximation, or floating-point shader operations.
Oblique directions and explicit uncertainty from numerical input rounding are
subsequent milestones in the journal.

## What the proofs cover

Milestone 1 is complete: geometry, integer arithmetic, parameter packing,
summary formula, exact WGSL certificates, exact WASM controller proofs and
artifact-identity checks have passed. The identified artifacts pass all 12
geometric cases and three invalid-parameter checks on software WebGPU.
Those observed runs remain separate evidence from the universal proofs.

- [Cardinal geometry](../../proofs/talos/lean/Project/Lidar/Cardinal.lean) proves
  nearest-hit selection and the miss characterization for any valid rectangle
  list in the cardinal model.
- [Continuous geometry](../../proofs/talos/lean/Project/Lidar/Continuous.lean)
  interprets those integer answers along real-valued rays and relates reflected
  coordinates to ordinary Cartesian rectangle membership.
- [Integer arithmetic](../../LeanExe/WGSL/UInt.lean) proves zero numerical error
  between mathematical expressions and modeled `u32` evaluation when its bound
  checker accepts the expression and inputs satisfy the stated bounds.
- [Shader composition](../../proofs/talos/lean/Project/Lidar/Shader.lean) connects
  the lidar expression and a certificate for emitted shader statements to the
  continuous nearest-hit property. The accepted grammar has immutable inputs,
  a lane guard and a single lane-owned output write.
- [Controller packing](../../proofs/talos/lean/Project/Lidar/Controller.lean)
  proves bounded parameter packing, rejection and exact field extraction. The
  generated controller certificate uses the arithmetic compiler theorem for
  emitted WASM bytes, decoding, validation and modeled execution.
  [The return-value theorem](../../tools/lidar/ControllerResult.lean) connects
  the exact decoded WASM call to the native Lean packing/rejection function.
- [The pipeline theorem](../../tools/lidar/Application.lean) composes that WASM
  result, the unpacked parameter fields, and the exact scan shader's continuous
  nearest-hit property in one statement.

The artifact checks and the observed runs are separate evidence. Consult the
journal for which checks have completed at the current development milestone.

## Host and arithmetic assumptions

The WGSL proof uses the narrow integer statement model, not a formalization of
every WGSL feature or a verified GPU driver. WebGPU must implement the accepted
`u32` operations and accesses, run the requested lanes to completion, and honor
buffer visibility between dispatches. The model follows WGSL's
[32-bit unsigned integer semantics](https://www.w3.org/TR/WGSL/#integer-types),
including modulo `2^32` arithmetic; the checked bounds prove that wrapping does
not occur on the stated domain. Subtraction is explicitly saturated by
`max(a,b)-b`. No floating-point profile is needed for this first domain. The
WASM engine must implement the modeled 64-bit integer semantics. The packed
valid result fits in 40 bits; the rejected all-ones result is received as `-1`
through Wasmtime's signed host representation.

The native host is responsible for validating rectangle ordering and bounds,
loading the identified artifacts, transferring words without changing their
values, binding the declared buffers, maintaining distinct output storage, and
submitting the scan before its summary. Allocation success, filesystem identity
checks, Python bindings, the driver, operating system and hardware are external
assumptions. The mathematical scene is exact; it is not a claim about an
unmodeled physical sensor or real terrain.

The recorded execution used **Mesa llvmpipe through Vulkan, a CPU WebGPU
adapter**. It establishes observed agreement on the recorded cases, not
universal GPU conformance or hardware-GPU performance.
