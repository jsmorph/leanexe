#!/usr/bin/env python3
"""Host-only execution of body-compiled shaders; expected words come from Lean."""
import argparse
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from run import execute_dispatch, WGPU_VERSION


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("--vectors", required=True, type=Path)
    parser.add_argument("--report", required=True, type=Path)
    parser.add_argument("--backend", default="Vulkan")
    parser.add_argument("--adapter", default="SwiftShader")
    args = parser.parse_args()
    if args.report.exists():
        raise ValueError("report already exists")
    import wgpu
    if wgpu.__version__ != WGPU_VERSION:
        raise ValueError(f"expected wgpu {WGPU_VERSION}")
    package = json.loads((args.package / "manifest.json").read_text())
    if package.get("kind") != "lean-body-wgsl" or package.get("schemaVersion") != 2:
        raise ValueError("expected a Lean-body compiler package")
    shape = package["shape"]
    if any(type(shape[k]) is not int or not 0 < shape[k] <= 16384
           for k in ("rows", "cols", "elementsA", "elementsB")):
        raise ValueError("shape exceeds bounded execution test limits")
    counts = {"a": shape["elementsA"], "b": shape["elementsB"],
              "c": shape["rows"] * shape["cols"]}
    if counts["c"] > 16384:
        raise ValueError("output exceeds bounded execution test limit")
    vectors = json.loads(args.vectors.read_text())
    for key, count in (("a", counts["a"]), ("b", counts["b"]), ("expected", counts["c"])):
        words = vectors[key]
        if len(words) != count or any(type(w) is not int or not 0 <= w < 2**32 for w in words):
            raise ValueError(f"invalid {key} words")
    adapters = [a for a in wgpu.gpu.enumerate_adapters_sync()
                if a.info["backend_type"] == args.backend
                and args.adapter.lower() in str(dict(a.info)).lower()]
    if not adapters:
        raise RuntimeError("requested native CPU adapter is unavailable")
    adapter = adapters[0]
    device = adapter.request_device_sync()
    manifest = {
        "entryPoint": "lean_kernel", "bindings": {"group": 0, "a": 0, "b": 1, "c": 2},
        "buffers": {key: {"elements": n, "bytes": 4*n} for key, n in counts.items()},
        "dispatchWorkgroups": [(shape["cols"]+7)//8, (shape["rows"]+7)//8, 1],
    }
    actual = execute_dispatch(device, {"manifest": manifest,
        "wgsl": (args.package / "kernel.wgsl").read_text(),
        "inputs": {"a": vectors["a"], "b": vectors["b"]}}, wgpu)
    mismatches = [{"index": i, "expected": e, "actual": a}
                  for i, (e, a) in enumerate(zip(vectors["expected"], actual)) if e != a]
    report = {"status": "pass" if not mismatches else "fail", "adapter": dict(adapter.info),
              "sourceDeclaration": package["sourceDeclaration"], "actual": actual,
              "expected": vectors["expected"], "mismatches": mismatches,
              "evidence": "execution test against original Lean definition under pure IEEE32 arithmetic",
              "universalRuntimeConformanceEstablished": False}
    args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report))
    return 0 if not mismatches else 1


if __name__ == "__main__":
    raise SystemExit(main())
