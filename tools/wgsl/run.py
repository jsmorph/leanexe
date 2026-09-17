#!/usr/bin/env python3
"""Execute an exact WGSL artifact and record bounded native runtime evidence."""

import argparse
import datetime
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import time

from reference import (PROFILES, bytes_to_words, deterministic_inputs, gemm_results,
                       hex_words, rational, words_to_bytes)

WGSL_REVISION = "2026-08-17"
WGPU_VERSION = "0.31.1"
MAX_OPERATIONS = 262144
MAX_ELEMENTS = 16384


def integer(value, name, minimum=1, maximum=65535):
    if type(value) is not int or not minimum <= value <= maximum:
        raise ValueError(f"{name} must be an integer in [{minimum}, {maximum}]")
    return value


def validate_manifest(manifest):
    if not isinstance(manifest, dict):
        raise ValueError("manifest must be an object")
    for field in ("profile", "dimensions", "bindings", "buffers"):
        if not isinstance(manifest.get(field), dict):
            raise ValueError(f"manifest {field} must be an object")
    if type(manifest.get("schemaVersion")) is not int or manifest["schemaVersion"] != 1 or manifest.get("kernel") != "gemm_f32":
        raise ValueError("expected schemaVersion 1 GEMM manifest")
    if manifest.get("entryPoint") != "gemm_f32":
        raise ValueError("only the gemm_f32 entry point is supported")
    if manifest.get("wgslRevision") != WGSL_REVISION:
        raise ValueError("unsupported WGSL revision")
    profile = manifest.get("profile", {})
    if profile.get("id") not in PROFILES or type(profile.get("revision")) is not int or profile["revision"] != 1:
        raise ValueError("unsupported profile id/revision")
    dims = manifest["dimensions"]
    m, n, k = (integer(dims[name], name) for name in ("rows", "cols", "inner"))
    if m * n * k > MAX_OPERATIONS:
        raise ValueError("GEMM exceeds bounded reference operation limit")
    sizes = {"a": m * k, "b": k * n, "c": m * n}
    for name, count in sizes.items():
        if count > MAX_ELEMENTS:
            raise ValueError("buffer exceeds harness element limit")
        buffer = manifest["buffers"][name]
        if not isinstance(buffer, dict):
            raise ValueError("buffer layout must be an object")
        integer(buffer["elements"], "buffer elements", 1, MAX_ELEMENTS)
        integer(buffer["bytes"], "buffer bytes", 4, 4 * MAX_ELEMENTS)
        if buffer != {"elements": count, "bytes": 4 * count}:
            raise ValueError(f"inconsistent {name} buffer layout")
    bindings = manifest["bindings"]
    integer(bindings["group"], "group", 0, 3)
    slots = [integer(bindings[name], name, 0, 999) for name in ("a", "b", "c")]
    if len(set(slots)) != 3:
        raise ValueError("storage buffer bindings must be distinct")
    workgroup = manifest["workgroupSize"]
    if not isinstance(workgroup, list) or len(workgroup) != 3:
        raise ValueError("expected two-dimensional workgroup size")
    integer(workgroup[2], "workgroup z", 1, 1)
    x, y = (integer(workgroup[i], "workgroup size", 1, 256) for i in range(2))
    if x * y > 256:
        raise ValueError("workgroup size exceeds portable limit")
    expected_dispatch = [(n + x - 1) // x, (m + y - 1) // y, 1]
    dispatch = manifest["dispatchWorkgroups"]
    if not isinstance(dispatch, list) or len(dispatch) != 3:
        raise ValueError("expected three dispatch dimensions")
    for value in dispatch:
        integer(value, "dispatch dimension")
    if dispatch != expected_dispatch:
        raise ValueError("dispatch dimensions do not cover the output exactly once")
    return m, n, k


def parse_vectors(path, counts):
    vectors = json.loads(path.read_text())
    if not isinstance(vectors, dict) or set(vectors) != {"a", "b"}:
        raise ValueError("vectors must contain only a and b binary32 hex arrays")
    result = {}
    for name, count in counts.items():
        values = vectors[name]
        if not isinstance(values, list) or len(values) != count:
            raise ValueError(f"wrong vector length for {name}")
        if any(not isinstance(word, str) or not re.fullmatch(r"[0-9a-fA-F]{8}", word) for word in values):
            raise ValueError("vector entries must be eight hexadecimal digits")
        result[name] = [int(word, 16) for word in values]
        if any(abs(rational(word)) > 16 for word in result[name]):
            raise ValueError("harness inputs must be finite and have magnitude at most 16")
    return result


def open_device(job):
    import wgpu
    import wgpu.backends.wgpu_native as native

    if wgpu.__version__ != WGPU_VERSION:
        raise RuntimeError(f"expected wgpu {WGPU_VERSION}, found {wgpu.__version__}")
    manifest = job["manifest"]
    validate_manifest(manifest)
    adapters = wgpu.gpu.enumerate_adapters_sync()
    adapters = [adapter for adapter in adapters
                if (not job["backend"] or adapter.info["backend_type"] == job["backend"])
                and job["adapter"].lower() in str(dict(adapter.info)).lower()]
    if not adapters:
        raise RuntimeError("no native WebGPU adapter matched; install/configure a supported driver (e.g. Mesa Lavapipe)")
    adapters.sort(key=lambda adapter: (adapter.info["adapter_type"] != "CPU", str(dict(adapter.info))))
    adapter = adapters[0]
    device = adapter.request_device_sync()
    native_path = getattr(native, "lib_path", None)
    runtime = {"python": platform.python_version(), "platform": platform.platform(),
               "wgpuPy": wgpu.__version__, "wgpuNative": str(native.__version__),
               "adapter": dict(adapter.info), "deviceLimits": dict(device.limits),
               "environment": {key: os.environ.get(key) for key in
                               ("WGPU_BACKEND_TYPE", "WGPU_LIB_PATH", "VK_ICD_FILENAMES", "VK_DRIVER_FILES",
                                "LIBGL_ALWAYS_SOFTWARE", "MESA_LOADER_DRIVER_OVERRIDE")}}
    if native_path and Path(native_path).is_file():
        runtime["wgpuNativeLibrarySha256"] = hashlib.sha256(Path(native_path).read_bytes()).hexdigest()
    runtime["pythonPackages"] = {name: importlib.metadata.version(name)
                                 for name in ("wgpu", "cffi", "pycparser", "rendercanvas", "numpy")}
    return device, runtime


def execute_worker(job):
    import wgpu

    device, runtime = open_device(job)
    try:
        if "benchmark" in job:
            from resident import benchmark
            return {"runtime": runtime, "benchmark": benchmark(device, job, wgpu)}
        return {"runtime": runtime, "outputs": execute_dispatch(device, job, wgpu)}
    except Exception as error:
        return {"runtime": runtime, "error": f"{type(error).__name__}: {error}"}


def execute_dispatch(device, job, wgpu):
    manifest = job["manifest"]
    shader = device.create_shader_module(code=job["wgsl"])
    bindings = manifest["bindings"]
    layouts = []
    buffers = {}
    for name in ("a", "b", "c"):
        usage = wgpu.BufferUsage.STORAGE
        if name == "c":
            usage |= wgpu.BufferUsage.COPY_SRC
            # Nonzero initialization makes missing stores visible to the checker.
            words = [0x7fc00001] * manifest["buffers"][name]["elements"]
        else:
            words = job["inputs"][name]
        buffers[name] = device.create_buffer_with_data(data=words_to_bytes(words), usage=usage)
        layouts.append({"binding": bindings[name], "visibility": wgpu.ShaderStage.COMPUTE,
                        "buffer": {"type": "storage" if name == "c" else "read-only-storage"}})
    group_layout = device.create_bind_group_layout(entries=layouts)
    group = bindings["group"]
    group_layouts = [device.create_bind_group_layout(entries=[]) for _ in range(group)] + [group_layout]
    pipeline_layout = device.create_pipeline_layout(bind_group_layouts=group_layouts)
    bind_group = device.create_bind_group(layout=group_layout, entries=[
        {"binding": bindings[name], "resource": {"buffer": buffers[name], "offset": 0,
                                                "size": manifest["buffers"][name]["bytes"]}}
        for name in ("a", "b", "c")])
    pipeline = device.create_compute_pipeline(layout=pipeline_layout,
                                             compute={"module": shader, "entry_point": manifest["entryPoint"]})
    encoder = device.create_command_encoder()
    compute = encoder.begin_compute_pass()
    compute.set_pipeline(pipeline)
    for index in range(group):
        compute.set_bind_group(index, device.create_bind_group(layout=group_layouts[index], entries=[]))
    compute.set_bind_group(group, bind_group)
    compute.dispatch_workgroups(*manifest["dispatchWorkgroups"])
    compute.end()
    device.queue.submit([encoder.finish()])
    result = bytes(device.queue.read_buffer(buffers["c"]))
    return bytes_to_words(result)


def run(args):
    if args.report.exists() or args.report.is_symlink():
        print(json.dumps({"status": "error", "report": str(args.report),
                          "error": "report already exists; choose a fresh evidence path"}))
        return 1
    started = time.monotonic()
    report = {"schemaVersion": 1, "status": "error",
              "timestampUtc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
              "evidenceKind": "tested-execution-only", "universalRuntimeConformanceEstablished": False,
              "formalArtifactProofEstablished": False,
              "runtimeAssumption": "Compiler, device, and execution system satisfy the recorded profile and shared semantics; testing does not establish this universally."}
    try:
        # The package gate can pass the exact bytes it has just checked over
        # stdin, avoiding a second filesystem read between proof and dispatch.
        snapshot = json.load(sys.stdin) if getattr(args, "snapshot_stdin", False) else None
        if snapshot is not None and (not isinstance(snapshot, dict) or
                set(snapshot) != {"artifactUtf8", "manifestUtf8"} or
                any(type(value) is not str for value in snapshot.values())):
            raise ValueError("invalid verified input snapshot")
        data = snapshot["artifactUtf8"].encode("utf-8") if snapshot is not None else args.artifact.read_bytes()
        if len(data) > 1024 * 1024:
            raise ValueError("WGSL artifact exceeds one MiB limit")
        source = data.decode("utf-8")
        if "\0" in source:
            raise ValueError("WGSL source cannot contain NUL characters")
        report["artifact"] = {"path": str(args.artifact), "sha256": hashlib.sha256(data).hexdigest(),
                              "byteLength": len(data), "text": source}
        manifest_bytes = snapshot["manifestUtf8"].encode("utf-8") if snapshot is not None else args.manifest.read_bytes()
        manifest = json.loads(manifest_bytes)
        report["manifest"] = manifest
        report["manifestSha256"] = hashlib.sha256(manifest_bytes).hexdigest()
        m, n, k = validate_manifest(manifest)
        if args.vectors:
            inputs = parse_vectors(args.vectors, {"a": m * k, "b": k * n})
            report["inputSource"] = {"vectors": str(args.vectors)}
        else:
            integer(args.seed, "seed", 0, 0xffffffff)
            inputs = {"a": deterministic_inputs(m * k, args.seed),
                      "b": deterministic_inputs(k * n, args.seed ^ 0x9e3779b9)}
            report["inputSource"] = {"generator": "lcg-normal-signed-zero-v1", "seed": args.seed}
        report["inputs"] = {name: hex_words(words) for name, words in inputs.items()}
        expected = gemm_results(inputs["a"], inputs["b"], m, n, k, manifest["profile"]["id"])
        report["permittedOutputs"] = [hex_words(words) for words in expected]
        report["executionConfiguration"] = {"backendFilter": args.backend, "adapterFilter": args.adapter,
                                              "timeoutSeconds": args.timeout, "workerPython": args.python,
                                              "initialOutputWord": "7fc00001", "pipelineConstants": {}}
        job = {"manifest": manifest, "wgsl": source, "inputs": inputs,
               "backend": args.backend, "adapter": args.adapter}
        worker = subprocess.run([args.python, str(Path(__file__).resolve()), "--worker"],
                                input=json.dumps(job), capture_output=True, text=True, timeout=args.timeout)
        report["workerStderr"] = worker.stderr
        if worker.returncode:
            report["workerStdout"] = worker.stdout
            raise RuntimeError(f"native worker exited with status {worker.returncode}: {worker.stderr.strip()}")
        response = json.loads(worker.stdout)
        report["runtime"] = response["runtime"]
        if "error" in response:
            raise RuntimeError(response["error"])
        outputs = response["outputs"]
        report["outputs"] = hex_words(outputs)
        if len(outputs) != len(expected):
            raise RuntimeError("native worker returned wrong output buffer length")
        failures = [{"index": index, "actual": f"{actual:08x}", "permitted": hex_words(permitted)}
                    for index, (actual, permitted) in enumerate(zip(outputs, expected)) if actual not in permitted]
        report["check"] = {"kind": "exact-profile-relation-membership", "passed": not failures,
                           "checkedElements": len(expected), "failures": failures}
        report["status"] = "pass" if not failures else "mismatch"
    except subprocess.TimeoutExpired as error:
        report["error"] = f"native worker timed out after {args.timeout} seconds"
        report["workerStderr"] = (error.stderr or b"").decode(errors="replace") if isinstance(error.stderr, bytes) else error.stderr
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
        report["error"] = f"{type(error).__name__}: {error}"
    report["elapsedSeconds"] = time.monotonic() - started
    args.report.parent.mkdir(parents=True, exist_ok=True)
    # Exclusive creation also protects evidence created while the worker ran.
    try:
        with args.report.open("x") as output:
            output.write(json.dumps(report, indent=2, sort_keys=True) + "\n")
    except OSError as error:
        print(json.dumps({"status": "error", "report": str(args.report), "error": str(error)}))
        return 1
    print(json.dumps({"status": report["status"], "report": str(args.report), "error": report.get("error")}))
    return 0 if report["status"] == "pass" else 1


def main():
    if sys.argv[1:] == ["--session"]:
        try:
            from session import serve
            serve()
        except Exception as error:
            print(json.dumps({"error": f"{type(error).__name__}: {error}"}), flush=True)
            return 1
        return 0
    if sys.argv[1:] == ["--worker"]:
        try:
            print(json.dumps(execute_worker(json.load(sys.stdin))))
        except Exception as error:
            print(f"{type(error).__name__}: {error}", file=sys.stderr)
            return 1
        return 0
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("artifact", type=Path)
    parser.add_argument("manifest", type=Path)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--vectors", type=Path)
    parser.add_argument("--snapshot-stdin", action="store_true",
                        help="read exact shader/manifest text from the package gate over stdin")
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--timeout", type=int, choices=range(1, 301), default=30, metavar="SECONDS")
    parser.add_argument("--python", default=sys.executable, help="Python with the pinned wgpu dependency installed")
    parser.add_argument("--backend", choices=("Vulkan", "OpenGL", "Metal", "D3D12"), default="")
    parser.add_argument("--adapter", default="", help="adapter information substring filter")
    return run(parser.parse_args())


if __name__ == "__main__":
    sys.exit(main())
