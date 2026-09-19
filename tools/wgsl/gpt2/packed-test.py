#!/usr/bin/env python3
"""CPU dispatch tests; all expected arithmetic is evaluated by PackedVectors.lean."""
import argparse
from array import array
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from run import execute_dispatch, WGPU_VERSION


def fixture(value, count):
    if isinstance(value, dict):
        if set(value) != {"word", "count"} or value["count"] != count:
            raise ValueError("invalid repeated fixture")
        word = value["word"]
        if type(word) is not int or not 0 <= word < 2**32:
            raise ValueError("invalid repeated word")
        return array("I", [word]) * count
    if not isinstance(value, list) or len(value) != count or any(
            type(word) is not int or not 0 <= word < 2**32 for word in value):
        raise ValueError("invalid fixture words")
    return array("I", value)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    if sys.byteorder != "little" or array("I").itemsize != 4:
        raise ValueError("this host test requires little-endian four-byte words")
    import wgpu
    if wgpu.__version__ != WGPU_VERSION:
        raise ValueError(f"expected wgpu {WGPU_VERSION}")
    adapters = [a for a in wgpu.gpu.enumerate_adapters_sync()
                if a.info["backend_type"] == "Vulkan" and "swiftshader" in str(dict(a.info)).lower()]
    if not adapters:
        raise RuntimeError("native SwiftShader CPU adapter unavailable")
    device = adapters[0].request_device_sync()
    rows = []
    cases = [("small",3,2,8),("qkv",768,2304,768*2304+2304),
             ("attention",768,768,768*768+768),("expansion",768,3072,768*3072+3072),
             ("projection",3072,768,3072*768+768),
             ("vocabularyLeft",768,25129,768*25129),("vocabularyRight",768,25128,768*25128)]
    for name, inner, cols, elements_b in cases:
        package = args.directory / name
        manifest = json.loads((package / "manifest.json").read_text())
        if manifest["shape"] != {"rows":1,"cols":cols,"elementsA":inner,"elementsB":elements_b}:
            raise ValueError(f"unexpected shape: {name}")
        data = json.loads((args.directory / "vectors" / f"{name}.json").read_text())
        inputs = {key:fixture(data[key],count).tobytes()
                  for key,count in (("a",inner),("b",elements_b))}
        expected = fixture(data["expected"],cols)
        runtime = {"entryPoint":"lean_kernel","bindings":{"group":0,"a":0,"b":1,"c":2},
                   "buffers":{key:{"elements":count,"bytes":4*count}
                              for key,count in (("a",inner),("b",elements_b),("c",cols))},
                   "dispatchWorkgroups":[(cols+7)//8,1,1]}
        actual = execute_dispatch(device,{"manifest":runtime,"inputs":inputs,
                                  "wgsl":(package / "kernel.wgsl").read_text()},wgpu)
        if len(actual) != cols:
            raise RuntimeError(f"wrong output length: {name}")
        mismatches = [{"column":i,"expected":e,"actual":a}
                      for i,(e,a) in enumerate(zip(expected,actual)) if e != a]
        result = {"case":name,"words":cols,"mismatches":mismatches,"status":"fail" if mismatches else "pass"}
        (package / "execution.json").write_text(json.dumps(result,indent=2)+"\n")
        rows.append(result)
        print(f"{name}: {result['status']}, {cols} output words",flush=True)
        if mismatches:
            raise RuntimeError(f"CPU shader mismatch: {name}")
    report = {"status":"pass","adapter":dict(adapters[0].info),"cases":rows,
              "expectedSource":"original Lean kernel definitions with Wasm.IEEE32 arithmetic",
              "universalWebGPUConformanceProved":False}
    (args.directory / "execution.json").write_text(json.dumps(report,indent=2)+"\n")


if __name__ == "__main__":
    main()
