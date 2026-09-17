#!/usr/bin/env python3
"""Dependency-free arithmetic and harness boundary regression tests."""

from fractions import Fraction
import importlib.util
import json
from pathlib import Path
import random
import struct
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/wgsl"))
from reference import (FUSION_PROFILE, SIGN, STRICT_PROFILE, add, bytes_to_words,
                       deterministic_inputs, fused, gemm_results, multiply,
                       rational, round_binary32, words_to_bytes)

spec = importlib.util.spec_from_file_location("wgsl_run", ROOT / "tools/wgsl/run.py")
harness = importlib.util.module_from_spec(spec)
spec.loader.exec_module(harness)


def manifest(rows=2, cols=3, inner=4):
    return {"schemaVersion": 1, "kernel": "gemm_f32", "entryPoint": "gemm_f32",
            "wgslRevision": "2026-08-17", "profile": {"id": STRICT_PROFILE, "revision": 1},
            "dimensions": {"rows": rows, "cols": cols, "inner": inner},
            "bindings": {"group": 0, "a": 0, "b": 1, "c": 2},
            "workgroupSize": [8, 8, 1], "dispatchWorkgroups": [(cols + 7) // 8, (rows + 7) // 8, 1],
            "buffers": {name: {"elements": size, "bytes": size * 4} for name, size in
                        (("a", rows * inner), ("b", inner * cols), ("c", rows * cols))}}


class ReferenceTests(unittest.TestCase):
    def test_ieee_edges(self):
        self.assertEqual(multiply(1, 0x3f000000), 0)
        self.assertEqual(multiply(3, 0x3f000000), 2)
        self.assertEqual(multiply(SIGN | 1, 0x3f000000), SIGN)
        self.assertEqual(add(0x007fffff, 1), 0x00800000)
        self.assertEqual(add(SIGN, SIGN), SIGN)
        self.assertEqual(add(SIGN, 0), 0)
        self.assertEqual(add(0xbf800000, 0x3f800000), 0)
        self.assertEqual(multiply(SIGN, 0x3f800000), SIGN)
        self.assertEqual(fused(SIGN, 0x3f800000, SIGN), SIGN)
        self.assertEqual(fused(SIGN, 0x3f800000, 0), 0)
        self.assertEqual(add(0x3f800000, 0x33800000), 0x3f800000)
        self.assertEqual(add(0x3f800001, 0x33800000), 0x3f800002)
        with self.assertRaisesRegex(ValueError, "infinities"):
            rational(0x7f800000)
        with self.assertRaisesRegex(ValueError, "overflow"):
            multiply(0x7f7fffff, 0x40000000)

    def test_round_trip_and_host_crosscheck(self):
        rng = random.Random(0x5747534c)
        words = [0, SIGN, 1, SIGN | 1, 0x007fffff, 0x00800000, 0x7f7fffff]
        words += [rng.randrange(0x7f800000) | (rng.randrange(2) << 31) for _ in range(1000)]
        for word in words:
            self.assertEqual(round_binary32(rational(word), word == SIGN), word)
        # These moderate finite operands make binary64 addition/product exact
        # enough for an independent struct-to-f32 nearest-even cross-check.
        for _ in range(500):
            a, b = [rng.randrange(0x3b000000, 0x43000000) | (rng.randrange(2) << 31) for _ in range(2)]
            x, y = [struct.unpack("<f", struct.pack("<I", word))[0] for word in (a, b)]
            host = lambda value: struct.unpack("<I", struct.pack("<f", value))[0]
            self.assertEqual(multiply(a, b), host(x * y))
            self.assertEqual(add(a, b), host(x + y))

    def test_fusion_relation(self):
        a, b = 0x3f800001, 0x3f7ffffe
        self.assertEqual(add(multiply(a, b), 0xbf800000), 0)
        self.assertEqual(fused(a, b, 0xbf800000), 0xa8800000)
        inputs_a, inputs_b = [0xbf800000, a], [0x3f800000, b]
        self.assertEqual(gemm_results(inputs_a, inputs_b, 1, 1, 2, STRICT_PROFILE), [[0]])
        self.assertEqual(gemm_results(inputs_a, inputs_b, 1, 1, 2, FUSION_PROFILE), [[0, 0xa8800000]])
        with self.assertRaisesRegex(ValueError, "choice limit"):
            gemm_results(inputs_a, inputs_b, 1, 1, 2, FUSION_PROFILE, max_choices=1)
        with self.assertRaisesRegex(ValueError, "work limit"):
            gemm_results(inputs_a, inputs_b, 1, 1, 2, FUSION_PROFILE, max_work=1)

    def test_rectangular_indexing(self):
        encode = lambda values: [round_binary32(Fraction(value)) for value in values]
        actual = gemm_results(encode([1, 2, 3, 4]), encode([1, 2, 3, 4, 5, 6]), 2, 3, 2, STRICT_PROFILE)
        self.assertEqual(actual, [[word] for word in encode([9, 12, 15, 19, 26, 33])])

    def test_reproducible_serialization(self):
        values = deterministic_inputs(100, 123)
        self.assertEqual(values, deterministic_inputs(100, 123))
        self.assertNotEqual(values, deterministic_inputs(100, 124))
        self.assertEqual(bytes_to_words(words_to_bytes(values)), values)


class BoundaryTests(unittest.TestCase):
    def test_manifest_rejections(self):
        self.assertEqual(harness.validate_manifest(manifest()), (2, 3, 4))
        mutations = [lambda m: m["profile"].update(revision=2),
                     lambda m: m.update(profile=None),
                     lambda m: m.update(schemaVersion=True),
                     lambda m: m["dimensions"].update(inner=0),
                     lambda m: m["dimensions"].update(inner=True),
                     lambda m: m["bindings"].update(c=0),
                     lambda m: m["buffers"]["a"].update(bytes=4),
                     lambda m: m.update(dispatchWorkgroups=[0, 0, 0]),
                     lambda m: m.update(dispatchWorkgroups=[1.0, 1, 1]),
                     lambda m: m.update(workgroupSize=[8, 8, True]),
                     lambda m: m.update(workgroupSize=[32, 32, 1])]
        for mutate in mutations:
            value = manifest()
            mutate(value)
            with self.assertRaises(ValueError):
                harness.validate_manifest(value)

    def test_failure_preserves_artifact_and_diagnostics(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            artifact = directory / "exact.wgsl"
            metadata = directory / "manifest.json"
            report = directory / "report.json"
            artifact.write_bytes(b"// exact bytes\r\n")
            metadata.write_text(json.dumps(manifest()))
            result = subprocess.run([sys.executable, str(ROOT / "tools/wgsl/run.py"),
                                     str(artifact), str(metadata), "--python", "/nonexistent/python",
                                     "--report", str(report)], capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 1)
            evidence = json.loads(report.read_text())
            self.assertEqual(evidence["status"], "error")
            self.assertEqual(evidence["artifact"]["text"], "// exact bytes\r\n")
            self.assertIn("FileNotFoundError", evidence["error"])
            self.assertFalse(evidence["formalArtifactProofEstablished"])
            self.assertFalse(evidence["universalRuntimeConformanceEstablished"])

    def test_timeout_is_failure_with_report(self):
        with tempfile.TemporaryDirectory() as directory:
            directory = Path(directory)
            artifact, metadata, report, worker = [directory / name for name in
                                                   ("kernel.wgsl", "manifest.json", "report.json", "worker")]
            artifact.write_text("// unused by timed-out worker\n")
            metadata.write_text(json.dumps(manifest()))
            worker.write_text("#!/usr/bin/env python3\nimport time\ntime.sleep(10)\n")
            worker.chmod(0o755)
            result = subprocess.run([sys.executable, str(ROOT / "tools/wgsl/run.py"),
                                     str(artifact), str(metadata), "--python", str(worker),
                                     "--timeout", "1", "--report", str(report)],
                                    capture_output=True, text=True, timeout=5)
            self.assertEqual(result.returncode, 1)
            evidence = json.loads(report.read_text())
            self.assertEqual(evidence["status"], "error")
            self.assertIn("timed out after 1 seconds", evidence["error"])


if __name__ == "__main__":
    unittest.main()
