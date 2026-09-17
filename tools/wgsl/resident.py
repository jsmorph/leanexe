"""Bounded head-kernel measurements with one resident weight buffer/pipeline."""

import statistics
import time

from reference import bytes_to_words, words_to_bytes, gemm_results


class DispatchPlan:
    def __init__(self, device, job, wgpu):
        self.device = device
        self.manifest = manifest = job["manifest"]
        bindings = manifest["bindings"]
        shader = device.create_shader_module(code=job["wgsl"])
        self.buffers = {}
        layouts = []
        for name in ("a", "b", "c"):
            usage = wgpu.BufferUsage.STORAGE
            if name in ("a", "c"):
                usage |= wgpu.BufferUsage.COPY_DST
            if name == "c":
                usage |= wgpu.BufferUsage.COPY_SRC
                words = [0x7fc00001] * manifest["buffers"][name]["elements"]
            else:
                words = job["inputs"][name]
            self.buffers[name] = device.create_buffer_with_data(data=words_to_bytes(words), usage=usage)
            layouts.append({"binding": bindings[name], "visibility": wgpu.ShaderStage.COMPUTE,
                            "buffer": {"type": "storage" if name == "c" else "read-only-storage"}})
        group_layout = device.create_bind_group_layout(entries=layouts)
        self.group = bindings["group"]
        group_layouts = [device.create_bind_group_layout(entries=[]) for _ in range(self.group)] + [group_layout]
        pipeline_layout = device.create_pipeline_layout(bind_group_layouts=group_layouts)
        self.bind_groups = [device.create_bind_group(layout=layout, entries=[])
                            for layout in group_layouts[:-1]]
        self.bind_groups.append(device.create_bind_group(layout=group_layout, entries=[
            {"binding": bindings[name], "resource": {"buffer": self.buffers[name], "offset": 0,
                                                     "size": manifest["buffers"][name]["bytes"]}}
            for name in ("a", "b", "c")]))
        self.pipeline = device.create_compute_pipeline(layout=pipeline_layout,
            compute={"module": shader, "entry_point": manifest["entryPoint"]})
        self.sentinel = words_to_bytes([0x7fc00001] * manifest["buffers"]["c"]["elements"])

    def dispatch(self, a=None):
        if a is not None:
            if len(a) != self.manifest["buffers"]["a"]["elements"]:
                raise ValueError("resident input length changed")
            self.device.queue.write_buffer(self.buffers["a"], 0, words_to_bytes(a))
        self.device.queue.write_buffer(self.buffers["c"], 0, self.sentinel)
        encoder = self.device.create_command_encoder()
        compute = encoder.begin_compute_pass()
        compute.set_pipeline(self.pipeline)
        for index, bind_group in enumerate(self.bind_groups):
            compute.set_bind_group(index, bind_group)
        compute.dispatch_workgroups(*self.manifest["dispatchWorkgroups"])
        compute.end()
        self.device.queue.submit([encoder.finish()])
        return bytes_to_words(bytes(self.device.queue.read_buffer(self.buffers["c"])))

    def destroy(self):
        for buffer in self.buffers.values():
            buffer.destroy()


def benchmark(device, job, wgpu):
    from run import integer

    manifest = job["manifest"]
    if manifest["profile"]["id"] != "leanexe-f32-rne-separate-v1":
        raise ValueError("benchmark requires the separate profile")
    config = job["benchmark"]
    repeats = integer(config["repetitions"], "repetitions", 3, 50)
    warmup = integer(config["warmupRounds"], "warmup rounds", 1, 5)
    cases = config["inputsA"]
    if not isinstance(cases, list) or not 1 <= len(cases) <= 16:
        raise ValueError("expected 1–16 resident input cases")
    weights = job["inputs"]["b"]
    if len(weights) != manifest["buffers"]["b"]["elements"]:
        raise ValueError("wrong resident weight count")
    for name, arrays in (("A", cases), ("B", [weights])):
        for words in arrays:
            count = manifest["buffers"][name.lower()]["elements"]
            if not isinstance(words, list) or len(words) != count or any(
                    type(word) is not int or not 0 <= word < 2**32 for word in words):
                raise ValueError(f"invalid {name} word array")
    rows, cols, inner = (manifest["dimensions"][name] for name in ("rows", "cols", "inner"))
    expected = [[next(iter(words)) for words in gemm_results(a, weights, rows, cols, inner,
                                                          manifest["profile"]["id"])] for a in cases]
    setup_job = {**job, "inputs": {"a": cases[0], "b": weights}}
    setup_started = time.perf_counter()
    resident = DispatchPlan(device, setup_job, wgpu)
    setup_ms = 1000 * (time.perf_counter() - setup_started)
    samples = {"recreate": [], "resident": []}
    checked_words = 0
    try:
        # Alternate order each round to reduce order/thermal bias. Timers include
        # input upload, command submission and synchronous readback, not reference
        # arithmetic, Python startup, device creation, or artifact verification.
        for iteration in range(warmup + repeats):
            modes = ("recreate", "resident") if iteration % 2 == 0 else ("resident", "recreate")
            for mode in modes:
                started = time.perf_counter()
                outputs = []
                for a in cases:
                    plan = resident if mode == "resident" else DispatchPlan(device,
                        {**job, "inputs": {"a": a, "b": weights}}, wgpu)
                    try:
                        outputs.append(plan.dispatch(a if mode == "resident" else None))
                    finally:
                        if mode == "recreate":
                            plan.destroy()
                elapsed_ms = 1000 * (time.perf_counter() - started)
                if outputs != expected:
                    raise RuntimeError(f"{mode} outputs differ from the exact separate binary32 reference")
                checked_words += sum(map(len, outputs))
                if iteration >= warmup:
                    samples[mode].append(elapsed_ms)
    finally:
        resident.destroy()
    sequences = (warmup + repeats) * len(cases)
    return {"status": "pass", "samplesMs": samples, "residentSetupMs": setup_ms,
            "medianSequenceMs": {mode: statistics.median(values) for mode, values in samples.items()},
            "rowsPerSequence": rows * len(cases), "checkedWords": checked_words,
            "repetitions": repeats, "warmupRounds": warmup,
            "resident": {"weightUploads": 1, "pipelineCreations": 1, "dispatches": sequences},
            "recreate": {"weightUploads": sequences, "pipelineCreations": sequences, "dispatches": sequences},
            "inputsA": cases, "weightsB": weights, "expectedOutputs": expected,
            "timingScope": "kernel setup when recreated, input upload, submission, synchronous readback and buffer disposal; excludes startup, verification and reference arithmetic",
            "universalRuntimeConformanceEstablished": False}
