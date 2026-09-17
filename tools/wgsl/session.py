"""Serial native session: immutable weights, one pipeline, bounded requests."""

import json
import sys

from resident import DispatchPlan


def serve():
    import wgpu
    from run import open_device

    job = json.loads(sys.stdin.readline())
    device, runtime = open_device(job)
    plan = DispatchPlan(device, job, wgpu)
    calls = 0
    try:
        print(json.dumps({"ready": True}), flush=True)
        for line in sys.stdin:
            request = json.loads(line)
            a = request.get("a")
            if not isinstance(a, list) or len(a) != job["manifest"]["buffers"]["a"]["elements"] or any(
                    type(word) is not int or not 0 <= word < 2**32 for word in a):
                raise ValueError("invalid session input words")
            outputs = plan.dispatch(a)
            calls += 1
            print(json.dumps({"outputs": outputs, "runtime": runtime,
                              "resident": {"weightUploads": 1, "pipelineCreations": 1, "dispatches": calls}}), flush=True)
    finally:
        plan.destroy()
