# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

import os
import selectors
import subprocess
import time


def read_exact(process: subprocess.Popen, expected: bytes) -> None:
    deadline = time.monotonic() + 10
    received = bytearray()
    with selectors.DefaultSelector() as selector:
        selector.register(process.stdout, selectors.EVENT_READ)
        while len(received) < len(expected):
            remaining = deadline - time.monotonic()
            if remaining <= 0 or not selector.select(remaining):
                raise RuntimeError("Running sum did not produce output before the next input")
            data = os.read(process.stdout.fileno(), len(expected) - len(received))
            if not data:
                raise RuntimeError("Running sum closed stdout before the expected output")
            received.extend(data)
    if received != expected:
        raise RuntimeError(f"Expected {expected!r}, observed {bytes(received)!r}")


def check(command: list[str]) -> None:
    with subprocess.Popen(
        command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE
    ) as process:
        try:
            process.stdin.write(b"12\n")
            process.stdin.flush()
            read_exact(process, b"12\n")
            process.stdin.write(b"-5\n20")
            process.stdin.flush()
            read_exact(process, b"7\n")
            process.stdin.close()
            read_exact(process, b"27\n")
            status = process.wait(timeout=10)
            extra = process.stdout.read()
            errors = process.stderr.read()
            if status != 0 or extra or errors:
                raise RuntimeError(f"Status {status}, extra stdout {extra!r}, stderr {errors!r}")
        except BaseException:
            process.kill()
            process.wait()
            raise


check([".lake/build/bin/running-sum-native"])
check(["build/tools/leanexe-wasmtime-host", "run", "build/running-sum/sum.wasm"])
print("Running sum interactive output: native and Wasm passed")

failed_read = subprocess.run(
    ["sh", "-c", "exec .lake/build/bin/running-sum-native 0<&-"],
    stdout=subprocess.PIPE,
    stderr=subprocess.PIPE,
    timeout=10,
    check=False,
)
if (
    failed_read.returncode == 0
    or failed_read.stdout
    or b"error code:" not in failed_read.stderr
):
    raise RuntimeError(f"Closed stdin did not propagate its error: {failed_read}")
print("Running sum native read error: passed")
