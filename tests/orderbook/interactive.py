# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Interactive output of the order book's process.  The script writes one record to the process's
stdin, a pipe, and reads the record's events from its stdout before it writes the next record, and
then closes stdin and requires status 0 with no further output.  It runs the native executable and
the module through the Wasmtime host.  Usage: uv run tests/orderbook/interactive.py NATIVE HOST WASM
"""

import os
import selectors
import struct
import subprocess
import sys
import time


def words(*values: int) -> bytes:
    return b"".join(struct.pack("<Q", value) for value in values)


# A limit buy of 10 at price 5 for account 7 with tag 1, good till cancelled, from the empty book,
# rests and receives id 1; a cancel of order 1 by account 7 then removes it.
STEPS = [
    (words(1, 0, 5, 10, 7, 1, 0), words(1, 1, 1, 0, 0, 0, 0)),
    (words(3, 1, 7, 0, 0, 0, 0), words(4, 1, 10, 1, 0, 0, 0)),
]


def read_exact(process: subprocess.Popen, expected: bytes) -> None:
    deadline = time.monotonic() + 10
    received = bytearray()
    with selectors.DefaultSelector() as selector:
        selector.register(process.stdout, selectors.EVENT_READ)
        while len(received) < len(expected):
            remaining = deadline - time.monotonic()
            if remaining <= 0 or not selector.select(remaining):
                raise RuntimeError("the process did not write the events before the next record")
            data = os.read(process.stdout.fileno(), len(expected) - len(received))
            if not data:
                raise RuntimeError("the process closed stdout before the expected events")
            received.extend(data)
    if received != expected:
        raise RuntimeError(f"expected {expected.hex()}, observed {bytes(received).hex()}")


def check(command: list[str]) -> None:
    with subprocess.Popen(
        command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE
    ) as process:
        try:
            for record, events in STEPS:
                process.stdin.write(record)
                process.stdin.flush()
                read_exact(process, events)
            process.stdin.close()
            status = process.wait(timeout=10)
            extra = process.stdout.read()
            errors = process.stderr.read()
            if status != 0 or extra or errors:
                raise RuntimeError(f"status {status}, extra stdout {extra!r}, stderr {errors!r}")
        except BaseException:
            process.kill()
            process.wait()
            raise


def main() -> None:
    if len(sys.argv) != 4:
        print("usage: interactive.py NATIVE HOST WASM", file=sys.stderr)
        sys.exit(2)
    native, host, wasm = sys.argv[1:]
    check([native])
    check([host, "run", wasm])
    print("orderbook process interactive output: native and Wasm passed")


main()
