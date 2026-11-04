# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""The far end of UART0 of QEMU's mps2-an500 for the echoes of the request protocol
(tests/TestSupport/Bare/Req.lean), whose steps cmsdkTick and deadlineCmsdkTick answer each byte
with the byte's bit 5 flipped.

The script listens on a Unix-domain socket in a temporary directory and runs the command QEMU
ARG... followed by "-serial unix:PATH" and "-trace cmsdk_apb_uart_tx_pending -D LOG".  The first
serial port is UART0, and QEMU connects it to the socket before the guest runs, since a socket
device without "server" or "reconnect" connects at once (hw/arm/mps2.c, lines 287 to 308,
chardev/char.c, lines 469 to 475, and chardev/char-socket.c, lines 935 to 954 and 1234 to 1247).
The trace event writes a line to LOG each time the UART's transmitter must wait for the socket
(hw/char/cmsdk-apb-uart.c, lines 205 to 218).  The script then (a) sends MESSAGE one byte at a
time, waiting for each reply; (b) sends bursts of BURSTS bytes from a second thread while it reads
the replies; (c) sends HELD bytes from a second thread, reads nothing until LOG shows that the
transmitter waits, and then reads the replies; and (d) repeats (a), so that a reply in excess of
the bytes sent shows as a wrong reply.  Each reply must equal the byte sent with bit 5 flipped.
With --hold HOLD, for deadlineCmsdkTick, which drops a reply that it cannot write within its
limit of 671 ms after the byte arrived, (c) sends HELD - 1 bytes other than 0xff and then 0xff,
waits HOLD more seconds before it reads, and reads until the reply to 0xff.  The replies must
then be the bytes sent with bit 5 flipped, in order, with at least one missing: the reply to
the byte that the step read while the transmitter waited.  QEMU's CMSDK timer is a ptimer,
which counts on QEMU_CLOCK_VIRTUAL (hw/core/ptimer.c, ptimer_init), and that clock follows the
host's clock while the machine runs, without -icount (system/cpu-timers.c, cpu_get_clock_locked).
Finally it stops QEMU with SIGTERM, after which QEMU must exit with status 0, prints one line, a
summary or the cause of the failure, and exits with status 0 or 1.  TIMEOUT bounds each wait in
seconds.

The references are to QEMU 8.2.2.  The CMSDK UART model holds one received byte and takes a byte
from its character device only while the receiver is enabled and STATE.RXFULL is clear
(hw/char/cmsdk-apb-uart.c, lines 115 to 152).  The socket device reads at most as many bytes as
the model takes (chardev/char-socket.c, lines 141 to 150 and 484 to 513, and chardev/char-io.c,
lines 43 to 64), and a read of DATA clears RXFULL and wakes the device (cmsdk-apb-uart.c, lines
160 to 165).  The bytes of a burst that the model cannot take wait in the socket, so the receiver
never overruns and no byte is lost, whatever the guest's speed.  A write of DATA sets STATE.TXFULL
and sends the byte at once.  TXFULL stays set only while the socket's send buffer is full, until
the main loop's watch on the socket sends the byte (lines 194 to 231 and 249 to 260, and
char-socket.c, lines 107 to 139).  The step therefore finds TXFULL set only when the script leaves
replies unread, as in (c), and a write while TXFULL is set would replace the waiting byte (lines
250 to 256), a lost reply that the check of (c) finds.  On Linux, each one-byte write of QEMU to a
Unix-domain socket takes a buffer of its own from the socket's send buffer of 208 KiB
(net.core.wmem_default), and the transmitter waits after 278 unread replies on the test's host.
A TCP socket on the loopback interface grows its send buffer to 2.5 MiB, which the echo, at about
40 KB/s, fills only after a minute.  The checks depend on no timing: each wait ends on an event of
the socket or of LOG, and TIMEOUT bounds only a failure.

Usage: uv run tests/baremetal/uart_echo.py [--timeout TIMEOUT] [--hold HOLD] LOG QEMU [ARG...]
"""

import argparse
import os
import socket
import subprocess
import sys
import tempfile
import threading
import time

MESSAGE = b"The request protocol's echo answers each byte with bit 5 flipped.\n" + bytes(range(256))
BURSTS = (2, 16, len(MESSAGE), 65536)
HELD = 65536
PENDING = b"cmsdk_apb_uart_tx_pending"
LAST = 0xFF


class Failure(Exception):
    pass


def block(n):
    return (MESSAGE * (n // len(MESSAGE) + 1))[:n]


class Log:
    """The count of the lines of QEMU's log that show the transmitter waiting."""

    def __init__(self, path):
        try:
            self.file = open(path, "rb")
        except FileNotFoundError:
            raise Failure(f"QEMU did not create the log {path}") from None
        self.rest = b""
        self.count = 0

    def pending(self):
        lines = (self.rest + self.file.read()).split(b"\n")
        self.rest = lines.pop()
        self.count += sum(PENDING in line for line in lines)
        return self.count


def receive(conn, n):
    data = bytearray()
    while len(data) < n:
        try:
            chunk = conn.recv(n - len(data))
        except TimeoutError:
            raise Failure(f"{len(data)} of {n} replies, then none for {conn.gettimeout()} s") \
                from None
        if not chunk:
            raise Failure(f"the connection closed after {len(data)} of {n} replies, the last "
                          f"{bytes(data[-64:])!r}")
        data += chunk
    return bytes(data)


def check(what, sent, reply):
    for i, (s, r) in enumerate(zip(sent, reply)):
        if r != s ^ 0x20:
            raise Failure(f"{what}: reply {i} is {r:#04x}, not {s ^ 0x20:#04x} for {s:#04x}; "
                          f"replies {i} on: {reply[i:i + 32]!r}")


def receive_until(conn, last):
    data = bytearray()
    while not data or data[-1] != last:
        try:
            chunk = conn.recv(65536)
        except TimeoutError:
            raise Failure(f"{len(data)} replies without {last:#04x}, then none for "
                          f"{conn.gettimeout()} s") from None
        if not chunk:
            raise Failure(f"the connection closed after {len(data)} replies without {last:#04x}")
        data += chunk
    return bytes(data)


def check_dropped(what, sent, reply):
    """Checks that reply is sent with bit 5 flipped, in order, with bytes missing, and returns
    the number missing."""
    i = 0
    for j, r in enumerate(reply):
        while i < len(sent) and sent[i] ^ 0x20 != r:
            i += 1
        if i == len(sent):
            raise Failure(f"{what}: reply {j}, {r:#04x}, answers no byte sent after those that "
                          f"replies 0 to {j - 1} answer; replies {j} on: {reply[j:j + 32]!r}")
        i += 1
    return len(sent) - len(reply)


def lockstep(conn):
    for i, s in enumerate(MESSAGE):
        conn.sendall(bytes([s]))
        check(f"lockstep byte {i}", [s], receive(conn, 1))


def burst(conn, data, log=None, hold=None):
    """Sends data from a second thread and reads the replies.  With log, it reads nothing until
    the log shows the transmitter waiting, and it returns the number of waits and of replies
    missing.  With hold, it waits hold seconds more and accepts missing replies."""
    errors = []

    def send():
        try:
            conn.sendall(data)
        except OSError as e:
            errors.append(e)

    before = log.pending() if log is not None else 0
    sender = threading.Thread(target=send, daemon=True)
    sender.start()
    if log is not None:
        deadline = time.monotonic() + conn.gettimeout()
        while log.pending() == before:
            if errors:
                raise Failure(f"sending {len(data)} bytes failed: {errors[0]}")
            if time.monotonic() > deadline:
                raise Failure(f"the transmitter did not wait within {conn.gettimeout()} s of "
                              f"holding {len(data)} replies")
            time.sleep(0.01)
    if hold is None:
        reply = receive(conn, len(data))
    else:
        time.sleep(hold)
        reply = receive_until(conn, data[-1] ^ 0x20)
    sender.join()
    if errors:
        raise Failure(f"sending {len(data)} bytes failed: {errors[0]}")
    dropped = 0
    if hold is None:
        check(f"burst of {len(data)}", data, reply)
    else:
        dropped = check_dropped(f"burst of {len(data)}", data, reply)
        if dropped == 0:
            raise Failure(f"burst of {len(data)}: no reply missing after a hold of {hold} s")
    return (log.pending() - before, dropped) if log is not None else (0, 0)


def accept(qemu, listener, timeout):
    listener.settimeout(0.1)
    deadline = time.monotonic() + timeout
    while True:
        try:
            conn, _ = listener.accept()
            conn.settimeout(timeout)
            return conn
        except TimeoutError:
            if qemu.poll() is not None or time.monotonic() > deadline:
                raise Failure("QEMU did not connect") from None


def serve(qemu_args, log_path, timeout, session):
    """Runs QEMU with its first serial port on a Unix-domain socket and with the trace of the
    transmitter's waits in log_path, calls session(conn, Log) on the connection, and stops QEMU.
    Returns session's result, the failure if any, the time taken, and QEMU's status before and
    after the stop."""
    with tempfile.TemporaryDirectory() as tmp, \
            socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as listener:
        path = os.path.join(tmp, "uart0")
        listener.bind(path)
        listener.listen(1)
        qemu = subprocess.Popen(qemu_args + ["-serial", f"unix:{path}", "-trace",
                                             PENDING.decode(), "-D", log_path],
                                stdin=subprocess.DEVNULL)
        start = time.monotonic()
        result, error = None, None
        try:
            with accept(qemu, listener, timeout) as conn:
                result = session(conn, Log(log_path))
        except (Failure, OSError) as e:
            error = e
        elapsed = time.monotonic() - start
        early = qemu.poll()
        qemu.terminate()
        status = qemu.wait()
    return result, error, elapsed, early, status


def report(error, early, status):
    """The line for a failed run, or None."""
    if early is not None:
        return f"QEMU exited with status {early} before the stop" + (f": {error}" if error else "")
    if error:
        return str(error)
    if status != 0:
        return f"QEMU exited with status {status} after SIGTERM"
    return None


def exchange(conn, log, hold):
    lockstep(conn)
    for n in BURSTS:
        burst(conn, block(n))
    if hold is None:
        held = block(HELD)
    else:
        held = bytes(b for b in block(2 * HELD) if b != LAST)[:HELD - 1] + bytes([LAST])
    waits, dropped = burst(conn, held, log, hold)
    lockstep(conn)
    return waits, dropped


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--hold", type=float)
    parser.add_argument("log")
    parser.add_argument("qemu", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    if not args.qemu:
        parser.error("QEMU is missing")
    result, error, elapsed, early, status = serve(
        args.qemu, args.log, args.timeout, lambda conn, log: exchange(conn, log, args.hold))
    failure = report(error, early, status)
    if failure:
        print(failure)
        return 1
    waits, dropped = result
    print(f"{2 * len(MESSAGE)} bytes in lockstep, bursts of {', '.join(map(str, BURSTS))}, "
          f"and {HELD} held bytes, during which the transmitter waited "
          f"{waits} time{'' if waits == 1 else 's'}"
          + ("" if args.hold is None else
             f" and {dropped} repl{'y' if dropped == 1 else 'ies'} went missing after a "
             f"hold of {args.hold:g} s")
          + f", in {elapsed:.1f} s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
