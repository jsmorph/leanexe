# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""The far end of USART3 of a NUCLEO-F767ZI for the diagnostic image of
tests/TestSupport/M7/Diag.lean, which reports the debug registers and RCC_CSR as the last reset
left them.

The script opens the serial port DEVICE, the virtual COM port of the board's ST-LINK, through
serve_device of tests/baremetal/uart_echo.py at BAUD, 4,800 unless set, discards the bytes that
arrive until 0.5 s pass without one, sends one byte, and reads the record's 48 bytes: the magic
word 0xD1A6C0DE, the number of starts since the image wrote the magic word, and DHCSR, DEMCR,
DFSR, FP_CTRL, DWT_CTRL, ITM_TCR, DBGMCU_CR, DBGMCU_APB1_FZ, DBGMCU_APB2_FZ, and RCC_CSR, each
word's low byte first.  It sends a second byte and requires the same 48 bytes.  It prints the
start count and the registers in one line and checks them against EXPECT:

- probe, the state that st-flash reset leaves: DHCSR.C_DEBUGEN 1 and DBGMCU_APB1_FZ 0x1800, which
  shows that the image reads the bits that a debugger sets;
- nrst, the state after tools/baremetal/stlink_nrst.py: DHCSR's control bits C_DEBUGEN, C_HALT,
  C_STEP, C_MASKINTS, and C_SNAPSTALL 0, DEMCR 0, FP_CTRL and DWT_CTRL at a reset value of the
  Cortex-M7 (DDI 0489F, Tables 9-7 and 11-1), ITM_TCR 0, the DBGMCU registers 0, and RCC_CSR
  0x04000000, PINRSTF alone;
- power-on, the state after a power-on: the values of nrst with RCC_CSR 0x0E000000, PORRSTF,
  PINRSTF, and BORRSTF (RM0410 section 5.3.21).

DFSR keeps its status bits over a system reset, and the script reports it without a check.  With
--start START, the start count must equal START.  The script prints the line, followed by the
failed checks if any, and exits with status 0 or 1.  TIMEOUT bounds each wait in seconds.

Usage: uv run tests/baremetal/uart_diag.py [--timeout TIMEOUT] --device DEVICE [--baud BAUD]
         --expect probe|nrst|power-on [--start START]
"""

import argparse
import struct
import sys

from uart_echo import Failure, serve_device

MAGIC = 0xD1A6C0DE
NAMES = ["DHCSR", "DEMCR", "DFSR", "FP_CTRL", "DWT_CTRL", "ITM_TCR", "DBGMCU_CR",
         "DBGMCU_APB1_FZ", "DBGMCU_APB2_FZ", "RCC_CSR"]
FP_CTRL_RESET = (0x10000040, 0x10000080)
DWT_CTRL_RESET = (0x40000000, 0x48000000, 0x20000000, 0x28000000)


def recv_exact(conn, n):
    data = bytearray()
    while len(data) < n:
        try:
            chunk = conn.recv(n - len(data))
        except TimeoutError:
            raise Failure(f"{len(data)} of {n} bytes within {conn.gettimeout()} s") from None
        if not chunk:
            raise Failure(f"the port closed after {len(data)} of {n} bytes")
        data += chunk
    return bytes(data)


def drain(conn):
    saved = conn.timeout
    conn.timeout = 0.5
    try:
        while True:
            try:
                if not conn.recv(256):
                    return
            except TimeoutError:
                return
    finally:
        conn.timeout = saved


def session(conn):
    drain(conn)
    conn.sendall(b"?")
    first = recv_exact(conn, 48)
    conn.sendall(b"?")
    second = recv_exact(conn, 48)
    if second != first:
        raise Failure(f"two records differ: {first.hex()} and {second.hex()}")
    words = struct.unpack("<12I", first)
    if words[0] != MAGIC:
        raise Failure(f"no magic word: {first.hex()}")
    return words[1], dict(zip(NAMES, words[2:]))


def checks(expect, r):
    """The failed checks of the registers r for the expected state."""
    if expect == "probe":
        want = [("DHCSR.C_DEBUGEN 1", r["DHCSR"] & 1 == 1),
                ("DBGMCU_APB1_FZ 0x00001800", r["DBGMCU_APB1_FZ"] == 0x1800)]
    else:
        csr = 0x04000000 if expect == "nrst" else 0x0E000000
        want = [("DHCSR's control bits 0", r["DHCSR"] & 0x2F == 0),
                ("DEMCR 0", r["DEMCR"] == 0),
                ("FP_CTRL at a reset value", r["FP_CTRL"] in FP_CTRL_RESET),
                ("DWT_CTRL at a reset value", r["DWT_CTRL"] in DWT_CTRL_RESET),
                ("ITM_TCR 0", r["ITM_TCR"] == 0),
                ("DBGMCU_CR 0", r["DBGMCU_CR"] == 0),
                ("DBGMCU_APB1_FZ 0", r["DBGMCU_APB1_FZ"] == 0),
                ("DBGMCU_APB2_FZ 0", r["DBGMCU_APB2_FZ"] == 0),
                (f"RCC_CSR 0x{csr:08x}", r["RCC_CSR"] == csr)]
    return [name for name, ok in want if not ok]


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--device", required=True)
    parser.add_argument("--baud", type=int, default=4800)
    parser.add_argument("--expect", required=True, choices=["probe", "nrst", "power-on"])
    parser.add_argument("--start", type=int)
    args = parser.parse_args()
    result, error, _ = serve_device(args.device, args.baud, args.timeout,
                                    lambda conn, log: session(conn))
    if error:
        print(error)
        return 1
    start, regs = result
    print(f"start {start} " + " ".join(f"{k} 0x{v:08x}" for k, v in regs.items()))
    failed = checks(args.expect, regs)
    if args.start is not None and start != args.start:
        failed.append(f"start {args.start}")
    if failed:
        print(f"not {args.expect}: " + ", ".join(failed))
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
