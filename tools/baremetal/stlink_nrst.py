# /// script
# requires-python = ">=3.12"
# dependencies = ["pyusb==1.3.1"]
# ///
"""Resets the NUCLEO-F767ZI through its NRST pin after setting the debug registers that a system
reset keeps to their power-on values, so that the core starts with no debugger attached.

The script talks to the board's ST-LINK/V2-1, USB 0483:374b with firmware V2J39M27, through
libusb with the commands of stlink 1.8.0 (src/stlink-lib/usb.c and commands.h): each command is
16 bytes on endpoint 0x01, and its reply arrives on endpoint 0x81, where the first byte of a
debug command's reply is 0x80 on success.  It claims interface 0, the debug interface, and leaves
the virtual COM port's interfaces alone.  It reads the version and requires V2J39M27, the
firmware with which the procedure was tested, and enters SWD mode at 1.8 MHz as stlink does,
unless the ST-LINK is in debug mode already.  It requires the Cortex-M7's SW-DP, IDCODE
0x5BA02477, and DBGMCU_IDCODE's DEV_ID 0x451 of the STM32F76x and STM32F77x.

It then reads DHCSR, DEMCR, DFSR, FP_CTRL, DBGMCU_CR, DBGMCU_APB1_FZ, and DBGMCU_APB2_FZ and
writes DEMCR with TRCENA alone, since DDI 0403E.e section C1.6.5 makes DWT and ITM reads UNKNOWN
and writes IMPLEMENTATION DEFINED while TRCENA is 0 and tells software to clear the DWT's and the
ITM's enables before TRCENA.  With TRCENA set it reads DWT_CTRL and ITM_TCR, writes 0 to DWT_CTRL,
and writes 0 to ITM_TCR if it reads nonzero, and reads both back.  It writes 0 to DEMCR,
0x00000002 to FP_CTRL, its KEY with ENABLE clear, 0 to DBGMCU_CR, DBGMCU_APB1_FZ, and
DBGMCU_APB2_FZ, and 0xA05F0000 to DHCSR, the key with C_DEBUGEN, C_HALT, C_STEP, C_MASKINTS, and
C_SNAPSTALL clear.  It reads every register back and requires those values: DEMCR and the
DBGMCU registers 0, FP_CTRL.ENABLE 0, the writable fields of DWT_CTRL 0, ITM_TCR 0, and DHCSR's
control bits 0.  It then sends DEBUG_EXIT, drives NRST low, waits 100 us, as stlink_reset does,
and drives NRST high.  SB111, ON by default, connects the board's NRST to the ST-LINK's T_NRST
(UM1974 Rev 7, Table 12), and the script reads and writes no target register after DEBUG_EXIT.
A failed check ends the script after DEBUG_EXIT without the pulse.

RM0410 section 44.10 states that DHCSR and DEMCR are reset only by a power-on reset, and
sections 44.16.4 and 44.16.5 that DBGMCU_CR and DBGMCU_APB1_FZ are not reset by a system reset,
so the values that the script writes persist through the NRST reset.  DFSR keeps its status bits,
since the script does not write it, and the comparators of the FPB and the DWT keep their values,
which act only while FP_CTRL.ENABLE or, for the DWT's, DEMCR.TRCENA is set.

With --dry-run the script prints the commands and opens no device.  It prints each command with
its bytes and each value that it reads, then one line, a summary or the cause of the failure, and exits with
status 0 or 1.

Usage: uv run tools/baremetal/stlink_nrst.py [--dry-run]
"""

import argparse
import sys
import time

import usb.core
import usb.util

VID, PID = 0x0483, 0x374B
EP_OUT, EP_IN = 0x01, 0x81
TIMEOUT_MS = 3000
FIRMWARE = (2, 39, 27)
SWD_IDCODE = 0x5BA02477
DEV_ID = 0x451

OK = 0x80
WAITS = (0x10, 0x14)

DHCSR = 0xE000EDF0
DEMCR = 0xE000EDFC
DFSR = 0xE000ED30
FP_CTRL = 0xE0002000
DWT_CTRL = 0xE0001000
ITM_TCR = 0xE0000E80
DBGMCU_IDCODE = 0xE0042000
DBGMCU_CR = 0xE0042004
DBGMCU_APB1_FZ = 0xE0042008
DBGMCU_APB2_FZ = 0xE004200C

NAMES = {
    DHCSR: "DHCSR", DEMCR: "DEMCR", DFSR: "DFSR", FP_CTRL: "FP_CTRL", DWT_CTRL: "DWT_CTRL",
    ITM_TCR: "ITM_TCR", DBGMCU_IDCODE: "DBGMCU_IDCODE", DBGMCU_CR: "DBGMCU_CR",
    DBGMCU_APB1_FZ: "DBGMCU_APB1_FZ", DBGMCU_APB2_FZ: "DBGMCU_APB2_FZ",
}

DBGKEY = 0xA05F0000
TRCENA = 0x01000000
FP_KEY = 0x00000002
DHCSR_CONTROL = 0x0000002F
DWT_CTRL_WRITABLE = 0x007F1FFF

MODES = {0: "DFU", 1: "mass storage", 2: "debug", 3: "SWIM", 4: "bootloader"}


class Failure(Exception):
    pass


def hexbytes(b):
    return " ".join(f"{x:02x}" for x in b)


def le32(v):
    return v.to_bytes(4, "little")


class Probe:
    """The ST-LINK's debug interface, or with dry set a printer of the commands."""

    def __init__(self, dry):
        self.dry = dry
        self.dev = None
        if dry:
            return
        devs = list(usb.core.find(find_all=True, idVendor=VID, idProduct=PID))
        if len(devs) != 1:
            raise Failure(f"{len(devs)} ST-LINK/V2-1 devices {VID:04x}:{PID:04x}, not 1")
        dev = devs[0]
        print(f"ST-LINK/V2-1 on bus {dev.bus:03d} device {dev.address:03d}")
        if dev.is_kernel_driver_active(0):
            dev.detach_kernel_driver(0)
        cfg = dev.get_active_configuration()
        if cfg.bConfigurationValue != 1:
            raise Failure(f"the device is in configuration {cfg.bConfigurationValue}, not 1")
        usb.util.claim_interface(dev, 0)
        self.dev = dev

    def close(self):
        if self.dev is not None:
            usb.util.release_interface(self.dev, 0)
            usb.util.dispose_resources(self.dev)
            self.dev = None

    def xfer(self, cmd, n):
        """Sends the command bytes cmd, padded to 16, and returns the n bytes of the reply."""
        buf = bytes(cmd) + bytes(16 - len(cmd))
        self.dev.write(EP_OUT, buf, TIMEOUT_MS)
        if n == 0:
            return b""
        reply = bytes(self.dev.read(EP_IN, n, TIMEOUT_MS))
        if len(reply) != n:
            raise Failure(f"{hexbytes(cmd)}: a reply of {len(reply)} bytes, not {n}")
        return reply

    def command(self, label, cmd, n, retry=True):
        """A debug command whose reply starts with a status byte, retried after a wait status
        three times with delays of 1, 2, and 4 ms, as stlink's CMD_CHECK_RETRY does."""
        print(f"{label}: {hexbytes(cmd)}")
        if self.dry:
            return None
        for attempt in range(4):
            reply = self.xfer(cmd, n)
            if reply[0] == OK:
                return reply
            if not (retry and reply[0] in WAITS and attempt < 3):
                break
            time.sleep((1 << attempt) / 1000)
        raise Failure(f"{label}: {hexbytes(cmd)}: status 0x{reply[0]:02x}")

    def version(self):
        cmd = [0xF1]
        if self.dry:
            print(f"GET_VERSION: {hexbytes(cmd)}")
            return
        r = self.xfer(cmd, 6)
        v = int.from_bytes(r[0:2], "big")
        ver = (v >> 12, (v >> 6) & 0x3F, v & 0x3F)
        vid, pid = int.from_bytes(r[2:4], "little"), int.from_bytes(r[4:6], "little")
        name = f"V{ver[0]}J{ver[1]}M{ver[2]}"
        print(f"GET_VERSION: {hexbytes(cmd)}: {name}, {vid:04x}:{pid:04x}")
        if ver != FIRMWARE or (vid, pid) != (VID, PID):
            raise Failure(f"firmware {name} {vid:04x}:{pid:04x}; the procedure was tested with "
                          f"V2J39M27 {VID:04x}:{PID:04x} only")

    def mode(self):
        cmd = [0xF5]
        if self.dry:
            print(f"GET_CURRENT_MODE: {hexbytes(cmd)}")
            return 1
        m = self.xfer(cmd, 2)[0]
        print(f"GET_CURRENT_MODE: {hexbytes(cmd)}: {MODES.get(m, 'unknown')} ({m})")
        if m not in (1, 2):
            raise Failure(f"the ST-LINK is in mode {m}, not mass storage or debug")
        return m

    def read(self, addr):
        r = self.command(f"READDEBUGREG {NAMES[addr]}", [0xF2, 0x36, *le32(addr)], 8)
        if r is None:
            return None
        v = int.from_bytes(r[4:8], "little")
        print(f"  {NAMES[addr]} 0x{v:08x}")
        return v

    def write(self, addr, v):
        self.command(f"WRITEDEBUGREG {NAMES[addr]} 0x{v:08x}", [0xF2, 0x35, *le32(addr), *le32(v)],
                     2)

    def exit_debug(self):
        cmd = [0xF2, 0x21]
        print(f"DEBUG_EXIT: {hexbytes(cmd)}")
        if not self.dry:
            self.xfer(cmd, 0)


def check(name, v, ok, want):
    if v is not None and not ok:
        raise Failure(f"{name} reads 0x{v:08x}, not {want}")


def clear(p):
    """Sets the debug registers and reads them back; raises Failure on a wrong value."""
    m = p.mode()
    p.command("SWD_SET_FREQ 1.8 MHz", [0xF2, 0x43, 0x01, 0x00], 2)
    if m != 2:
        p.command("ENTER_SWD", [0xF2, 0x30, 0xA3], 2)
    r = p.command("READ_IDCODES", [0xF2, 0x31], 12, retry=False)
    if r is not None:
        idcode = int.from_bytes(r[4:8], "little")
        print(f"  IDCODE 0x{idcode:08x}")
        check("the SW-DP's IDCODE", idcode, idcode == SWD_IDCODE, f"0x{SWD_IDCODE:08x}")
    v = p.read(DBGMCU_IDCODE)
    check("DBGMCU_IDCODE", v, v is None or v & 0xFFF == DEV_ID, f"DEV_ID 0x{DEV_ID:03x}")
    for a in (DHCSR, DEMCR, DFSR, FP_CTRL, DBGMCU_CR, DBGMCU_APB1_FZ, DBGMCU_APB2_FZ):
        p.read(a)
    p.write(DEMCR, TRCENA)
    p.read(DWT_CTRL)
    itm = p.read(ITM_TCR)
    p.write(DWT_CTRL, 0)
    if itm is None:
        print("WRITEDEBUGREG ITM_TCR 0x00000000 if ITM_TCR reads nonzero")
    elif itm != 0:
        p.write(ITM_TCR, 0)
    v = p.read(DWT_CTRL)
    check("DWT_CTRL", v, v is None or v & DWT_CTRL_WRITABLE == 0, "0 in its writable fields")
    v = p.read(ITM_TCR)
    check("ITM_TCR", v, v == 0, "0")
    p.write(DEMCR, 0)
    p.write(FP_CTRL, FP_KEY)
    for a in (DBGMCU_CR, DBGMCU_APB1_FZ, DBGMCU_APB2_FZ):
        p.write(a, 0)
    p.write(DHCSR, DBGKEY)
    for a in (DEMCR, DBGMCU_CR, DBGMCU_APB1_FZ, DBGMCU_APB2_FZ):
        v = p.read(a)
        check(NAMES[a], v, v == 0, "0")
    v = p.read(FP_CTRL)
    check("FP_CTRL", v, v is None or v & 1 == 0, "ENABLE 0")
    v = p.read(DHCSR)
    check("DHCSR", v, v is None or v & DHCSR_CONTROL == 0, "0 in its control bits")


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--dry-run", action="store_true", help="print the commands only")
    args = parser.parse_args()
    p = None
    try:
        p = Probe(args.dry_run)
        p.version()
        try:
            clear(p)
        finally:
            p.exit_debug()
        p.command("DRIVE_NRST low", [0xF2, 0x3C, 0x00], 2)
        time.sleep(100e-6)
        p.command("DRIVE_NRST high", [0xF2, 0x3C, 0x01], 2)
    except (Failure, usb.core.USBError) as e:
        print(f"fail: {e}")
        return 1
    finally:
        if p is not None:
            p.close()
    print("pass: the debug registers hold their power-on values, and NRST was pulsed"
          if not args.dry_run else "pass: the commands of the procedure")
    return 0


if __name__ == "__main__":
    sys.exit(main())
