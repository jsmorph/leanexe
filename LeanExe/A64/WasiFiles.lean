import LeanExe.A64.WasiPreopen
import LeanExe.A64.WasiClocks

/-!
The stubs of `fd_close`, of `fd_read` and `fd_write` on a handle, of `path_open`, and of
`fd_filestat_get`, which follow `closeInvoke`, `handleReadInvoke`, `handleWriteInvoke`,
`openInvoke`, and `filestatInvoke` of `Verified/Shim/Files.lean`.  A stub receives its arguments
in X0 to X8, keeps its return address in X19 across its calls, which it makes through the
runtime's routine `SVC #0; RET` at `svc`, and uses no stack.  It reaches the shim's scratch at
`X17 + scratch` in X20 (`scratchAddr` of `LeanExe/A64/WasiStrings.lean`), where the byte at offset
`16 + d` is 1 while the shim holds descriptor `d` below 1,024 and the byte at offset 8 is 1 while
descriptor 3 is the preopened directory.  A stub writes guest memory only where the
specification's function writes, and the scratch's bytes from offset 8 to 1,039 only where the
shim's descriptors change.

The stub of `fd_close` returns errno 8 (`badf`) for a descriptor that the shim does not hold
(`heldTest`).  Otherwise it calls `close`, clears the descriptor's byte, and clears the preopen
flag when the descriptor is 3, whatever the result, since Linux releases the descriptor before it
reports an error.  A result of 0 returns errno 0, a negated error number its errno through the
routine of errnos at `en` (`errorTail` of `LeanExe/A64/WasiClocks.lean`), and any other result
reaches the trap stub `tr`.

`handleStub nr` is the stub of `fd_read` for `nr` 63 and of `fd_write` for `nr` 64 on a handle.
It reaches `tr` unless the request names one iovec whose eight bytes, whose buffer, and whose
count's four bytes lie within the memory, the size of which the area's first word holds less 8
(`rangeCheck`).  For a descriptor that the shim does not hold it returns errno 8.  Otherwise it
makes the call of `nr` on the descriptor with the buffer at `X17 + 4096 + pointer` and its
length, as the stream stubs make it, and a result at most the length is the count, which it
stores at the count's pointer (`countTail`).

The stub of `path_open` keeps the result's pointer from X8 in X21 and reaches `tr` unless the path
and the result's four bytes lie within the memory.  It then makes the checks of `openCheck` in its
order: a path that is not UTF-8 (`utf8Check`) returns errno 25, a directory that the shim does not
hold errno 8, the `fdflags` `dsync`, `rsync`, or `sync` errno 58, `directory` with `creat`,
`excl`, or `trunc` errno 28, a zero byte in the path errno 28 (`zeroScan`), and a path of 4,096
bytes or more errno 37.  It copies the path and a terminating zero to the scratch's path buffer
at offset 1,080 (`pathCopy`), writes the `open_how` record at offset 1,056 with the flags word of
`openFlagsWord arm64Flags`, the mode 438 for `creat` and 0 otherwise, and the resolution 10
(`openHow`), and calls `openat2` with the directory, the two buffers, and the record's size 24,
again after `EAGAIN` while fewer than four calls were made (`openCalls`).  A result below 1,024
sets the result's byte in the scratch, is stored at the result's pointer, and returns errno 0
(`openResult`).

The stub of `fd_filestat_get` reaches `tr` unless the record's 64 bytes lie within the memory and
returns errno 8 for a descriptor that the shim does not hold.  Otherwise it calls `statx` on the
descriptor with the empty path and `AT_EMPTY_PATH`, which writes the 256-byte `statx` record at
offset 1,088 of the scratch, and converts the record's timestamps to nanoseconds: nanoseconds of
`10^9` or more reach `tr`, and a time of `2^64` nanoseconds or more returns errno 61.  It stores
the WASI `filestat` record's eight words at the guest's pointer and returns errno 0.  An error
result returns its errno, and any other result reaches `tr`.

`utf8Check` follows core's `ByteArray.validateUTF8`: it reads the first byte of each character,
requires one to three continuation bytes from `0x80` to `0xBF` after a first byte from `0xC2` to
`0xF4`, and tests the second byte against the bounds of the overlong forms, the surrogates, and
the code points above `0x10FFFF`, which depend only on the first two bytes.
-/

namespace LeanExe.A64

/-- The guest's address `X17 + 4096 + Xp` in X`d`. -/
def guestAddr (d p : Fin 32) : List Instr := [.addReg d 17 p, .addImm d d 4095, .addImm d d 1]

/-- The four bytes of the low 32 bits of X0 stored at the guest's address in X`p`, through X16 and
X12. -/
def wordStore (p : Fin 32) : List Instr :=
  [.addReg 16 17 p, .addImm 16 16 4] ++ store32 0 12

/-! ## `fd_close` -/

/-- The number of instructions of `closeStub`. -/
def closeStubSize : Nat := 30

/-- The stub of `fd_close` of the descriptor in X0, placed at `a`, with the routine `SVC #0; RET`
at `svc`, the trap stub at `tr`, the routine of errnos at `en`, and the scratch `scratch` bytes
above the area. -/
def closeStub (a svc tr en : UInt64) (scratch : Nat) : GenM (List Instr) := do
  let held ← heldTest (after a 5) (after a 28) 0
  let tail ← errorTail (after a 20) tr en
  return scratchAddr scratch ++ held ++
    [.orrReg 19 31 30, .orrReg 21 31 0, .movz 8 57 0, .bl (← bField (after a 13) svc),
      .addReg 10 20 21, .strb 31 10 16, .subsImm 31 21 3,
      .bcond 1 (← cbField (after a 17) (after a 19)), .strb 31 20 8,
      .cbz 0 (← cbField (after a 19) (after a 26))] ++ tail ++
    [.movz 0 0 0, .ret 19, .movz 0 8 0, .ret 30]

/-! ## `fd_read` and `fd_write` on a handle -/

/-- The handling of the call's result in X0, placed at `a`, with the length in X11, the count's
pointer in X3, the trap stub at `tr`, and the routine of errnos at `en`: a result at most the
length stored at the count's pointer and errno 0 returned to X19, and `errorTail` for every other
result. -/
def countTail (a tr en : UInt64) : GenM (List Instr) := do
  let tail ← errorTail (after a 13) tr en
  return [.subsReg 31 0 11, .bcond 8 (← cbField (after a 1) (after a 13))] ++ wordStore 3 ++
    [.movz 0 0 0, .ret 19] ++ tail

/-- The number of instructions of `handleStub`. -/
def handleStubSize : Nat := 61

/-- The stub of `fd_read` (`nr` 63) or `fd_write` (`nr` 64) of the descriptor in X0 with the iovec
at the pointer in X1, the iovec count in X2, and the count's pointer in X3, placed at `a`, with the
routine `SVC #0; RET` at `svc`, the trap stub at `tr`, the routine of errnos at `en`, and the
scratch `scratch` bytes above the area.  X14 keeps the iovec's eight bytes. -/
def handleStub (nr : Fin 65536) (a svc tr en : UInt64) (scratch : Nat) : GenM (List Instr) := do
  let r1 ← rangeCheck (after a 3) tr
  let r2 ← rangeCheck (after a 12) tr
  let r3 ← rangeCheck (after a 17) tr
  let held ← heldTest (after a 26) (after a 59) 0
  let tail ← countTail (after a 40) tr en
  return [.subsImm 31 2 1, .bcond 1 (← cbField (after a 1) tr), .addImm 12 1 8] ++ r1 ++
    [.addReg 14 17 1, .ldr 14 14 512, .orrW 9 31 14, .lsrImm 12 14 32, .addReg 12 9 12] ++ r2 ++
    [.addImm 12 3 4] ++ r3 ++ scratchAddr scratch ++ held ++
    [.orrW 10 31 14, .lsrImm 11 14 32, .addReg 1 17 10, .addImm 1 1 4095, .addImm 1 1 1,
      .orrReg 2 31 11, .movz 8 nr 0, .orrReg 19 31 30, .bl (← bField (after a 39) svc)] ++ tail ++
    [.movz 0 8 0, .ret 30]

/-! ## `fd_filestat_get` -/

/-- The conversion of the `statx_timestamp` `off` bytes above the scratch's address in X20 to
nanoseconds in X`d`, placed at `a`, with the trap stub at `tr` and the return of errno 61 at
`ov`: the seconds in X9 and the low 32 bits of the next word, the nanoseconds, in X10; `tr` for
nanoseconds above `10^9 − 1`; `ov` for seconds above `⌊(2^64 − 1 − nsec) / 10^9⌋`, the quotient
of `UDIV`, which a time of `2^64` nanoseconds or more and every negative second count exceed; and
otherwise `sec · 10^9 + nsec` in X`d` at `after a 16`, with X11 to X12 changed. -/
def stampConvert (a tr ov : UInt64) (off : Fin 4096) (d : Fin 32) : GenM (List Instr) := do
  return [.ldr 9 20 off, .ldr 10 20 (off + 1), .orrW 10 31 10] ++ movImm 11 999999999 ++
    [.subsReg 31 10 11, .bcond 8 (← cbField (after a 8) tr), .addImm 11 11 1, .subReg 12 31 10,
      .subImm 12 12 1, .udiv 12 12 11, .subsReg 31 9 12, .bcond 8 (← cbField (after a 14) ov),
      .madd d 9 11 10]

/-- The 32 `STR XZR` that clear the 256 bytes of the scratch's `statx` record, 1,088 bytes above
the scratch's address in X20. -/
def statxClear : List Instr := (List.range 32).map fun i => .str 31 20 (Fin.ofNat 4096 (136 + i))

/-- The words of the WASI file types of the 16 values of a mode's bits `S_IFMT`, four bits for
each, as `filetypeOf` of `Verified/Shim/Replies.lean` gives them: 2 for 2, 3 for 4, 1 for 6, 4 for
8, 7 for 10, and 0 for the others. -/
def filetypeTable : UInt64 := 0x0000070401030200

/-- The number of instructions of `filestatStub`. -/
def filestatStubSize : Nat := 147

/-- The stub of `fd_filestat_get` of the descriptor in X0 with the record's pointer in X1, placed at
`a`, with the routine `SVC #0; RET` at `svc`, the trap stub at `tr`, the routine of errnos at `en`,
and the scratch `scratch` bytes above the area.  It reaches `tr` unless the record's 64 bytes lie
within the memory, and returns errno 8 for a descriptor that the shim does not hold.  Otherwise it
keeps the return address in X19 and the record's pointer in X21, writes the empty path, a zero
byte, at the scratch's path buffer, clears the `statx` record (`statxClear`), and calls
`statx(fd, path, AT_EMPTY_PATH, STATX_BASIC_STATS | STATX_BTIME, record)`.  A result other than 0
goes to `errorTail`.  On 0 it converts `stx_atime` to X22 and `stx_mtime` to X23, and `stx_btime`
to X24 when bit `STATX_BTIME` of `stx_mask` is set and 0 otherwise (`stampConvert`); finds the file
type in `filetypeTable` with `LSRV` by four times the bits `S_IFMT` of `stx_mode`, the high half
of its second byte; loads `stx_ino`, `stx_nlink`, and `stx_size` into X25 to X27; and stores the
eight words of `filestat` at the record's guest address: 1, `stx_ino`, the file type, `stx_nlink`,
`stx_size`, and the three times.  The return of errno 61 lies at `after a 137`, the errno tail at
`after a 139`, and the return of errno 8 at `after a 145`. -/
def filestatStub (a svc tr en : UInt64) (scratch : Nat) : GenM (List Instr) := do
  let range ← rangeCheck (after a 1) tr
  let held ← heldTest (after a 10) (after a 145) 0
  let atime ← stampConvert (after a 57) tr (after a 137) 144 22
  let mtime ← stampConvert (after a 73) tr (after a 137) 150 23
  let btime ← stampConvert (after a 94) tr (after a 137) 146 24
  let tail ← errorTail (after a 139) tr en
  return [.addImm 12 1 64] ++ range ++ scratchAddr scratch ++ held ++
    [.orrReg 19 31 30, .orrReg 21 31 1, .strb 31 20 1080] ++ statxClear ++
    [.addImm 1 20 1080, .movz 2 0x1000 0, .movz 3 0xFFF 0, .addImm 4 20 1088, .movz 8 291 0,
      .bl (← bField (after a 55) svc), .cbnz 0 (← cbField (after a 56) (after a 139))] ++ atime ++
    mtime ++
    [.ldr 9 20 136, .movz 10 0x800 0, .andReg 9 9 10, .movz 24 0 0,
      .cbz 9 (← cbField (after a 93) (after a 110))] ++ btime ++
    [.ldrb 10 20 1117, .lsrImm 10 10 4, .addReg 10 10 10, .addReg 10 10 10] ++
    movImm 11 filetypeTable ++
    [.lsrv 11 11 10, .movz 12 0xF 0, .andReg 11 11 12, .ldr 25 20 140, .ldr 26 20 138,
      .orrW 26 31 26, .ldr 27 20 141, .addReg 13 17 21, .movz 9 1 0, .str 9 13 512,
      .str 25 13 513, .str 11 13 514, .str 26 13 515, .str 27 13 516, .str 22 13 517,
      .str 23 13 518, .str 24 13 519, .movz 0 0 0, .ret 19, .movz 0 61 0, .ret 19] ++ tail ++
    [.movz 0 8 0, .ret 30]

/-! ## `path_open` -/

/-- Whether a byte is a continuation byte of UTF-8, from `0x80` to `0xBF`. -/
def contByte (b : UInt8) : Bool := 0x80 ≤ b && b < 0xC0

/-- The decision of `utf8Check` on the bytes `bs`: a first byte below `0x80` stands alone, one from
`0xC2` to `0xDF` takes one continuation byte, one from `0xE0` to `0xEF` two, with a second byte
from `0xA0` after `0xE0` and below `0xA0` after `0xED`, and one from `0xF0` to `0xF4` three, with
a second byte from `0x90` after `0xF0` and below `0x90` after `0xF4`. -/
def utf8Scan : List UInt8 → Bool
  | [] => true
  | w :: rest =>
    if w < 0x80 then utf8Scan rest
    else if w < 0xC2 then false
    else if w < 0xE0 then
      match rest with
      | x :: rest => contByte x && utf8Scan rest
      | [] => false
    else if w < 0xF0 then
      match rest with
      | x :: y :: rest => contByte x && contByte y && (w != 0xE0 || 0xA0 ≤ x) &&
          (w != 0xED || x < 0xA0) && utf8Scan rest
      | _ => false
    else if w < 0xF5 then
      match rest with
      | x :: y :: z :: rest => contByte x && contByte y && contByte z &&
          (w != 0xF0 || 0x90 ≤ x) && (w != 0xF4 || x < 0x90) && utf8Scan rest
      | _ => false
    else false

/-- The check that the `n` bytes from the guest's address `p`, with `p` in X2 and `n` in X3, are
UTF-8, placed at `a`: the next word after it, `after a 74`, when they are, and `bad` otherwise.
X9 walks the bytes, X10 counts the bytes that remain, X11 holds a character's first byte, X12 its
second, and X13 the others. -/
def utf8Check (a bad : UInt64) : GenM (List Instr) := do
  return guestAddr 9 2 ++ [.orrReg 10 31 3,
    .cbz 10 (← cbField (after a 4) (after a 74)), .ldrb 11 9 0,
    .subsImm 31 11 0x80, .bcond 3 (← cbField (after a 7) (after a 71)),
    .subsImm 31 11 0xC2, .bcond 3 (← cbField (after a 9) bad),
    .subsImm 31 11 0xE0, .bcond 2 (← cbField (after a 11) (after a 21)),
    .subsImm 31 10 2, .bcond 3 (← cbField (after a 13) bad),
    .ldrb 12 9 1, .subImm 13 12 0x80, .subsImm 31 13 0x40, .bcond 2 (← cbField (after a 17) bad),
    .addImm 9 9 2, .subImm 10 10 2, .b (← bField (after a 20) (after a 4)),
    .subsImm 31 11 0xF0, .bcond 2 (← cbField (after a 22) (after a 44)),
    .subsImm 31 10 3, .bcond 3 (← cbField (after a 24) bad),
    .ldrb 12 9 1, .subImm 13 12 0x80, .subsImm 31 13 0x40, .bcond 2 (← cbField (after a 28) bad),
    .ldrb 13 9 2, .subImm 13 13 0x80, .subsImm 31 13 0x40, .bcond 2 (← cbField (after a 32) bad),
    .subsImm 31 11 0xE0, .bcond 1 (← cbField (after a 34) (after a 37)),
    .subsImm 31 12 0xA0, .bcond 3 (← cbField (after a 36) bad),
    .subsImm 31 11 0xED, .bcond 1 (← cbField (after a 38) (after a 41)),
    .subsImm 31 12 0xA0, .bcond 2 (← cbField (after a 40) bad),
    .addImm 9 9 3, .subImm 10 10 3, .b (← bField (after a 43) (after a 4)),
    .subsImm 31 11 0xF5, .bcond 2 (← cbField (after a 45) bad),
    .subsImm 31 10 4, .bcond 3 (← cbField (after a 47) bad),
    .ldrb 12 9 1, .subImm 13 12 0x80, .subsImm 31 13 0x40, .bcond 2 (← cbField (after a 51) bad),
    .ldrb 13 9 2, .subImm 13 13 0x80, .subsImm 31 13 0x40, .bcond 2 (← cbField (after a 55) bad),
    .ldrb 13 9 3, .subImm 13 13 0x80, .subsImm 31 13 0x40, .bcond 2 (← cbField (after a 59) bad),
    .subsImm 31 11 0xF0, .bcond 1 (← cbField (after a 61) (after a 64)),
    .subsImm 31 12 0x90, .bcond 3 (← cbField (after a 63) bad),
    .subsImm 31 11 0xF4, .bcond 1 (← cbField (after a 65) (after a 68)),
    .subsImm 31 12 0x90, .bcond 2 (← cbField (after a 67) bad),
    .addImm 9 9 4, .subImm 10 10 4, .b (← bField (after a 70) (after a 4)),
    .addImm 9 9 1, .subImm 10 10 1, .b (← bField (after a 73) (after a 4))]

/-- The check that none of the `n` bytes from the guest's address `p`, with `p` in X2 and `n` in
X3, is zero, placed at `a`: the next word after it, `after a 10`, when none is, and `bad`
otherwise, with X9, X10, and X12 changed. -/
def zeroScan (a bad : UInt64) : GenM (List Instr) := do
  return guestAddr 9 2 ++ [.orrReg 10 31 3,
    .cbz 10 (← cbField (after a 4) (after a 10)), .ldrb 12 9 0,
    .cbz 12 (← cbField (after a 6) bad), .addImm 9 9 1, .subImm 10 10 1,
    .b (← bField (after a 9) (after a 4))]

/-- The copy of the `n` bytes from the guest's address `p`, with `p` in X2 and `n` in X3, and a
terminating zero to the scratch's path buffer, 1,080 bytes above the scratch's address in X20,
placed at `a`, with X9, X10, X12, and X13 changed. -/
def pathCopy (a : UInt64) : GenM (List Instr) := do
  return guestAddr 9 2 ++ [.addImm 10 20 1080, .orrReg 12 31 3,
    .cbz 12 (← cbField (after a 5) (after a 12)), .ldrb 13 9 0, .strb 13 10 0, .addImm 9 9 1,
    .addImm 10 10 1, .subImm 12 12 1, .b (← bField (after a 11) (after a 5)), .strb 31 10 0]

/-- The `open_how` record of a `path_open` request with the `dirflags` in X1, the `oflags` in X4,
the rights in X5, and the `fdflags` in X7, written 1,056 bytes above the scratch's address in X20,
placed at `a`: the flags word of `openFlagsWord arm64Flags`, computed in X24 from `O_CLOEXEC` with
`creat` in X25, `excl` in X26, `trunc` in X27, and the write access in X28, then the mode 438 for
`creat` and 0 otherwise, and the resolution 10, with X9 and X10 changed. -/
def openHow (a : UInt64) : GenM (List Instr) := do
  return [.movz 24 8 1,
    .movz 9 1 0, .andReg 25 4 9, .movz 9 8 0, .andReg 27 4 9,
    .movz 9 64 0, .andReg 28 5 9, .orrReg 28 28 25, .orrReg 28 28 27,
    .cbz 28 (← cbField (after a 9) (after a 19)),
    .movz 9 1 0, .movz 10 2 0, .andReg 10 5 10, .cbnz 10 (← cbField (after a 13) (after a 17)),
    .movz 10 64 0, .andReg 10 5 10, .cbnz 10 (← cbField (after a 16) (after a 18)),
    .movz 9 2 0, .orrReg 24 24 9,
    .cbz 25 (← cbField (after a 19) (after a 22)), .movz 9 0x40 0, .orrReg 24 24 9,
    .movz 9 2 0, .andReg 9 4 9, .cbz 9 (← cbField (after a 24) (after a 27)),
    .movz 9 0x4000 0, .orrReg 24 24 9,
    .movz 9 4 0, .andReg 26 4 9, .cbnz 25 (← cbField (after a 29) (after a 31)), .movz 26 0 0,
    .cbz 26 (← cbField (after a 31) (after a 34)), .movz 9 0x80 0, .orrReg 24 24 9,
    .cbz 27 (← cbField (after a 34) (after a 38)), .cbnz 26 (← cbField (after a 35) (after a 38)),
    .movz 9 0x200 0, .orrReg 24 24 9,
    .movz 9 1 0, .andReg 9 7 9, .cbz 9 (← cbField (after a 40) (after a 43)),
    .movz 9 0x400 0, .orrReg 24 24 9,
    .movz 9 4 0, .andReg 9 7 9, .cbz 9 (← cbField (after a 45) (after a 48)),
    .movz 9 0x800 0, .orrReg 24 24 9,
    .movz 9 1 0, .andReg 9 1 9, .cbnz 9 (← cbField (after a 50) (after a 53)),
    .movz 9 0x8000 0, .orrReg 24 24 9,
    .str 24 20 132, .movz 9 0 0, .cbz 25 (← cbField (after a 55) (after a 57)), .movz 9 438 0,
    .str 9 20 133, .movz 9 10 0, .str 9 20 134]

/-- The `openat2` calls of `path_open` under the directory in X0, placed at `a`, with the routine
`SVC #0; RET` at `svc`: X22 keeps the directory and X23 counts the calls before the last, and a
call that returns `-EAGAIN` is made again while fewer than four calls were made.  The last call's
result is in X0 at `after a 14`. -/
def openCalls (a svc : UInt64) : GenM (List Instr) := do
  return [.orrReg 22 31 0, .movz 23 0 0,
    .orrReg 0 31 22, .addImm 1 20 1080, .addImm 2 20 1056, .movz 3 24 0, .movz 8 437 0,
    .bl (← bField (after a 7) svc), .addImm 9 0 11, .cbnz 9 (← cbField (after a 9) (after a 14)),
    .subsImm 31 23 2, .bcond 8 (← cbField (after a 11) (after a 14)), .addImm 23 23 1,
    .b (← bField (after a 13) (after a 2))]

/-- The handling of the last `openat2`'s result in X0, placed at `a`, with the result's pointer in
X21, the scratch's address in X20, the trap stub at `tr`, and the routine of errnos at `en`: a
descriptor below 1,024 sets its byte in the scratch, is stored at the result's pointer, and
returns errno 0 to X19, and `errorTail` handles every other result. -/
def openResult (a tr en : UInt64) : GenM (List Instr) := do
  let tail ← errorTail (after a 16) tr en
  return [.subsImm 31 0 1023, .bcond 8 (← cbField (after a 1) (after a 16)), .addReg 10 20 0,
    .movz 9 1 0, .strb 9 10 16] ++ wordStore 21 ++ [.movz 0 0 0, .ret 19] ++ tail

/-- The number of instructions of `openStub`. -/
def openStubSize : Nat := 236

/-- The stub of `path_open` of the directory in X0 with the `dirflags` in X1, the path's pointer
and length in X2 and X3, the `oflags` in X4, the rights in X5, the inherited rights in X6, the
`fdflags` in X7, and the result's pointer in X8, placed at `a`, with the routine `SVC #0; RET` at
`svc`, the trap stub at `tr`, the routine of errnos at `en`, and the scratch `scratch` bytes above
the area.  The errnos of the checks lie at `after a 226` (25), `after a 228` (8), `after a 230`
(58), `after a 232` (28), and `after a 234` (37). -/
def openStub (a svc tr en : UInt64) (scratch : Nat) : GenM (List Instr) := do
  let r1 ← rangeCheck (after a 8) tr
  let r2 ← rangeCheck (after a 13) tr
  let utf8 ← utf8Check (after a 17) (after a 226)
  let held ← heldTest (after a 91) (after a 228) 0
  let zero ← zeroScan (after a 105) (after a 232)
  let copy ← pathCopy (after a 117)
  let how ← openHow (after a 130)
  let calls ← openCalls (after a 190) svc
  let result ← openResult (after a 204) tr en
  return [.orrReg 21 31 8, .orrReg 19 31 30] ++ scratchAddr scratch ++ [.addReg 12 2 3] ++ r1 ++
    [.addImm 12 21 4] ++ r2 ++ utf8 ++ held ++
    [.movz 9 0x1A 0, .andReg 9 7 9, .cbnz 9 (← cbField (after a 98) (after a 230)),
      .movz 9 2 0, .andReg 9 4 9, .cbz 9 (← cbField (after a 101) (after a 105)),
      .movz 9 0xD 0, .andReg 9 4 9, .cbnz 9 (← cbField (after a 104) (after a 232))] ++ zero ++
    [.subsImm 31 3 4095, .bcond 8 (← cbField (after a 116) (after a 234))] ++ copy ++ how ++
    calls ++ result ++
    [.movz 0 25 0, .ret 30, .movz 0 8 0, .ret 30, .movz 0 58 0, .ret 30, .movz 0 28 0, .ret 30,
      .movz 0 37 0, .ret 30]

end LeanExe.A64
