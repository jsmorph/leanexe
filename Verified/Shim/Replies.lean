import LeanExe.Linux.Replies
import Verified.Shim.Memory
import Verified.Wasi.NestedBytes

/-!
The WASI replies that the shim builds from the results of its Linux calls, and the parameters
that its replies depend on.  `errnoOf` maps a Linux error number to a WASI errno by Wasmtime 44's
table.  A reply carries outputs of the sizes that the call's description gives for every errno and
for a trap: the outputs of a successful call, and zeros otherwise.  A result that Linux never
gives for the request traps with `shimTrap`.

`OpenFlags` holds the two open flags whose values differ between arm64 and x86-64, and `Launch`
what the launcher gives the process: its arguments, its environment, and whether descriptor 3 is
a directory that it grants.  `openNumbers I events` gives the descriptor numbers that the shim
holds open after the layer events `events`, and `preopened I events` whether descriptor 3 is still
the preopened directory.  `openCheck` makes Wasmtime 44's checks of `path_open` before any call in
Wasmtime's order, except for a file handle as the directory, and `openHowBytes` gives the
`open_how` record of the `openat2` call, with the access mode and the creation flags that
Wasmtime's `open_at` and cap-std 3.4.5 choose, the shim's own `O_DIRECTORY`, `O_APPEND`, and
`O_NONBLOCK`, and cap-std's resolution flags `RESOLVE_BENEATH` and `RESOLVE_NO_MAGICLINKS`.
-/

namespace Verified.Shim

open LeanExe LeanExe.Wasi Verified.Wasi

/-- The WASI errno of the Linux error number `x`, by Wasmtime 44's table, with `EXDEV` as `perm`,
the errno that cap-std gives an escape, and `io` for every other number.  Wasmtime converts a
stream's error with `from_raw_os_error` of `crates/wasi/src/p2/host/filesystem.rs` and the
conversion of its codes in `crates/wasi/src/p1.rs`, and a descriptor's error with the table of
the same arms in `crates/wasi/src/filesystem.rs`; a number outside the arms falls back to the
error's kind, which gives a code other than `io` only for numbers that the arms name. -/
def errnoOf (x : UInt64) : UInt64 :=
  match x.toNat with
  | 1 => 63 -- EPERM: perm
  | 2 => 44 -- ENOENT: noent
  | 4 => 27 -- EINTR: intr
  | 5 => 29 -- EIO: io
  | 9 => 8 -- EBADF: badf
  | 12 => 48 -- ENOMEM: nomem
  | 13 => 2 -- EACCES: acces
  | 16 => 10 -- EBUSY: busy
  | 17 => 20 -- EEXIST: exist
  | 18 => 63 -- EXDEV: perm
  | 20 => 54 -- ENOTDIR: notdir
  | 21 => 31 -- EISDIR: isdir
  | 22 => 28 -- EINVAL: inval
  | 27 => 22 -- EFBIG: fbig
  | 28 => 51 -- ENOSPC: nospc
  | 29 => 70 -- ESPIPE: spipe
  | 31 => 34 -- EMLINK: mlink
  | 32 => 64 -- EPIPE: pipe
  | 36 => 37 -- ENAMETOOLONG: nametoolong
  | 39 => 55 -- ENOTEMPTY: notempty
  | 40 => 32 -- ELOOP: loop
  | 75 => 61 -- EOVERFLOW: overflow
  | 84 => 25 -- EILSEQ: ilseq
  | 95 => 58 -- EOPNOTSUPP: notsup
  | 114 => 7 -- EALREADY: already
  | 115 => 26 -- EINPROGRESS: inprogress
  | _ => 29

theorem errnoOf_valid (x : UInt64) : (errnoOf x).toNat ≤ 76 ∧ errnoOf x ≠ 0 := by
  unfold errnoOf
  split <;> decide

/-- The message of a trap of the shim: a request that no contract admits, or a Linux result that
Linux never gives for the request. -/
def shimTrap : String := "linux shim"

/-- The message of an exit status of 126 or more, which the shim rejects. -/
def exitRejected : String := "linux shim: exit status 126 or more"

/-- The reply to an `fd_read` of `count` bytes whose `read` returned `ret` with the bytes `output`
in its buffer: the first `ret` bytes when `ret` is at most `count`, the errno of a negated error
number, and a trap of the shim for any other result. -/
def readReply (count ret : UInt64) (output : List UInt8) : Transfer Bytes :=
  if ret.toNat ≤ count.toNat then .returned 0 (bytesOfList (output.take ret.toNat))
  else if Linux.isError ret then .returned (errnoOf (0 - ret)) Bytes.empty
  else .trapped shimTrap Bytes.empty

/-- The reply to an `fd_write` of `count` bytes whose `write` returned `ret`: the count `ret` when
it is at most `count`, the errno of a negated error number, and a trap of the shim for any other
result. -/
def writeReply (count ret : UInt64) : Transfer UInt64 :=
  if ret.toNat ≤ count.toNat then .returned 0 ret
  else if Linux.isError ret then .returned (errnoOf (0 - ret)) 0
  else .trapped shimTrap 0

theorem readReply_valid (count ret : UInt64) (output : List UInt8) :
    (readReply count ret output).committed.data.size ≤ count.toNat ∧
      (readReply count ret output).validErrno := by
  unfold readReply
  split
  · refine ⟨?_, by simp [Transfer.validErrno]⟩
    simp only [Transfer.committed, bytesOfList_size, List.length_take]
    omega
  · split
    · exact ⟨Nat.zero_le _, (errnoOf_valid _).1⟩
    · exact ⟨Nat.zero_le _, trivial⟩

theorem writeReply_valid (size : Nat) (ret : UInt64) :
    (writeReply (UInt64.ofNat size) ret).committed.toNat ≤ size ∧
      (writeReply (UInt64.ofNat size) ret).validErrno := by
  unfold writeReply
  split
  · refine ⟨?_, by simp [Transfer.validErrno]⟩
    simp only [Transfer.committed, UInt64.toNat_ofNat'] at *
    have := Nat.mod_le size (2 ^ 64)
    omega
  · split
    · exact ⟨Nat.zero_le _, (errnoOf_valid _).1⟩
    · exact ⟨Nat.zero_le _, trivial⟩

/-- The values of the open flags that differ between architectures: `O_DIRECTORY` and
`O_NOFOLLOW`. -/
structure OpenFlags where
  directory : UInt64
  nofollow : UInt64

/-- arm64's `O_DIRECTORY` (octal 040000) and `O_NOFOLLOW` (octal 0100000), from
`arch/arm64/include/uapi/asm/fcntl.h` of Linux 7.0. -/
def arm64Flags : OpenFlags := ⟨0x4000, 0x8000⟩

/-- What the launcher gives the process: its arguments and its environment variables, each a byte
string without its terminating zero, and whether descriptor 3 is a directory that it grants. -/
structure Launch where
  args : List (List UInt8)
  environ : List (List UInt8)
  preopen : Bool

/-- `n` zero bytes. -/
def zeros (n : Nat) : Bytes := bytesOfList (List.replicate n 0)

/-- The `n` little-endian bytes of `value`. -/
def leBytes (n value : Nat) : Bytes := bytesOfList ((List.range n).map (byteOf value))

@[simp] theorem zeros_size (n : Nat) : (zeros n).data.size = n := by simp [zeros]

@[simp] theorem leBytes_size (n value : Nat) : (leBytes n value).data.size = n := by
  simp [leBytes]

/-- `n` little-endian bytes, at most eight, of a value below `2^(8 n)` read back as the value. -/
theorem littleEndian_leBytes {n value : Nat} (wide : n ≤ 8) (small : value < 2 ^ (8 * n)) :
    littleEndian (leBytes n value) = UInt64.ofNat value := by
  apply littleEndian_of_bytes (by simpa using wide) (by simpa using small)
  intro index bound
  simp [leBytes, bytesOfList, ByteArray.getElem_eq_getElem_data]

/-! ## Clocks and random bytes -/

/-- The reply to `clock_time_get` of clock 0 or 1 whose `clock_gettime` returned `ret` with the
timespec `output`: the time in nanoseconds when the seconds lie below `2^63` and the time below
`2^64`, errno 61 (`overflow`) for a negative second count or a time of `2^64` or more, the errno
of a negated error number, and a trap of the shim for a nanosecond count of `10^9` or more and for
any other result. -/
def clockReply (ret : UInt64) (output : List UInt8) : Transfer (List Bytes) :=
  let sec := Linux.leValue (output.take 8)
  let nsec := Linux.leValue ((output.drop 8).take 8)
  if ret = 0 then
    if nsec < 10 ^ 9 then
      if sec < 2 ^ 63 ∧ sec * 10 ^ 9 + nsec < 2 ^ 64 then
        .returned 0 [leBytes 8 (sec * 10 ^ 9 + nsec)]
      else .returned 61 [zeros 8]
    else .trapped shimTrap [zeros 8]
  else if Linux.isError ret then .returned (errnoOf (0 - ret)) [zeros 8]
  else .trapped shimTrap [zeros 8]

/-- The reply to `random_get` of `length` bytes whose last `getrandom`, asked for the `remaining`
bytes after the bytes `filled`, returned `ret` with the bytes `output` in its buffer: the filled
bytes and the output when it returned all of them, the errno of a negated error number, and a
trap of the shim for any other result, 0 among them. -/
def randomLast (length remaining : Nat) (filled : List UInt8) (ret : UInt64)
    (output : List UInt8) : Transfer (List Bytes) :=
  if ret.toNat = remaining then .returned 0 [bytesOfList (filled ++ output)]
  else if Linux.isError ret then .returned (errnoOf (0 - ret)) [zeros length]
  else .trapped shimTrap [zeros length]

/-! ## Arguments and environment -/

/-- The bytes that `strings` take with a terminating zero each. -/
def stringsSize (strings : List (List UInt8)) : Nat := (strings.map fun s => s.length + 1).sum

/-- Whether the count and the size of `strings` lie below `2^32`. -/
def stringsFit (strings : List (List UInt8)) : Bool :=
  decide (strings.length < 2 ^ 32 ∧ stringsSize strings < 2 ^ 32)

/-- `strings` one after another, each with its terminating zero. -/
def stringsBytes (strings : List (List UInt8)) : List UInt8 := strings.flatMap (· ++ [0])

/-- The outputs of `args_sizes_get` and `environ_sizes_get`: the count and the size of `strings`,
four little-endian bytes each. -/
def sizesOutputs (strings : List (List UInt8)) : List Bytes :=
  [leBytes 4 strings.length, leBytes 4 (stringsSize strings)]

/-- The reply to `args_sizes_get` or `environ_sizes_get` for `strings`: the count and the size, or
errno 61 (`overflow`) when either reaches `2^32`, as Wasmtime 44 answers. -/
def sizesReply (strings : List (List UInt8)) : Transfer (List Bytes) :=
  if stringsFit strings then .returned 0 (sizesOutputs strings) else .returned 61 [zeros 4, zeros 4]

/-- The reply to `args_get` or `environ_get` for `strings`: the strings with their terminating
zeros, or a trap of the shim when the count or the size reaches `2^32`, since the regions that the
sizes' four bytes give cannot hold them. -/
def stringsReply (strings : List (List UInt8)) : Transfer (List Bytes) :=
  if stringsFit strings then .returned 0 [bytesOfList (stringsBytes strings)]
  else .trapped shimTrap [zeros (littleEndian (leBytes 4 (stringsSize strings))).toNat]

/-! ## Files -/

/-- The bound on the descriptor numbers that the shim holds open: 1,024, Linux's default soft
`RLIMIT_NOFILE`, below which Linux numbers every descriptor of a process that keeps that limit.
The shim traps on an `openat2` that returns a number of the bound or more. -/
def descriptorLimit : Nat := 1024

/-- The descriptor numbers that the shim holds open after the layer events `events`: 3 when the
launcher grants it and each number below `descriptorLimit` that a call that opens a descriptor,
`openat2` for the shim, returned, each until a `close` of the number.  The shim refuses every
other number as a directory or file descriptor. -/
def openNumbers (I : Launch) (events : List Linux.Event) : List UInt64 :=
  (Linux.openAfter (if I.preopen then [3] else []) events).filter (·.toNat < descriptorLimit)

/-- Whether descriptor 3 is still the preopened directory after the layer events `events`: the
launcher granted it and no `close` of 3 is among them. -/
def preopened (I : Launch) (events : List Linux.Event) : Bool :=
  I.preopen && events.all fun e =>
    !(decide (e.call = Linux.closeCall) && Linux.descriptor (Linux.arg e.args 0) == 3)

/-- The errno of the checks that the shim makes of a `path_open` request before any call, in
Wasmtime 44's order, or 0: a path that is not UTF-8 (25, `ilseq`); a directory descriptor outside
`opened`, the numbers that the shim holds open (8, `badf`); the flags `dsync`, `rsync`, or `sync`
(58, `notsup`); `directory` with `creat`, `excl`, or `trunc` (28, `inval`); a zero byte in the path
(28); and a path of 4,096 bytes or more (37, `nametoolong`).  The shim does not know whether an
open number is a file, so for a file handle it makes the later checks and the call, where
Wasmtime answers 54 (`notdir`) first. -/
def openCheck (opened : List UInt64) (dir oflags : UInt64) (path : Bytes) (fdflags : UInt64) :
    UInt64 :=
  if ¬path.data.IsValidUTF8 then 25
  else if dir ∉ opened then 8
  else if fdflags &&& 0x1A ≠ 0 then 58
  else if oflags &&& 2 ≠ 0 ∧ oflags &&& 0xD ≠ 0 then 28
  else if (0 : UInt8) ∈ path.data.data.toList then 28
  else if 4096 ≤ path.data.size then 37
  else 0

/-- The `flags` word of `open_how` for a `path_open` request.  The access mode and the creation
flags are those that Wasmtime 44's `open_at` and cap-std 3.4.5 choose.  The file is written when
the rights hold `fd_write` (64) or `oflags` hold `creat` (1) or `trunc` (8), and read when the
rights hold `fd_read` (2) or lack `fd_write`, which gives `O_RDONLY`, `O_WRONLY`, or `O_RDWR`.
`creat` gives `O_CREAT`, `excl` (4) with `creat` gives `O_EXCL`, and `trunc` gives `O_TRUNC`
except with `creat` and `excl`, which cap-std opens as `create_new` without it.  The shim departs
from Wasmtime in three flags: `directory` (2) gives `O_DIRECTORY`, where Wasmtime tests the kind
after the open, and the `fdflags` `append` (1) and `nonblock` (4) give `O_APPEND` and
`O_NONBLOCK`, which Wasmtime keeps in user space.  A lookup without `symlink_follow` (1) gives
`O_NOFOLLOW`, and every open takes `O_CLOEXEC`.  The values are those of
`include/uapi/asm-generic/fcntl.h`, except `O_DIRECTORY` and `O_NOFOLLOW`, which `F` gives. -/
def openFlagsWord (F : OpenFlags) (dirflags oflags rights fdflags : UInt64) : UInt64 :=
  let creat := oflags &&& 1 != 0
  let excl := creat && oflags &&& 4 != 0
  let write := rights &&& 64 != 0 || creat || oflags &&& 8 != 0
  let read := rights &&& 2 != 0 || rights &&& 64 == 0
  (if read && write then 2 else if write then 1 else 0) |||
    (if creat then 0x40 else 0) ||| (if oflags &&& 2 != 0 then F.directory else 0) |||
    (if excl then 0x80 else 0) ||| (if oflags &&& 8 != 0 && !excl then 0x200 else 0) |||
    (if fdflags &&& 1 != 0 then 0x400 else 0) ||| (if fdflags &&& 4 != 0 then 0x800 else 0) |||
    (if dirflags &&& 1 == 0 then F.nofollow else 0) ||| 0x80000

/-- The 24 bytes of `open_how` for a `path_open` request: the flags, the mode 0666 for `creat` and
0 otherwise, since `openat2` refuses a mode without `O_CREAT`, and the resolution
`RESOLVE_BENEATH | RESOLVE_NO_MAGICLINKS` (10), each as eight little-endian bytes. -/
def openHowBytes (F : OpenFlags) (dirflags oflags rights fdflags : UInt64) : List UInt8 :=
  (List.range 8).map (byteOf (openFlagsWord F dirflags oflags rights fdflags).toNat) ++
    (List.range 8).map (byteOf (if oflags &&& 1 ≠ 0 then 438 else 0)) ++
    (List.range 8).map (byteOf 10)

/-- The reply to `path_open` whose last `openat2` returned `ret`: the descriptor when it lies below
`descriptorLimit`, the errno of a negated error number, and a trap of the shim for any other
result, a descriptor of `descriptorLimit` or more among them. -/
def openReply (ret : UInt64) : Transfer (List Bytes) :=
  if ret.toNat < descriptorLimit then .returned 0 [leBytes 4 ret.toNat]
  else if Linux.isError ret then .returned (errnoOf (0 - ret)) [zeros 4]
  else .trapped shimTrap [zeros 4]

/-- The reply to `fd_close` whose `close` returned `ret`. -/
def closeReply (ret : UInt64) : Transfer (List Bytes) :=
  if ret = 0 then .returned 0 []
  else if Linux.isError ret then .returned (errnoOf (0 - ret)) []
  else .trapped shimTrap []

/-- The reply to `fd_read` on a handle into a buffer of `capacity` bytes whose `read` returned
`ret` with the bytes `output` in the buffer: the whole buffer and the count when `ret` is at most
`capacity`, the errno of a negated error number, and a trap of the shim for any other result. -/
def handleReadReply (capacity ret : UInt64) (output : List UInt8) : Transfer (List Bytes) :=
  if ret.toNat ≤ capacity.toNat then .returned 0 [bytesOfList output, leBytes 4 ret.toNat]
  else if Linux.isError ret then .returned (errnoOf (0 - ret)) [zeros capacity.toNat, zeros 4]
  else .trapped shimTrap [zeros capacity.toNat, zeros 4]

/-- The reply to `fd_write` on a handle of `count` bytes whose `write` returned `ret`. -/
def handleWriteReply (count ret : UInt64) : Transfer (List Bytes) :=
  if ret.toNat ≤ count.toNat then .returned 0 [leBytes 4 ret.toNat]
  else if Linux.isError ret then .returned (errnoOf (0 - ret)) [zeros 4]
  else .trapped shimTrap [zeros 4]

/-- The reply to `fd_prestat_get` of `fd`: a directory whose name has one byte for descriptor 3
while it is the preopened directory, and errno 8 (`badf`) otherwise, as Wasmtime 44 answers. -/
def prestatReply (preopened : Bool) (fd : UInt64) : Transfer (List Bytes) :=
  if fd = 3 ∧ preopened = true then .returned 0 [bytesOfList [0, 0, 0, 0, 1, 0, 0, 0]]
  else .returned 8 [zeros 8]

/-- `reply` is the reply to `fd_prestat_dir_name` of `fd` into a buffer of `capacity` bytes: for
descriptor 3 while it is the preopened directory, the name `.` followed by `capacity - 1` bytes
that the relation leaves free, when the buffer has room, and errno 37 (`nametoolong`) otherwise.
The shim writes only the name, as Wasmtime 44 does, so the free bytes are those that the buffer
held, which the host, seeing no store, cannot fix.  The other replies are errno 54 (`notdir`) for
descriptors 0 to 2 and the other numbers of `opened` and errno 8 (`badf`) for every other number,
as Wasmtime 44 answers for a descriptor that is not open. -/
def DirNameReply (preopened : Bool) (opened : List UInt64) (fd capacity : UInt64)
    (reply : Transfer (List Bytes)) : Prop :=
  if fd = 3 ∧ preopened = true then
    if 1 ≤ capacity.toNat then
      ∃ rest : List UInt8, rest.length = capacity.toNat - 1 ∧
        reply = .returned 0 [bytesOfList (46 :: rest)]
    else reply = .returned 37 [zeros capacity.toNat]
  else if fd.toNat < 3 ∨ fd ∈ opened then reply = .returned 54 [zeros capacity.toNat]
  else reply = .returned 8 [zeros capacity.toNat]

end Verified.Shim
