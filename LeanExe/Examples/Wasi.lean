import LeanExe.Wasi
import LeanExe.Runtime

namespace LeanExe.Examples.Wasi

open LeanExe.Wasi

def echo : Action UInt32 := do
  let result ← fd_read 0 4096
  match result with
  | .error e => return e
  | .ok bytes =>
    let written ← fd_write 1 bytes
    match written with
    | .error e => return e
    | .ok n => return if n.toNat == bytes.size then 0 else 99

def ordered : Action UInt32 := do
  let action := fd_write 1 "A".toUTF8
  let _ ← action
  let _ ← fd_write 1 "B".toUTF8
  let _ ← action
  return 0

def clock : Action UInt32 := do
  let .ok r ← clock_res_get Clock.monotonic | return 96
  let .ok a ← clock_time_get Clock.monotonic 0 | return 97
  let .ok b ← clock_time_get Clock.monotonic 0 | return 98
  return if r > 0 && b >= a then 0 else 99

def arguments : Action UInt32 := do
  let .ok sizes ← args_sizes_get | return 96
  let .ok args ← args_get | return 98
  if args.size != sizes.1.toNat then return 97
  for arg in args do
    let _ ← fd_write 1 arg
    let _ ← fd_write 1 (ByteArray.mk #[0])
  return 0

def environment : Action UInt32 := do
  let .ok sizes ← environ_sizes_get | return 96
  let .ok vars ← environ_get | return 98
  if vars.size != sizes.1.toNat then return 97
  for value in vars do
    let _ ← fd_write 1 value
    let _ ← fd_write 1 (ByteArray.mk #[0])
  return 0

def random : Action UInt32 := do
  let result ← random_get 64
  match result with
  | .error e => return e
  | .ok bytes =>
    let result ← fd_write 1 bytes
    match result with
    | .error e => return e
    | .ok n => return if n == 64 then 0 else 99

def timer : Action UInt32 := do
  let .ok start ← clock_time_get Clock.monotonic 0 | return 95
  let result ← poll_oneoff #[Subscription.clock 0x100000000000007b Clock.monotonic 20000000 0 0]
  let .ok stop ← clock_time_get Clock.monotonic 0 | return 96
  if stop - start < 20000000 then return 99
  match result with
  | .error e => return e
  | .ok events =>
    if events.size != 1 then return 97
    let event := events[0]!
    return if event.userdata == 0x100000000000007b && event.error == 0 && event.eventType == 0 then 0 else 98

def absoluteTimer : Action UInt32 := do
  let .ok now ← clock_time_get Clock.monotonic 0 | return 1
  let deadline := now + 1000000
  let .ok events ← poll_oneoff #[Subscription.clock 123 Clock.monotonic deadline 0
    Subclockflags.subscription_clock_abstime] | return 2
  let .ok after ← clock_time_get Clock.monotonic 0 | return 3
  return if after >= deadline && events.size == 1 && events[0]!.error == 0 then 0 else 4

def ready : Action UInt32 := do
  let result ← poll_oneoff #[Subscription.read 456 0]
  match result with
  | .error e => return e
  | .ok events =>
    if events.size != 1 then return 97
    let event := events[0]!
    return if event.userdata == 456 && event.error == 0 && event.eventType == 1 then 0 else 98

def invalidPoll : Action UInt32 := do
  let result ← poll_oneoff #[]
  match result with
  | .error e => return e
  | .ok _ => return 99

def exit : Action UInt32 := do
  proc_exit 17
  let _ ← fd_write 1 "unreachable".toUTF8
  return 99

def errors : Action UInt32 := do
  if (← fd_close 4294967295) != Errno.badf then return 1
  if (← fd_sync 4294967295) != Errno.badf then return 2
  if (← fd_datasync 4294967295) != Errno.badf then return 3
  match ← fd_read 4294967295 128 with
  | .ok _ => return 4
  | .error e => if e != Errno.badf then return 5
  match ← fd_write 4294967295 "x".toUTF8 with
  | .ok _ => return 6
  | .error e => if e != Errno.badf then return 7
  match ← clock_res_get Clock.process_cputime_id with
  | .ok _ => return 8
  | .error e => if e != Errno.badf then return 9
  return ← sched_yield

def filesystem : Action UInt32 := do
  let .ok pre ← fd_prestat_get 3 | return 1
  let .ok name ← fd_prestat_dir_name 3 | return 2
  if pre.tag != 0 || pre.nameLength.toNat != name.size || name != "test".toUTF8 then return 3
  let rights := Rights.fd_read ||| Rights.fd_write ||| Rights.fd_seek ||| Rights.fd_tell |||
    Rights.fd_filestat_get ||| Rights.fd_filestat_set_size ||| Rights.fd_filestat_set_times |||
    Rights.fd_sync ||| Rights.fd_datasync ||| Rights.fd_advise ||| Rights.fd_allocate |||
    Rights.fd_fdstat_set_flags
  if (← path_create_directory 3 "dir".toUTF8) != 0 then return 4
  let .ok fd ← path_open 3 0 "dir/file".toUTF8 (Oflags.creat ||| Oflags.excl) rights 0 0 | return 5
  let .ok written ← fd_write fd "abcdef".toUTF8 | return 6
  if written != 6 then return 7
  let .ok position ← fd_tell fd | return 8
  if position != 6 then return 9
  let .ok changed ← fd_pwrite fd "XY".toUTF8 2 | return 10
  if changed != 2 then return 11
  let .ok bytes ← fd_pread fd 20 0 | return 12
  if bytes != "abXYef".toUTF8 then return 13
  let .ok oldPosition ← fd_tell fd | return 14
  if oldPosition != 6 then return 15
  let .ok sought ← fd_seek fd (0 - 2) Whence.cur | return 16
  if sought != 4 then return 17
  let .ok tail ← fd_read fd 20 | return 18
  if tail != "ef".toUTF8 then return 19
  let .ok stat ← fd_fdstat_get fd | return 20
  if stat.filetype != Filetype.regular_file || stat.flags != 0 then return 21
  if (← fd_fdstat_set_flags fd Fdflags.append) != 0 then return 22
  if (← fd_fdstat_set_flags fd 0) != 0 then return 23
  if (← fd_advise fd 0 6 Advice.normal) != 0 then return 24
  let allocated ← fd_allocate fd 0 10
  if allocated != 0 && allocated != Errno.notsup then return 25
  if (← fd_filestat_set_size fd 4) != 0 then return 26
  if (← fd_filestat_set_times fd 1000000000 2000000000 (Fstflags.atim ||| Fstflags.mtim)) != 0 then return 27
  let .ok info ← fd_filestat_get fd | return 28
  if info.size != 4 || info.filetype != Filetype.regular_file || info.nlink != 1 ||
      info.atim != 1000000000 || info.mtim != 2000000000 then return 29
  if (← fd_datasync fd) != 0 then return 30
  if (← fd_sync fd) != 0 then return 31
  let reduced ← fd_fdstat_set_rights fd Rights.fd_read 0
  if reduced == 0 then
    match ← fd_write fd "x".toUTF8 with
    | .ok _ => return 33
    | .error e => if e != Errno.notcapable && e != Errno.badf then return 34
  else if reduced != Errno.badf && reduced != Errno.notsup then return 32
  if (← fd_close fd) != 0 then return 35
  if (← path_link 3 0 "dir/file".toUTF8 3 "hard".toUTF8) != 0 then return 36
  let .ok linked ← path_filestat_get 3 0 "hard".toUTF8 | return 37
  if linked.nlink != 2 || linked.inode != info.inode || linked.device != info.device then return 38
  if (← path_rename 3 "hard".toUTF8 3 "renamed".toUTF8) != 0 then return 39
  if (← path_symlink "dir/file".toUTF8 3 "sym".toUTF8) != 0 then return 40
  let .ok target ← path_readlink 3 "sym".toUTF8 128 | return 41
  if target != "dir/file".toUTF8 then return 42
  let .ok truncated ← path_readlink 3 "sym".toUTF8 3 | return 43
  if truncated != "dir".toUTF8 then return 44
  if (← path_filestat_set_times 3 0 "dir/file".toUTF8 3000000000 4000000000
      (Fstflags.atim ||| Fstflags.mtim)) != 0 then return 45
  let .ok timed ← path_filestat_get 3 Lookupflags.symlink_follow "sym".toUTF8 | return 46
  if timed.atim != 3000000000 || timed.mtim != 4000000000 then return 47
  let .ok listing ← fd_readdir 3 4096 0 | return 48
  if listing.size < 24 then return 49
  let .ok partialListing ← fd_readdir 3 1 0 | return 50
  if partialListing.size != 1 then return 51
  if (← path_unlink_file 3 "sym".toUTF8) != 0 then return 52
  if (← path_unlink_file 3 "renamed".toUTF8) != 0 then return 53
  if (← path_unlink_file 3 "dir/file".toUTF8) != 0 then return 54
  if (← path_remove_directory 3 "dir".toUTF8) != 0 then return 55
  return 0

def renumber : Action UInt32 := do
  let .ok fd ← path_open 3 0 "file".toUTF8 Oflags.creat Rights.fd_write 0 0 | return 1
  if (← fd_renumber fd 1) != 0 then return 2
  let .ok n ← fd_write 1 "renumbered".toUTF8 | return 3
  if n != 10 then return 4
  return ← fd_close 1

def zeroRead : Action UInt32 := do
  match ← fd_read 0 0 with
  | .error e => return e
  | .ok bytes => return if bytes.size == 0 then 0 else 99

def empty : Action UInt32 := do
  let .ok n ← fd_write 1 (ByteArray.mk #[]) | return 3
  if n != 0 then return 4
  let .ok random ← random_get 0 | return 5
  return if random.size == 0 then 0 else 6

def released : Action UInt32 := do
  let before := LeanExe.Runtime.allocCount - LeanExe.Runtime.freeCount
  for _ in [:100] do
    let _ ← random_get 32
    let _ ← fd_read 4294967295 32
    let _ ← args_get
    let _ ← environ_get
    let _ ← poll_oneoff #[Subscription.clock 1 Clock.monotonic 0 0 0]
  let after := LeanExe.Runtime.allocCount - LeanExe.Runtime.freeCount
  return if before == after then 0 else 99

def firstArgument : Action (Except UInt32 ByteArray) := do
  let .ok args ← args_get | return .error 1
  if args.size == 0 then return .error 2
  return .ok args[0]!

def localChild : ByteArray :=
  let bytes := ByteArray.mk #[107, 101, 101, 112]
  let values := #[bytes, bytes]
  values[0]!

def localRetained : Action UInt32 := do
  let bytes := localChild
  let _ ← random_get 4096
  let .ok n ← fd_write 1 bytes | return 1
  return if n == 4 then 0 else 2

def argumentPair : Action (Except UInt32 (ByteArray × ByteArray)) := do
  let .ok args ← args_get | return .error 1
  if args.size == 0 then return .error 2
  let first := args[0]!
  let last := if args.size > 1 then args[args.size - 1]! else first
  return .ok (first, last)

def retainedPair : Action UInt32 := do
  let .ok (first, last) ← argumentPair | return 1
  let _ ← random_get 4096
  let .ok _ ← fd_write 1 first | return 2
  let .ok _ ← fd_write 1 last | return 3
  return 0

def consumeArguments : Action UInt32 := do
  let .ok first ← firstArgument | return 1
  let .ok (left, right) ← argumentPair | return 2
  let localBytes := localChild
  return if first.size == 4 && left.size == 4 && right.size == 4 && localBytes.size == 4 then 0 else 3

def retainedReleased : Action UInt32 := do
  let beforeAlloc := LeanExe.Runtime.allocCount
  let beforeFree := LeanExe.Runtime.freeCount
  for _ in [:100] do
    if (← consumeArguments) != 0 then return 1
  let allocs := LeanExe.Runtime.allocCount - beforeAlloc
  let frees := LeanExe.Runtime.freeCount - beforeFree
  return if allocs == frees then 0 else 2

def retained : Action UInt32 := do
  let .ok first ← firstArgument | return 1
  let .ok second ← fd_read 0 4 | return 2
  for _ in [:10] do
    let _ ← args_get
    let _ ← random_get 4096
  let .ok a ← fd_write 1 first | return 3
  let .ok b ← fd_write 1 second | return 4
  let .ok c ← fd_write 1 first | return 5
  return if a.toNat == first.size && b.toNat == second.size && c == a then 0 else 6

def streaming : Action UInt32 := do
  for _ in [:65536] do
    let .ok bytes ← fd_read 0 4096 | return 1
    if bytes.size == 0 then return 0
    let .ok n ← fd_write 1 bytes | return 2
    if n.toNat != bytes.size then return 3
  return 4

def pollBadFd : Action UInt32 := do
  match ← poll_oneoff #[Subscription.read 765 4294967295] with
  | .error e => return e
  | .ok events =>
    if events.size != 1 then return 2
    let event := events[0]!
    return if event.userdata == 765 && event.error == Errno.badf && event.eventType == 1 then 0 else 3

def invalidPollTag : Action UInt32 := do
  match ← poll_oneoff #[⟨0, 256, 0, 0, 0, 0⟩] with
  | .ok _ => return 4
  | .error e => return if e == Errno.inval then 0 else 5

def socket : Action UInt32 := do
  let .ok _ ← fd_write 2 "ready\n".toUTF8 | return 8
  let .ok _ ← poll_oneoff #[Subscription.read 1 3] | return 9
  let .ok fd ← sock_accept 3 0 | return 1
  let .ok _ ← poll_oneoff #[Subscription.read 2 fd] | return 10
  let .ok (bytes, flags) ← sock_recv fd 4 Riflags.recv_waitall | return 2
  if bytes.size != 4 || flags != 0 then return 3
  let .ok n ← sock_send fd bytes 0 | return 4
  if n != 4 then return 5
  if (← sock_shutdown fd Sdflags.wr) != 0 then return 6
  return ← fd_close fd

def socketErrors : Action UInt32 := do
  match ← sock_accept 4294967295 0 with
  | .ok _ => return 1
  | .error e => if e != Errno.badf then return 2
  match ← sock_recv 4294967295 4 0 with
  | .ok _ => return 3
  | .error e => if e != Errno.badf then return 4
  match ← sock_send 4294967295 "x".toUTF8 0 with
  | .ok _ => return 5
  | .error e => if e != Errno.badf then return 6
  if (← sock_shutdown 4294967295 Sdflags.wr) != Errno.badf then return 7
  return 0

def signal : Action UInt32 := do
  return ← proc_raise Signal.none

end LeanExe.Examples.Wasi
