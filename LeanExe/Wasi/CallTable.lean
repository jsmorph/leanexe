module

public import LeanExe.Wasi.Calls

@[expose] public section

/-!
The descriptions of the flat Preview 1 functions, which `tools/wasi-calls.py` generates from the
pinned witx (WebAssembly/WASI commit `fae981bae14809d91f9bc2d63852d461f331d161`).  Its check fails
when this file differs from its output.
-/

namespace LeanExe.Wasi.Call

def argsGet : Call :=
  { name := "args_get", params := [.reported 4 4 false, .reported 1 1 true],
    reporter := some "args_sizes_get" }

def argsSizesGet : Call :=
  { name := "args_sizes_get", params := [.result32, .result32] }

def environGet : Call :=
  { name := "environ_get", params := [.reported 4 4 false, .reported 1 1 true],
    reporter := some "environ_sizes_get" }

def environSizesGet : Call :=
  { name := "environ_sizes_get", params := [.result32, .result32] }

def clockResGet : Call :=
  { name := "clock_res_get", params := [.enum32 4, .result64] }

def clockTimeGet : Call :=
  { name := "clock_time_get", params := [.enum32 4, .word64, .result64] }

def fdAdvise : Call :=
  { name := "fd_advise", params := [.handle, .word64, .word64, .enum32 6] }

def fdAllocate : Call :=
  { name := "fd_allocate", params := [.handle, .word64, .word64] }

def fdClose : Call :=
  { name := "fd_close", params := [.handle] }

def fdDatasync : Call :=
  { name := "fd_datasync", params := [.handle] }

def fdFdstatGet : Call :=
  { name := "fd_fdstat_get", params := [.handle, .record 24 8 [(0, 1), (2, 2), (8, 8), (16, 8)]] }

def fdFdstatSetFlags : Call :=
  { name := "fd_fdstat_set_flags", params := [.handle, .flags32 0x1f] }

def fdFdstatSetRights : Call :=
  { name := "fd_fdstat_set_rights", params := [.handle, .flags64 0x3fffffff, .flags64 0x3fffffff] }

def fdFilestatGet : Call :=
  { name := "fd_filestat_get", params := [.handle,
      .record 64 8 [(0, 8), (8, 8), (16, 1), (24, 8), (32, 8), (40, 8), (48, 8), (56, 8)]] }

def fdFilestatSetSize : Call :=
  { name := "fd_filestat_set_size", params := [.handle, .word64] }

def fdFilestatSetTimes : Call :=
  { name := "fd_filestat_set_times", params := [.handle, .word64, .word64, .flags32 0xf] }

def fdPread : Call :=
  { name := "fd_pread", params := [.handle, .iovec false, .word64, .result32] }

def fdPrestatGet : Call :=
  { name := "fd_prestat_get", params := [.handle, .record 8 4 [(0, 1), (4, 4)]] }

def fdPrestatDirName : Call :=
  { name := "fd_prestat_dir_name", params := [.handle, .output] }

def fdPwrite : Call :=
  { name := "fd_pwrite", params := [.handle, .iovec true, .word64, .result32] }

def fdRead : Call :=
  { name := "fd_read", params := [.handle, .iovec false, .result32] }

def fdReaddir : Call :=
  { name := "fd_readdir", params := [.handle, .output, .word64, .result32] }

def fdRenumber : Call :=
  { name := "fd_renumber", params := [.handle, .handle] }

def fdSeek : Call :=
  { name := "fd_seek", params := [.handle, .word64, .enum32 3, .result64] }

def fdSync : Call :=
  { name := "fd_sync", params := [.handle] }

def fdTell : Call :=
  { name := "fd_tell", params := [.handle, .result64] }

def fdWrite : Call :=
  { name := "fd_write", params := [.handle, .iovec true, .result32] }

def pathCreateDirectory : Call :=
  { name := "path_create_directory", params := [.handle, .input] }

def pathFilestatGet : Call :=
  { name := "path_filestat_get", params := [.handle, .flags32 0x1, .input,
      .record 64 8 [(0, 8), (8, 8), (16, 1), (24, 8), (32, 8), (40, 8), (48, 8), (56, 8)]] }

def pathFilestatSetTimes : Call :=
  { name := "path_filestat_set_times", params := [.handle, .flags32 0x1, .input, .word64, .word64,
      .flags32 0xf] }

def pathLink : Call :=
  { name := "path_link", params := [.handle, .flags32 0x1, .input, .handle, .input] }

def pathOpen : Call :=
  { name := "path_open", params := [.handle, .flags32 0x1, .input, .flags32 0xf,
      .flags64 0x3fffffff, .flags64 0x3fffffff, .flags32 0x1f, .result32] }

def pathReadlink : Call :=
  { name := "path_readlink", params := [.handle, .input, .output, .result32] }

def pathRemoveDirectory : Call :=
  { name := "path_remove_directory", params := [.handle, .input] }

def pathRename : Call :=
  { name := "path_rename", params := [.handle, .input, .handle, .input] }

def pathSymlink : Call :=
  { name := "path_symlink", params := [.input, .handle, .input] }

def pathUnlinkFile : Call :=
  { name := "path_unlink_file", params := [.handle, .input] }

def pollOneoffClock : Call :=
  { name := "poll_oneoff",
    params := [.subscriptions [
      [⟨0, 8, .const 1⟩, ⟨8, 1, .const 0⟩, ⟨16, 4, .word⟩, ⟨24, 8, .word⟩, ⟨32, 8, .word⟩,
        ⟨40, 2, .word⟩]],
      .result32] }

def pollOneoffRead : Call :=
  { name := "poll_oneoff",
    params := [.subscriptions [
      [⟨0, 8, .const 1⟩, ⟨8, 1, .const 1⟩, ⟨16, 4, .handle⟩],
      [⟨0, 8, .const 2⟩, ⟨8, 1, .const 0⟩, ⟨16, 4, .word⟩, ⟨24, 8, .word⟩, ⟨32, 8, .const 0⟩,
        ⟨40, 2, .const 0⟩]],
      .result32] }

def pollOneoffWrite : Call :=
  { name := "poll_oneoff",
    params := [.subscriptions [
      [⟨0, 8, .const 1⟩, ⟨8, 1, .const 2⟩, ⟨16, 4, .handle⟩],
      [⟨0, 8, .const 2⟩, ⟨8, 1, .const 0⟩, ⟨16, 4, .word⟩, ⟨24, 8, .word⟩, ⟨32, 8, .const 0⟩,
        ⟨40, 2, .const 0⟩]],
      .result32] }

def procRaise : Call :=
  { name := "proc_raise", params := [.enum32 31] }

def schedYield : Call :=
  { name := "sched_yield", params := [] }

def randomGet : Call :=
  { name := "random_get", params := [.output] }

def sockAccept : Call :=
  { name := "sock_accept", params := [.handle, .flags32 0x1f, .result32] }

def sockShutdown : Call :=
  { name := "sock_shutdown", params := [.handle, .flags32 0x3] }

/-- The descriptions of this file, in order.  The handle check requires the call of each `sys`
command to be one of them. -/
def table : List Call := [argsGet, argsSizesGet, environGet, environSizesGet, clockResGet,
    clockTimeGet, fdAdvise, fdAllocate, fdClose, fdDatasync, fdFdstatGet, fdFdstatSetFlags,
    fdFdstatSetRights, fdFilestatGet, fdFilestatSetSize, fdFilestatSetTimes, fdPread, fdPrestatGet,
    fdPrestatDirName, fdPwrite, fdRead, fdReaddir, fdRenumber, fdSeek, fdSync, fdTell, fdWrite,
    pathCreateDirectory, pathFilestatGet, pathFilestatSetTimes, pathLink, pathOpen, pathReadlink,
    pathRemoveDirectory, pathRename, pathSymlink, pathUnlinkFile, pollOneoffClock, pollOneoffRead,
    pollOneoffWrite, procRaise, schedYield, randomGet, sockAccept, sockShutdown]

end LeanExe.Wasi.Call
