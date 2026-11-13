import LeanExe.Wasi.Calls

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
  { name := "fd_advise", params := [.word32, .word64, .word64, .enum32 6] }

def fdAllocate : Call :=
  { name := "fd_allocate", params := [.word32, .word64, .word64] }

def fdClose : Call :=
  { name := "fd_close", params := [.word32] }

def fdDatasync : Call :=
  { name := "fd_datasync", params := [.word32] }

def fdFdstatGet : Call :=
  { name := "fd_fdstat_get", params := [.word32, .record 24 8 [(0, 1), (2, 2), (8, 8), (16, 8)]] }

def fdFdstatSetFlags : Call :=
  { name := "fd_fdstat_set_flags", params := [.word32, .flags32 0x1f] }

def fdFdstatSetRights : Call :=
  { name := "fd_fdstat_set_rights", params := [.word32, .flags64 0x3fffffff, .flags64 0x3fffffff] }

def fdFilestatGet : Call :=
  { name := "fd_filestat_get", params := [.word32,
      .record 64 8 [(0, 8), (8, 8), (16, 1), (24, 8), (32, 8), (40, 8), (48, 8), (56, 8)]] }

def fdFilestatSetSize : Call :=
  { name := "fd_filestat_set_size", params := [.word32, .word64] }

def fdFilestatSetTimes : Call :=
  { name := "fd_filestat_set_times", params := [.word32, .word64, .word64, .flags32 0xf] }

def fdPrestatGet : Call :=
  { name := "fd_prestat_get", params := [.word32, .record 8 4 [(0, 1), (4, 4)]] }

def fdPrestatDirName : Call :=
  { name := "fd_prestat_dir_name", params := [.word32, .output] }

def fdReaddir : Call :=
  { name := "fd_readdir", params := [.word32, .output, .word64, .result32] }

def fdRenumber : Call :=
  { name := "fd_renumber", params := [.word32, .word32] }

def fdSeek : Call :=
  { name := "fd_seek", params := [.word32, .word64, .enum32 3, .result64] }

def fdSync : Call :=
  { name := "fd_sync", params := [.word32] }

def fdTell : Call :=
  { name := "fd_tell", params := [.word32, .result64] }

def pathCreateDirectory : Call :=
  { name := "path_create_directory", params := [.word32, .input] }

def pathFilestatGet : Call :=
  { name := "path_filestat_get", params := [.word32, .flags32 0x1, .input,
      .record 64 8 [(0, 8), (8, 8), (16, 1), (24, 8), (32, 8), (40, 8), (48, 8), (56, 8)]] }

def pathFilestatSetTimes : Call :=
  { name := "path_filestat_set_times", params := [.word32, .flags32 0x1, .input, .word64, .word64,
      .flags32 0xf] }

def pathLink : Call :=
  { name := "path_link", params := [.word32, .flags32 0x1, .input, .word32, .input] }

def pathOpen : Call :=
  { name := "path_open", params := [.word32, .flags32 0x1, .input, .flags32 0xf,
      .flags64 0x3fffffff, .flags64 0x3fffffff, .flags32 0x1f, .result32] }

def pathReadlink : Call :=
  { name := "path_readlink", params := [.word32, .input, .output, .result32] }

def pathRemoveDirectory : Call :=
  { name := "path_remove_directory", params := [.word32, .input] }

def pathRename : Call :=
  { name := "path_rename", params := [.word32, .input, .word32, .input] }

def pathSymlink : Call :=
  { name := "path_symlink", params := [.input, .word32, .input] }

def pathUnlinkFile : Call :=
  { name := "path_unlink_file", params := [.word32, .input] }

def procRaise : Call :=
  { name := "proc_raise", params := [.enum32 31] }

def schedYield : Call :=
  { name := "sched_yield", params := [] }

def randomGet : Call :=
  { name := "random_get", params := [.output] }

def sockAccept : Call :=
  { name := "sock_accept", params := [.word32, .flags32 0x1f, .result32] }

def sockShutdown : Call :=
  { name := "sock_shutdown", params := [.word32, .flags32 0x3] }

end LeanExe.Wasi.Call
