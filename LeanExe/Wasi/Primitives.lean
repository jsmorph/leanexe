import Lean
import LeanExe.Wasi

namespace LeanExe.Wasi

inductive Operand where
  | local32 (slot : Nat)
  | local64 (slot : Nat)
  | address (value : Nat)
  | buffer

inductive Result where
  | errno
  | values (fields : List (Nat × Nat))
  | buffer (capacitySlot : Nat) (counted recvFlags : Bool)
  | preopenName
  | strings (sizesFunction : String)
  | events
  | exit

def Result.width : Result → Nat
  | .errno => 1
  | .values fields => 2 + fields.length
  | .buffer _ _ flags => if flags then 6 else 5
  | .preopenName => 5
  | .strings _ | .events => 4
  | .exit => 1

def Result.owners : Result → List Nat
  | .buffer .. | .preopenName | .strings _ | .events => [2]
  | _ => []

inductive Iovec where
  | none
  | input (pointerSlot : Nat)
  | output

structure Primitive where
  name : String
  paramCount : Nat
  result : Result
  operands : List Operand
  iovec : Iovec := .none

def Primitive.sourceName (p : Primitive) : Lean.Name :=
  .str `LeanExe.Wasi p.name

def primitives : Array Primitive := #[
  ⟨"args_get", 0, .strings "args_sizes_get", [.address 0, .address 0], .none⟩,
  ⟨"args_sizes_get", 0, .values [(0, 4), (4, 4)], [.address 64, .address 68], .none⟩,
  ⟨"environ_get", 0, .strings "environ_sizes_get", [.address 0, .address 0], .none⟩,
  ⟨"environ_sizes_get", 0, .values [(0, 4), (4, 4)], [.address 64, .address 68], .none⟩,
  ⟨"clock_res_get", 1, .values [(0, 8)], [.local32 0, .address 64], .none⟩,
  ⟨"clock_time_get", 2, .values [(0, 8)], [.local32 0, .local64 1, .address 64], .none⟩,
  ⟨"fd_advise", 4, .errno, [.local32 0, .local64 1, .local64 2, .local32 3], .none⟩,
  ⟨"fd_allocate", 3, .errno, [.local32 0, .local64 1, .local64 2], .none⟩,
  ⟨"fd_close", 1, .errno, [.local32 0], .none⟩,
  ⟨"fd_datasync", 1, .errno, [.local32 0], .none⟩,
  ⟨"fd_fdstat_get", 1, .values [(0, 1), (2, 2), (8, 8), (16, 8)], [.local32 0, .address 64], .none⟩,
  ⟨"fd_fdstat_set_flags", 2, .errno, [.local32 0, .local32 1], .none⟩,
  ⟨"fd_fdstat_set_rights", 3, .errno, [.local32 0, .local64 1, .local64 2], .none⟩,
  ⟨"fd_filestat_get", 1, .values [(0, 8), (8, 8), (16, 1), (24, 8), (32, 8), (40, 8), (48, 8), (56, 8)], [.local32 0, .address 64], .none⟩,
  ⟨"fd_filestat_set_size", 2, .errno, [.local32 0, .local64 1], .none⟩,
  ⟨"fd_filestat_set_times", 4, .errno, [.local32 0, .local64 1, .local64 2, .local32 3], .none⟩,
  ⟨"fd_pread", 3, .buffer 1 true false, [.local32 0, .address 0, .address 1, .local64 2, .address 64], .output⟩,
  ⟨"fd_prestat_get", 1, .values [(0, 1), (4, 4)], [.local32 0, .address 64], .none⟩,
  ⟨"fd_prestat_dir_name", 1, .preopenName, [.local32 0, .buffer, .local32 1], .none⟩,
  ⟨"fd_pwrite", 5, .values [(0, 4)], [.local32 0, .address 0, .address 1, .local64 4, .address 64], .input 2⟩,
  ⟨"fd_read", 2, .buffer 1 true false, [.local32 0, .address 0, .address 1, .address 64], .output⟩,
  ⟨"fd_readdir", 3, .buffer 1 true false, [.local32 0, .buffer, .local32 1, .local64 2, .address 64], .none⟩,
  ⟨"fd_renumber", 2, .errno, [.local32 0, .local32 1], .none⟩,
  ⟨"fd_seek", 3, .values [(0, 8)], [.local32 0, .local64 1, .local32 2, .address 64], .none⟩,
  ⟨"fd_sync", 1, .errno, [.local32 0], .none⟩,
  ⟨"fd_tell", 1, .values [(0, 8)], [.local32 0, .address 64], .none⟩,
  ⟨"fd_write", 4, .values [(0, 4)], [.local32 0, .address 0, .address 1, .address 64], .input 2⟩,
  ⟨"path_create_directory", 4, .errno, [.local32 0, .local32 2, .local32 3], .none⟩,
  ⟨"path_filestat_get", 5, .values [(0, 8), (8, 8), (16, 1), (24, 8), (32, 8), (40, 8), (48, 8), (56, 8)], [.local32 0, .local32 1, .local32 3, .local32 4, .address 64], .none⟩,
  ⟨"path_filestat_set_times", 8, .errno, [.local32 0, .local32 1, .local32 3, .local32 4, .local64 5, .local64 6, .local32 7], .none⟩,
  ⟨"path_link", 9, .errno, [.local32 0, .local32 1, .local32 3, .local32 4, .local32 5, .local32 7, .local32 8], .none⟩,
  ⟨"path_open", 9, .values [(0, 4)], [.local32 0, .local32 1, .local32 3, .local32 4, .local32 5, .local64 6, .local64 7, .local32 8, .address 64], .none⟩,
  ⟨"path_readlink", 5, .buffer 4 true false, [.local32 0, .local32 2, .local32 3, .buffer, .local32 4, .address 64], .none⟩,
  ⟨"path_remove_directory", 4, .errno, [.local32 0, .local32 2, .local32 3], .none⟩,
  ⟨"path_rename", 8, .errno, [.local32 0, .local32 2, .local32 3, .local32 4, .local32 6, .local32 7], .none⟩,
  ⟨"path_symlink", 7, .errno, [.local32 1, .local32 2, .local32 3, .local32 5, .local32 6], .none⟩,
  ⟨"path_unlink_file", 4, .errno, [.local32 0, .local32 2, .local32 3], .none⟩,
  ⟨"poll_oneoff", 2, .events, [.address 0, .address 0, .address 0, .address 64], .none⟩,
  ⟨"proc_exit", 1, .exit, [.local32 0], .none⟩,
  ⟨"proc_raise", 1, .errno, [.local32 0], .none⟩,
  ⟨"sched_yield", 0, .errno, [], .none⟩,
  ⟨"random_get", 1, .buffer 0 false false, [.buffer, .local32 0], .none⟩,
  ⟨"sock_accept", 2, .values [(0, 4)], [.local32 0, .local32 1, .address 64], .none⟩,
  ⟨"sock_recv", 3, .buffer 1 true true, [.local32 0, .address 0, .address 1, .local32 2, .address 64, .address 68], .output⟩,
  ⟨"sock_send", 5, .values [(0, 4)], [.local32 0, .address 0, .address 1, .local32 4, .address 64], .input 2⟩,
  ⟨"sock_shutdown", 2, .errno, [.local32 0, .local32 1], .none⟩]

end LeanExe.Wasi
