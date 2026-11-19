import Verified.Wasi.ABI
import LeanExe.Wasi.Action

namespace Verified.Wasi

open Wasm LeanExe.Wasi

def metadataCode (pointer length : Nat) : Program :=
  [.const 0, .localGet pointer, .wrapI64, .store32 0,
   .const 4, .localGet length, .wrapI64, .store32 0,
   .const 8, .const 0, .store32 0]

def writeCode (output : Output) (pointer length errno : Nat) : Program :=
  metadataCode pointer length ++
    [.const output.fd.toUInt32, .const 0, .const 1, .const 8, .call 1,
     .localSet errno, .localGet errno, .extendUI32,
     .localGet errno, .eqz,
     .iff 0 1 [.const 8, .load32 0, .extendUI32] [.constI64 0] [] [.i64]]

/-- Pushes the word in local `count`, or the word in local `capacity` when the count is at least
the capacity. -/
def minCode (count capacity : Nat) : Program :=
  [.localGet count, .localGet capacity, .geUI64,
   .iff 0 1 [.localGet capacity] [.localGet count] [] [.i64]]

/-- Leaves in `target` the address of the window of a buffer and in `target + 1` its length, from
the buffer's root in local `root` and size in `root + 1` and the window's start in local `start`
and count in local `count`: the first position, the start or the size when that is smaller, in
`target`, the bytes from it to the end in `target + 1`, the length, the count or those bytes when
they are fewer, in `target + 1`, and the root plus the first position in `target`. -/
def windowCode (root start count target : Nat) : Program :=
  minCode start (root + 1) ++
    [.localSet target, .localGet (root + 1), .localGet target, .subI64, .localSet (target + 1)] ++
    minCode count (target + 1) ++
    [.localSet (target + 1), .localGet root, .localGet target, .addI64, .localSet target]

/-- The write wrapper of an output, a function from a buffer's root and size and a window's start
and count to the errno and the count: the window's address and length in locals 4 and 5, one
`fd_write` of the window's bytes, the errno, and the number of bytes written on errno 0 and 0
otherwise. -/
def writeFunction (output : Output) (typeIdx : Nat) : Function :=
  { params := [.i64, .i64, .i64, .i64]
    locals := [.i64, .i64, .i32]
    results := [.i64, .i64]
    body := windowCode 0 2 3 4 ++ writeCode output 4 5 6
    typeIdx := some typeIdx }

def exitCode (code : Nat) : Program :=
  [.localGet code, .wrapI64, .call 2, .unreachable]

end Verified.Wasi
