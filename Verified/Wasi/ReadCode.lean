module

public import Verified.Wasi.WrapperCode
public import Verified.Wasi.Relocation

@[expose] public section

namespace Verified.Wasi

open Wasm LeanExe.Wasi

def readCallCode (pointer capacity : Nat) : Program :=
  metadataCode pointer capacity ++
    [.const 0, .const 0, .const 1, .const 8, .call 0]

/-- Releases the byte string whose root local `root` holds, unless the root is 0, with the release
function of a module that imports `calls`, and sets the local to 0: the block of a reported request
that returned an errno. -/
def discardReadCodeWith (calls : List Call) (root : Nat) : Program :=
  [.localGet root, .eqzI64,
   .iff 0 0 [] [.localGet root, .call (3 + calls.length + 1)] [] [],
   .constI64 0, .localSet root]

def discardReadCode (root : Nat) : Program := discardReadCodeWith [] root

/-- The body of the read wrapper, a function from the address and the length of a region of
guest memory to the errno and the count: one `fd_read` of stdin into the region, the errno, and
the number of bytes read on errno 0 and 0 otherwise.  The caller passes a region below `2^32`
that lies apart from the scratch bytes. -/
def readCode (pointer length errno : Nat) : Program :=
  readCallCode pointer length ++
    [.localSet errno, .localGet errno, .extendUI32,
     .localGet errno, .eqz,
     .iff 0 1 [.const 8, .load32 0, .extendUI32] [.constI64 0] [] [.i64]]

def readFunction (typeIdx : Nat) : Function :=
  { params := [.i64, .i64]
    locals := [.i32]
    results := [.i64, .i64]
    body := readCode 0 1 2
    typeIdx := some typeIdx }

end Verified.Wasi
