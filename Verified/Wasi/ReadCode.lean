import Verified.Wasi.WrapperCode
import Verified.Wasi.Relocation

namespace Verified.Wasi

open Wasm LeanExe.Wasi

def readCallCode (pointer capacity : Nat) : Program :=
  metadataCode pointer capacity ++
    [.const 0, .const 0, .const 1, .const 8, .call 0]

/-- Releases the read buffer at `root` with the release function of a module that imports
`calls`. -/
def discardReadCodeWith (calls : List Call) (root : Nat) : Program :=
  [.localGet root, .eqzI64,
   .iff 0 0 [] [.localGet root, .call (3 + calls.length + 1)] [] [],
   .constI64 0, .localSet root]

def discardReadCode (root : Nat) : Program := discardReadCodeWith [] root

def readCodeWith (calls : List Call) (capacity root errno length : Nat) : Program :=
  [.localGet capacity, .constI64 4294967296, .geUI64,
   .iff 0 0
     [.constI64 61, .localSet errno, .constI64 0, .localSet root,
      .constI64 0, .localSet length]
     ([.localGet capacity, .eqzI64,
       .iff 0 1 [.constI64 0] [.localGet capacity, .call (3 + calls.length)] [] [.i64],
       .localSet root] ++
      readCallCode root capacity ++
      [.extendUI32, .localSet errno,
       .localGet errno, .eqzI64,
       .iff 0 0
         ([.const 8, .load32 0, .extendUI32, .localSet length,
           .localGet length, .eqzI64,
           .iff 0 0 (discardReadCodeWith calls root) [] [] []])
         (discardReadCodeWith calls root ++ [.constI64 0, .localSet length]) [] []]) [] [],
   .localGet errno, .localGet root, .localGet length]

def readCode (capacity root errno length : Nat) : Program :=
  readCodeWith [] capacity root errno length

def readFunctionWith (calls : List Call) (typeIdx : Nat) : Function :=
  { params := [.i64]
    locals := [.i64, .i64, .i64]
    results := [.i64, .i64, .i64]
    body := readCodeWith calls 0 1 2 3
    typeIdx := some typeIdx }

def readFunction (typeIdx : Nat) : Function := readFunctionWith [] typeIdx

end Verified.Wasi
