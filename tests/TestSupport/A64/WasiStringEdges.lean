import LeanExe.A64.Wasi

/-!
Modules that call `args_sizes_get` or `args_get` once with chosen pointers, for the runs of
`tests/linux/a64-wasi.sh` that the commands of the verified compiler cannot make: regions that
overlap, regions that end at the memory's end, and regions one byte past it.  Each module has one
page of memory, which its data fills with the byte 0xAA from 0x100 to 0x200 and from 0xFF00 to
0x10000, so that a missing write of a zero byte changes the output.  Its `_start` stores the call's
errno at guest address 12, writes the errno's four bytes and then the 256 bytes of a window to
standard output with `fd_write`, the iovec at 0 and the count at 8, and calls `proc_exit` with 0.
A call that traps ends the run with status 2 and nothing written.  `edgeCases` names each case with
its call, its two pointers, and its window.
-/

namespace TestSupport.A64.WasiStringEdges

open Wasm LeanExe LeanExe.A64

/-- 256 bytes of 0xAA. -/
def fill : List UInt8 := List.replicate 256 0xAA

/-- The program of `fd_write` of the `len` bytes from `p` to standard output, with the iovec at 0,
the count at 8, and the errno stored at 16. -/
def writeOut (p len : UInt32) : List Instruction :=
  [.const 0, .const p, .store32 0, .const 4, .const len, .store32 0, .const 16, .const 1, .const 0,
    .const 1, .const 8, .call 1, .store32 0]

/-- The module that calls `args_sizes_get` when `sizes` holds, else `args_get`, with the pointers
`p` and `q`, and writes the errno and the 256 bytes from `window`. -/
def edgeModule (sizes : Bool) (p q window : UInt32) : Module :=
  let data : List DataSegment :=
    [{ offset := some 0x100, bytes := fill }, { offset := some 0xFF00, bytes := fill }]
  let body : List Instruction :=
    [.const 12, .const p, .const q, .call (if sizes then 3 else 4), .store32 0] ++
      writeOut 12 4 ++ writeOut window 256 ++ [.const 0, .call 2]
  { imports := streamImports ++ [pointerPairImport "args_sizes_get", pointerPairImport "args_get"],
    memory := some { pagesMin := 1, data },
    funcs := [{ body }],
    exports := [⟨"_start", 5⟩] }

/-- The cases: a name, whether the call is `args_sizes_get`, the two pointers, and the window.
With the arguments `p`, the empty string, and `abc`, the count is 3 and the size 7. -/
def edgeCases : List (String × Bool × UInt32 × UInt32 × UInt32) :=
  [("strings-apart", false, 0x100, 0x140, 0x100),
    ("strings-overlap", false, 0x180, 0x184, 0x100),
    ("strings-array-end", false, 0xFFF4, 0xFF00, 0xFF00),
    ("strings-buffer-end", false, 0xFF00, 0xFFF9, 0xFF00),
    ("strings-array-past", false, 0xFFF5, 0xFF00, 0xFF00),
    ("strings-buffer-past", false, 0xFF00, 0xFFFA, 0xFF00),
    ("sizes-same", true, 0x100, 0x100, 0x100),
    ("sizes-count-end", true, 0xFFFC, 0xFF00, 0xFF00),
    ("sizes-count-past", true, 0xFFFD, 0xFF00, 0xFF00),
    ("sizes-size-past", true, 0xFF00, 0xFFFD, 0xFF00)]

/-- The executable of a case, with the cap and the room of the other WASI executables. -/
def edgeElf (sizes : Bool) (p q window : UInt32) : Except String (List UInt8 × ElfLayout) :=
  genWasiElf (edgeModule sizes p q window) 5 65536 4096

end TestSupport.A64.WasiStringEdges
