import LeanExe.A64.Elf
import LeanExe.Linux.CallTable

/-!
The stamp program, a static Linux executable for AArch64 that makes its calls through the Linux
call layer: it reads the file whose path `pin` names in the working directory, runs a function over
bytes on the realtime clock's 16 bytes, 16 random bytes, and the file's bytes, and writes the
function's result to the file that `pout` names, which it creates or truncates with mode 0644.
The paths are fixed when the program is generated, have from 1 to 63 bytes, and hold no zero byte.

Every call loads its arguments into X0 to X3, sets X8 to the call's arm64 number, and branches with
`BL` to `svcRetAddr`, the routine `SVC #0; RET` that ends the runtime's `sysRead`, so the runtime
of `genElfWith` and its layout serve the program unchanged.  The routine `genStampMain` keeps the
block's address in X19 while it makes the calls before the function's, and the root of the
allocator's block, the descriptor of the open file, and the count of bytes read or the length of
the result in its frame.  A call that fails ends the run at a stub that sets X0 to its status and
branches to the exit word: 72 when `clock_gettime` does not return 0, 73 when `getrandom` does not
return 16, 67 and 70 when `openat` of the input or the output returns a value of 2^31 or more, 68
when a `read` returns more than it asked for, 64 when the bytes read fill the block, 69 and 71 when
`close` of the input or the output does not return 0, and 74 when a `write` returns 0 or more than
it asked for.
-/

namespace LeanExe.A64

open Wasm

/-- The routine `SVC #0; RET`: the last two words of the runtime's `sysRead`. -/
def svcRetAddr : UInt64 := after sysReadAddr 1

/-- The value that the bytes `bs` give as a word, the first byte lowest. -/
def leWord (bs : List UInt8) : UInt64 := bs.foldr (fun b w => w * 256 + b.toUInt64) 0

/-- The words of the path `path` with its terminating zero byte, padded with zero bytes to a
multiple of 8, each word's lowest byte first. -/
def pathWords (path : List UInt8) : List UInt64 :=
  let n := path.length / 8 + 1
  let bytes := path ++ List.replicate (8 * n - path.length) 0
  (List.range n).map fun i => leWord ((bytes.drop (8 * i)).take 8)

/-- `AT_FDCWD`, -100 as a 64-bit word (`sys.txt.const` line 37). -/
def atFdcwd : UInt64 := 0xFFFFFFFFFFFFFF9C

/-- `O_RDONLY | O_CLOEXEC` on arm64. -/
def stampInFlags : UInt64 := 0x80000

/-- `O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC` on arm64. -/
def stampOutFlags : UInt64 := 0x80241

/-- The mode of the output file, 0644. -/
def stampOutMode : Fin 65536 := 420

/-- The instructions that store the words `ws` from the frame's word slot `slot`, each a
`movImm` into X16 and an `STR`. -/
def storeWords (ws : List UInt64) (slot : Nat) : GenM (List Instr) := do
  let parts ← (List.range ws.length).mapM fun i =>
    if h : slot + i < 4096 then pure (movImm 16 (ws.getD i 0) ++ [.str 16 31 ⟨slot + i, h⟩])
    else throw "a frame slot past 4095"
  return parts.flatten

/-- The size of the frame of `genStampMain` for the paths `pin` and `pout`: the return address,
the block's root, a descriptor, a count, and the words of the two paths, a multiple of 16 bytes. -/
def stampFrame (pin pout : List UInt8) : Nat :=
  16 * ((32 + 8 * ((pathWords pin).length + (pathWords pout).length) + 15) / 16)

/-- The number of instructions of `genStampMain` for the paths `pin` and `pout`. -/
def stampMainSize (pin pout : List UInt8) : Nat :=
  162 + 5 * ((pathWords pin).length + (pathWords pout).length)

/-- Whether a path suits `genStampMain`: from 1 to 63 bytes, none of them zero. -/
def pathOk (path : List UInt8) : Bool := 0 < path.length && path.length < 64 && !path.contains 0

/-- The entry routine of the stamp program, placed at `a`, with the function over bytes at `entry`,
the module's allocator at `alloc`, the routine `SVC #0; RET` at `svc`, and the exit word at
`base`.  Its stubs follow its return and set X0 to 64, 67, 68, 69, 70, 71, 72, 73, or 74. -/
def genStampMain (a entry alloc svc inMax room base : UInt64) (pin pout : List UInt8) :
    GenM (List Instr) := do
  unless pathOk pin && pathOk pout do throw "a path of no byte, of 64 bytes or more, or with a zero"
  let wi := (pathWords pin).length
  let wo := (pathWords pout).length
  let F := stampFrame pin pout
  let fr : Fin 4096 ← if h : F < 4096 then pure ⟨F, h⟩ else throw "a frame of 4096 bytes or more"
  let outSlot : Fin 4096 ← if h : 32 + 8 * wi < 4096 then pure ⟨32 + 8 * wi, h⟩
    else throw "a frame of 4096 bytes or more"
  let H := 49 + 5 * wi
  let P2 := H + 30 + 5 * wo
  let W := P2 + 17
  let S := W + 21
  let stubAt (j : Nat) : UInt64 := after a (S + 5 * j)
  let e64 := stubAt 0
  let e67 := stubAt 1
  let e68 := stubAt 2
  let e69 := stubAt 3
  let e70 := stubAt 4
  let e71 := stubAt 5
  let e72 := stubAt 6
  let e73 := stubAt 7
  let e74 := stubAt 8
  let callA := Instr.bl (← bField (after a 12) alloc)
  let callS (i : Nat) : GenM Instr := do return Instr.bl (← bField (after a i) svc)
  let storesIn ← storeWords (pathWords pin) 4
  let storesOut ← storeWords (pathWords pout) (4 + wi)
  let stub (j code : Nat) : GenM (List Instr) := do
    return movImm 0 (UInt64.ofNat code) ++ [.b (← bField (after (stubAt j) 4) base)]
  let front : List Instr :=
    [.subImm 31 31 fr, .str 30 31 0, .addImm 18 31 0] ++ movImm 16 room ++
      [.subReg 18 18 16] ++ movImm 0 (inMax + 33) ++
      [callA, .str 0 31 1, .addReg 19 17 0, .addImm 19 19 2048, .addImm 19 19 2048]
  let clock : List Instr :=
    [.movz 0 0 0, .addImm 1 19 0, .movz 8 113 0, ← callS 20,
      .cbnz 0 (← cbField (after a 21) e72)]
  let random : List Instr :=
    [.addImm 0 19 16, .movz 1 16 0, .movz 2 0 0, .movz 8 278 0, ← callS 26, .subsImm 31 0 16,
      .bcond 1 (← cbField (after a 28) e73)]
  let P1 := 29 + 5 * wi
  let openIn : List Instr :=
    movImm 0 atFdcwd ++ [.addImm 1 31 32] ++ movImm 2 stampInFlags ++
      [.movz 3 0 0, .movz 8 56 0, ← callS (P1 + 11), .lsrImm 16 0 31,
        .cbnz 16 (← cbField (after a (P1 + 13)) e67), .str 0 31 2, .addImm 1 19 32] ++
      movImm 2 (inMax + 1)
  let readLoop : List Instr :=
    [.ldr 0 31 2, .movz 8 63 0, ← callS (H + 2), .cbz 0 (← cbField (after a (H + 3)) (after a (H + 10))),
      .subsReg 31 0 2, .bcond 8 (← cbField (after a (H + 5)) e68), .addReg 1 1 0, .subReg 2 2 0,
      .cbnz 2 (← cbField (after a (H + 8)) (after a H)), .b (← bField (after a (H + 9)) e64)]
  let afterRead : List Instr :=
    movImm 16 (inMax + 1) ++ [.subReg 16 16 2, .str 16 31 3, .ldr 0 31 2, .movz 8 57 0,
      ← callS (H + 18), .cbnz 0 (← cbField (after a (H + 19)) e69), .ldr 0 31 1, .ldr 1 31 3,
      .addImm 1 1 32, .bl (← bField (after a (H + 23)) entry), mov 2 1, .addReg 1 17 0,
      .addImm 1 1 2048, .addImm 1 1 2048, .str 1 31 1, .str 2 31 3]
  let openOut : List Instr :=
    movImm 0 atFdcwd ++ [.addImm 1 31 outSlot] ++ movImm 2 stampOutFlags ++
      [.movz 3 stampOutMode 0, .movz 8 56 0, ← callS (P2 + 11), .lsrImm 16 0 31,
        .cbnz 16 (← cbField (after a (P2 + 13)) e70), .str 0 31 2, .ldr 1 31 1, .ldr 2 31 3]
  let writeLoop : List Instr :=
    [.cbz 2 (← cbField (after a W) (after a (W + 10))), .ldr 0 31 2, .movz 8 64 0, ← callS (W + 3),
      .cbz 0 (← cbField (after a (W + 4)) e74), .subsReg 31 0 2,
      .bcond 8 (← cbField (after a (W + 6)) e74), .addReg 1 1 0, .subReg 2 2 0,
      .b (← bField (after a (W + 9)) (after a W))]
  let finish : List Instr :=
    [.ldr 0 31 2, .movz 8 57 0, ← callS (W + 12), .cbnz 0 (← cbField (after a (W + 13)) e71)] ++
      movImm 0 0 ++ [.ldr 30 31 0, .addImm 31 31 fr, .ret 30]
  let stubs := (← stub 0 64) ++ (← stub 1 67) ++ (← stub 2 68) ++ (← stub 3 69) ++
    (← stub 4 70) ++ (← stub 5 71) ++ (← stub 6 72) ++ (← stub 7 73) ++ (← stub 8 74)
  return front ++ clock ++ random ++ storesIn ++ openIn ++ readLoop ++ afterRead ++ storesOut ++
    openOut ++ writeLoop ++ finish ++ stubs

/-- The stamp program of function `k` of `m`, placed after its exit word at `base`, with the
routine `SVC #0; RET` at `svc`, a limit of `inMax` bytes of the input file, a stack of `room` bytes
below `main`'s frame, a memory of `cap` pages, and the paths `pin` and `pout`.  Function 0 of the
functions that calls reach from function `k` is the allocator, and the functions may store
bytes. -/
def genStampProgram (m : Module) (k : Nat) (inMax svc base room : UInt64) (cap : Nat)
    (pin pout : List UInt8) : GenM (List Instr) :=
  genProgramWith (stampMainSize pin pout) (fun e => do
      let fs ← (reachFrom m k).mapM (funcOf m)
      match entryIn (sigIn (callTargets m k) fs) (after (after base 1) (stampMainSize pin pout))
          fs 0 with
      | some (a0, _, _) => genStampMain (after base 1) e a0 svc inMax room base pin pout
      | none => throw "no allocator among the functions that the function calls")
    m k base cap true

/-- The stamp executable of function `k` of `m`.  The layout of `genElfWith` reserves 16 bytes for
`main`'s frame below the stack's top and `room` bytes below them; the stamp program's frame takes
`stampFrame pin pout` bytes, so the layout receives the room `room + (stampFrame pin pout - 16)`,
and the stack holds `room` bytes below the frame. -/
def genStampElf (m : Module) (k : Nat) (inMax room : UInt64) (cap : Nat) (pin pout : List UInt8) :
    GenM (List UInt8 × ElfLayout) := do
  unless room.toNat + stampFrame pin pout < 2 ^ 32 do throw "a stack of 2^32 bytes or more"
  genElfWith (fun rd _ base => genStampProgram m k inMax (after rd 1) base room cap pin pout) m
    (room + UInt64.ofNat (stampFrame pin pout - 16)) cap

end LeanExe.A64
