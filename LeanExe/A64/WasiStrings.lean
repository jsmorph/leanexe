import LeanExe.A64.Gen

/-!
The stubs of `args_sizes_get`, `args_get`, `environ_sizes_get`, and `environ_get` of a WASI command
as a static Linux executable for AArch64.  They make no call: they read the arguments and the
environment from the process's initial stack, whose address the executable's `main` saves in the
first word of the shim's scratch, at `X17 + areaSize cap`.  Linux enters the process with SP at
`argc`, followed by the pointers to the arguments, 0, and the pointers to the environment's
strings, 0, each string ending with a zero byte (`fs/binfmt_elf.c` of Linux 7.0, lines 301 to
358), so the arguments' vector lies at the initial SP plus 8 and the environment's at the initial
SP plus `16 + 8 · argc`.  `vectorStart` sets X9 to one of them, and `StringVector` names which.

The scan piece counts the strings of the vector at X9 in X12 and sums their sizes, each string's
length plus one, in X13, until it reaches the vector's terminating 0.  It stops and branches to its
overflow target when the sum reaches `2^32`, which covers a count of `2^32` or more, since each
string adds at least 1, and keeps every sum below `2^64` whatever the pointers.

`sizesStub` follows the shim's `sizesInvoke`: it requires the count's pointer in X0 and the size's
in X1 to leave four bytes within the guest's memory, whose size it reads from the area's first word
plus 8, and otherwise branches to the trap stub.  It then scans the vector and returns errno 61 when
the scan overflows, or stores the count and the size as 32-bit words at their pointers, in that
order, and returns 0.  `stringsStub` follows `stringsInvoke`: it scans the vector and branches to
the trap stub when the scan overflows, then requires the pointers' array at X0 and the buffer at
X1 to lie within the memory, and then writes in two passes, first the address of each string's
copy into the array, then each string with its zero byte into the buffer, and returns 0.  The
stubs keep X17, X18, SP, and X30, use no stack, and write X0, X9 to X16, X20, and the guest's
memory.  Every store into the guest's memory goes through X16, whose value plus 4,092 is the byte's
address, as `resultTail` stores its count.
-/

namespace LeanExe.A64

/-- The vector of string pointers on the initial stack that a stub reads: the arguments' or the
environment's. -/
inductive StringVector where
  | args
  | environ
  deriving DecidableEq, Repr

/-- The instructions that set X9 to the address of the vector `v`, from the scratch's address in
X20, whose first word holds the initial SP: the initial SP plus 8 for the arguments, and the
initial SP plus `16 + 8 · argc`, with `argc` the initial stack's first word, for the
environment. -/
def vectorStart : StringVector → List Instr
  | .args => [.ldr 9 20 0, .addImm 9 9 8]
  | .environ => [.ldr 9 20 0, .ldr 10 9 0, .movz 11 8 0, .madd 9 10 11 9, .addImm 9 9 16]

/-- The scratch's address, `X17 + areaSize cap`, in X20. -/
def scratchAddr (cap : Nat) : List Instr :=
  movImm 20 (UInt64.ofNat (areaSize cap)) ++ [.addReg 20 20 17]

/-- The four `STRB` of the low 32 bits of X`v` at X16 plus 4,092 to 4,095, the lowest first, with
X`t` for the shifted values. -/
def store32 (v t : Fin 32) : List Instr :=
  [.strb v 16 4092, .lsrImm t v 8, .strb t 16 4093, .lsrImm t v 16, .strb t 16 4094,
    .lsrImm t v 24, .strb t 16 4095]

/-- The scan piece placed at `a`, which ends at `after a 15` with the count of the strings of the
vector at X9 in X12 and the sum of their sizes in X13, or branches to `ov` once the sum reaches
`2^32`.  X10 holds `2^32`, X11 walks the vector, X14 a string, and X15 its bytes. -/
def scanPiece (a ov : UInt64) : GenM (List Instr) := do
  return [.orrReg 11 31 9, .movz 12 0 0, .movz 13 0 0, .movz 10 1 2, .ldr 14 11 0,
    .cbz 14 (← cbField (after a 5) (after a 15)), .addImm 11 11 8, .addImm 12 12 1,
    .ldrb 15 14 0, .addImm 14 14 1, .addImm 13 13 1,
    .cbnz 15 (← cbField (after a 11) (after a 8)), .subsReg 31 13 10,
    .bcond 2 (← cbField (after a 13) ov), .b (← bField (after a 14) (after a 4))]

/-- The stub of `args_sizes_get` or `environ_sizes_get` for the vector `v`, placed at `a`, with the
trap stub at `tr` and a memory of `cap` pages: the checks of the count's pointer in X0 and the
size's in X1, the scratch's address, the vector's address, the scan, the stores of the count and
the size, and errno 61 after an overflow. -/
def sizesStub (v : StringVector) (a tr : UInt64) (cap : Nat) : GenM (List Instr) := do
  let n := (vectorStart v).length
  let checks := [.ldr 9 17 0, .addImm 9 9 8, .addImm 10 0 4, .subsReg 31 10 9,
    .bcond 8 (← cbField (after a 4) tr), .addImm 10 1 4, .subsReg 31 10 9,
    .bcond 8 (← cbField (after a 7) tr)]
  let scan ← scanPiece (after a (13 + n)) (after a (48 + n))
  return checks ++ scratchAddr cap ++ vectorStart v ++ scan ++
    [.addReg 16 17 0, .addImm 16 16 4] ++ store32 12 15 ++ [.addReg 16 17 1, .addImm 16 16 4] ++
    store32 13 15 ++ [.movz 0 0 0, .ret 30, .movz 0 61 0, .ret 30]

/-- The stub of `args_get` or `environ_get` for the vector `v`, placed at `a`, with the trap stub at
`tr` and a memory of `cap` pages: the scratch's address, the vector's address, the scan, the checks
of the array at X0 and the buffer at X1, the pass that writes the strings' addresses, which X13
holds, and the pass that copies the strings. -/
def stringsStub (v : StringVector) (a tr : UInt64) (cap : Nat) : GenM (List Instr) := do
  let n := (vectorStart v).length
  let scan ← scanPiece (after a (5 + n)) tr
  let c := 20 + n
  let checks := [.ldr 15 17 0, .addImm 15 15 8, .addReg 14 12 12, .addReg 14 14 14,
    .addReg 14 14 0, .subsReg 31 14 15, .bcond 8 (← cbField (after a (c + 6)) tr),
    .addReg 14 1 13, .subsReg 31 14 15, .bcond 8 (← cbField (after a (c + 9)) tr)]
  let p := 30 + n
  let pointers := [.orrReg 11 31 9, .addReg 16 17 0, .addImm 16 16 4, .orrReg 13 31 1,
    .ldr 14 11 0, .cbz 14 (← cbField (after a (p + 5)) (after a (p + 20))), .addImm 11 11 8] ++
    store32 13 15 ++ [.addImm 16 16 4, .ldrb 15 14 0, .addImm 14 14 1, .addImm 13 13 1,
    .cbnz 15 (← cbField (after a (p + 18)) (after a (p + 15))),
    .b (← bField (after a (p + 19)) (after a (p + 4)))]
  let s := 50 + n
  let copy := [.orrReg 11 31 9, .addReg 16 17 1, .addImm 16 16 4, .ldr 14 11 0,
    .cbz 14 (← cbField (after a (s + 4)) (after a (s + 12))), .addImm 11 11 8, .ldrb 15 14 0,
    .strb 15 16 4092, .addImm 14 14 1, .addImm 16 16 1,
    .cbnz 15 (← cbField (after a (s + 10)) (after a (s + 6))),
    .b (← bField (after a (s + 11)) (after a (s + 3))), .movz 0 0 0, .ret 30]
  return scratchAddr cap ++ vectorStart v ++ scan ++ checks ++ pointers ++ copy

/-- The number of instructions of `sizesStub v`. -/
def sizesStubSize (v : StringVector) : Nat := 50 + (vectorStart v).length

/-- The number of instructions of `stringsStub v`. -/
def stringsStubSize (v : StringVector) : Nat := 64 + (vectorStart v).length

end LeanExe.A64
