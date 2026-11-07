import TestSupport.M7.Nucleo

/-!
The cycle measurements of the Cortex-M7 back end on the NUCLEO-F767ZI, two images apart from the
proved one that `m7-windows` writes and `tests/baremetal/m7-board.sh` runs.  Both enable the cycle
counter alone: DEMCR.TRCENA, the unlock of the DWT through `DWT_LAR`, `DWT_CYCCNT` cleared, and
`DWT_CTRL` with CYCCNTENA set and the enables of the other counters and events, bits 16 to 22,
clear, since erratum 486321 of the Cortex-M7 r1p0 miscounts stall cycles in those counters
(SDEN-1068427).  Both run from the flash's ITCM address, as the proved image does, and both start
with a boot log at `0x2001E000`: a magic word, a count, and for each reset the value of
`RCC_CSR`, whose flags name the reset's causes, which the log then clears with RMVF.

`echoDwt` is the proved echo's program with the call at the loop's head redirected to `meas`,
placed after the program, which reads `DWT_CYCCNT`, records the cycles since its last exit in a
table indexed by the phase before and after the window, and branches to the step, which returns
to the loop as before.  The interval measured runs from the counter's read at the end of `meas`
to its read at the start of the next one, so it holds the window's instructions and five of
`meas`: the store of the counter's value and the branch to the step at its end, and `MOVW`,
`MOVT`, and the load of the counter at its start.  The call of `meas` takes the place of the call
of the step.  The table lies at `0x20000000`: the counter's value at the last exit, the last
phase, and from `0x20000010` 16 entries of eight words, the count, the least, the most, and the
sum of the cycles in two words, the low first, for the phase before times 4 plus the phase
after.

`divDwt` measures `udivmod64`'s paths and `UDIV`.  Each case loads r0 to r3, stores them in its
record, reads the counter, runs its body, reads the counter again, and stores the difference and
r0 to r3 in the record.  A record of ten words from `0x20000010` holds the case's kind times
65,536 plus its number, the cycles, r0 to r3 after the body, and r0 to r3 before it.  A body is a
call of `udivmod64`, a call of a routine that only returns, 16 `UDIV r4, r0, r2`, or 16
`MOV r4, r0`, and the second and the fourth calibrate the first and the third.  Each case runs five times.  At the end
the image writes the number of records at `0x20000004` and `0x600DCAFE` at `0x20000000`.
-/

namespace TestSupport.M7.Dwt

open LeanExe.M7 LeanExe.M7.Nucleo TestSupport.Bare

def demcr : UInt32 := 0xE000EDFC
def dwtCtrl : UInt32 := 0xE0001000
def dwtCyccnt : UInt32 := 0xE0001004
def dwtLar : UInt32 := 0xE0001FB0
def rccCsr : UInt32 := 0x40023874
def res : UInt32 := 0x20000000
def bootLog : UInt32 := 0x2001E000

/-- The cycle counter alone. -/
def dwtOn : List InitOp :=
  [.rmw demcr 0 0x01000000, .write dwtLar 0xC5ACCE55, .write dwtCyccnt 0,
    .rmw dwtCtrl 0x007F0000 1]

/-- The boot log: the count set to 0 unless the magic word is present, `RCC_CSR` stored in entry
`count % 64`, the count advanced, and the reset flags cleared. -/
def bootLogCode : List Instr :=
  movWord 0 bootLog ++ [.ldr 1 0 0] ++ movWord 2 0xB007106E ++
    [.cmpReg 1 2, Instr.bcondTo 0 12, .movImm 3 0, .str 3 0 4, .str 2 0 0, .ldr 3 0 4,
      .andImm 3 3 63] ++ movWord 4 rccCsr ++
    [.ldr 5 4 0, Instr.addLsl 0 6 0 3 2, .str 5 6 8, .movImm 1 1, Instr.addLsl 0 3 3 1 0,
      .str 3 0 4] ++ movWord 1 0x01000000 ++ [.orrReg 0 5 5 1, .str 5 4 0]

/-- The window table's initial contents. -/
def tableOps : List InitOp :=
  [.write res 0, .write (res + 4) 0xFFFFFFFF] ++ (List.range 16).flatMap fun k =>
    let e := res + 16 + 32 * UInt32.ofNat k
    [.write e 0, .write (e + 4) 0xFFFFFFFF, .write (e + 8) 0, .write (e + 12) 0,
      .write (e + 16) 0]

/-- The byte offset of a branch at `here` to `target`. -/
def off (here target : UInt32) : Int := (target.toNat : Int) - (here.toNat + 4)

/-- The halfwords' bytes of instructions. -/
def size (is : List Instr) : Nat := 2 * (is.flatMap encode).length

/-- The measurement at the loop's head, placed at `pos`, which branches to the step at `step`. -/
def meas (pos step : UInt32) : List Instr :=
  let body := movWord 7 dwtCyccnt ++ [.ldr 0 7 0] ++ movWord 6 res ++
    [.ldr 1 6 0, .subReg 0 0 0 1, .ldr 2 6 4, .ldrSp 3 0, .andImm 3 3 255, Instr.lsrBy 4 2 31,
      .cmpImm 4 1, Instr.bcondTo 0 92,
      Instr.lslBy 4 2 2, Instr.addLsl 0 4 4 3 0, Instr.lslBy 4 4 5, Instr.addLsl 0 4 6 4 0,
      .ldr 5 4 16, .movImm 1 1, Instr.addLsl 0 5 5 1 0, .str 5 4 16,
      .ldr 5 4 20, .cmpReg 0 5, Instr.bcondTo 2 4, .str 0 4 20,
      .ldr 5 4 24, .cmpReg 0 5, Instr.bcondTo 9 4, .str 0 4 24,
      .ldr 5 4 28, Instr.addLsl 1 5 5 0 0, .str 5 4 28, .ldr 5 4 32, .movImm 1 0, .adcReg 5 5 1,
      .str 5 4 32,
      .str 3 6 4, .ldr 0 7 0, .str 0 6 0]
  body ++ [Instr.bTo (off (pos + UInt32.ofNat (size body)) step)]

/-- The echo's measurement image. -/
def echoBoot : Boot :=
  { boot with init := initCode init ++ bootLogCode ++ initCode (dwtOn ++ tableOps) }

def echoDwt : GenM (List UInt8) := do
  let B := echoBoot
  let prog ← genProgram reqCompiled.module 9 [3] B.base stackLimit devBase udivmod64
  let pad := if size prog % 4 = 0 then [] else [Instr.bxLr]
  let m := B.base + UInt32.ofNat (size (prog ++ pad))
  let head := after B.base (mainStart [3])
  let step := after B.base (mainSize [3])
  match prog[mainStart [3]]? with
  | some (.bl ..) =>
      let prog' := prog.set (mainStart [3]) (Instr.blTo (off head m))
      return bootBytes B (Instr.bTo (-4) :: B.init ++ prog' ++ pad ++ meas m step)
  | _ => throw "echoDwt: no call at the loop's head"

/-- A case of the division measurements: `kind` 0 calls `udivmod64`, 1 a routine that returns,
2 runs 16 `UDIV r4, r0, r2`, and 3 runs 16 `MOV r4, r0`. -/
structure Case where
  kind : Nat
  n : UInt64
  d : UInt64

def cases : List Case :=
  [⟨1, 0, 1⟩,
    ⟨0, 0x123456789ABCDEF0, 0x100000000⟩, ⟨0, 0xFFFFFFFFFFFFFFFF, 0x100000000⟩,
    ⟨0, 0xFFFFFFFF, 7⟩, ⟨0, 1, 1⟩,
    ⟨0, 5, 0x100000001⟩,
    ⟨0, 0x100000005, 0x100000001⟩, ⟨0, 0x200000000, 0x100000001⟩,
    ⟨0, 0x10000000000, 0x200000001⟩, ⟨0, 0x1000000000000, 0x200000001⟩,
    ⟨0, 0x8000000000000000, 0x100000001⟩, ⟨0, 0xFFFFFFFFFFFFFFFF, 0x80000001⟩,
    ⟨0, 0xFFFFFFFFFFFFFFFF, 1⟩,
    ⟨3, 0xFFFFFFFF, 1⟩,
    ⟨2, 0xFFFFFFFF, 1⟩, ⟨2, 0xFFFFFFFF, 0xFFFFFFFF⟩, ⟨2, 1, 1⟩, ⟨2, 0xFFFFFFFF, 0x10000⟩,
    ⟨2, 0x80000000, 3⟩, ⟨2, 0, 1⟩, ⟨2, 0x12345678, 0x1234⟩]

def passes : Nat := 5

/-- The code of case `c`, number `id`, placed at `pos`, whose record lies at `rec`. -/
def caseCode (c : Case) (id : Nat) (pos rec empty div : UInt32) : List Instr :=
  let tmp := res + 8
  let pre := movWord 0 c.n.toUInt32 ++ movWord 1 (c.n >>> 32).toUInt32 ++
    movWord 2 c.d.toUInt32 ++ movWord 3 (c.d >>> 32).toUInt32 ++ movWord 4 rec ++
    [.str 0 4 24, .str 1 4 28, .str 2 4 32, .str 3 4 36] ++ movWord 7 dwtCyccnt ++
    movWord 5 tmp ++ [.ldr 6 7 0, .str 6 5 0]
  let here := pos + UInt32.ofNat (size pre)
  let body := match c.kind with
    | 0 => [Instr.blTo (off here div)]
    | 1 => [Instr.blTo (off here empty)]
    | 2 => List.replicate 16 (.udiv 4 0 2)
    | _ => List.replicate 16 (Instr.lslBy 4 0 0)
  let post := movWord 7 dwtCyccnt ++ [.ldr 5 7 0] ++ movWord 6 tmp ++
    [.ldr 6 6 0, .subReg 0 5 5 6] ++ movWord 4 rec ++
    [.str 5 4 4, .str 0 4 8, .str 1 4 12, .str 2 4 16, .str 3 4 20] ++
    movWord 5 (UInt32.ofNat (65536 * c.kind + id)) ++ [.str 5 4 0]
  pre ++ body ++ post

/-- The cases' code from `pos`, each `passes` times, with their records from `0x20000010`. -/
def casesCode (empty div : UInt32) : UInt32 → Nat → List (Nat × Case) → List Instr
  | _, _, [] => []
  | pos, k, (id, c) :: rest =>
      let is := caseCode c id pos (res + 16 + 40 * UInt32.ofNat k) empty div
      is ++ casesCode empty div (pos + UInt32.ofNat (size is)) (k + 1) rest

def runs : List (Nat × Case) :=
  (List.range passes).flatMap fun _ => (List.range cases.length).zip cases

def divBoot : Boot :=
  { org := flashItcm, entries := 126, sp := stackTop, init := bootLogCode ++ initCode dwtOn }

def divDwt : List UInt8 :=
  let B := divBoot
  let start := B.base
  let fin := movWord 0 res ++ movWord 1 (UInt32.ofNat runs.length) ++ [.str 1 0 4] ++
    movWord 1 0x600DCAFE ++ [.str 1 0 0, Instr.bTo (-4)]
  let body0 := casesCode 0 0 start 0 runs
  let empty := start + UInt32.ofNat (size body0 + size fin)
  let div := empty + 4
  let body := casesCode empty div start 0 runs
  bootBytes B (Instr.bTo (-4) :: B.init ++ body ++ fin ++ [.bxLr, .bxLr] ++ udivmod64)

end TestSupport.M7.Dwt
