import TestSupport.M7.Asm
import LeanExe.M7.Div

/-!
The co-simulation of the Cortex-M7 model of `LeanExe/M7/Machine.lean` against QEMU's `mps2-an500`,
whose processor is an emulated Cortex-M7.  `harness` writes an assembly file of cases, each an
instruction of one of the model's forms with a state drawn from SplitMix64: r0 to r12, SP, LR, the
flags, and a window of 64 bytes of memory.  The file's `main` runs every case under the startup
code of `tools/baremetal/armv7m/start.S` and then calls `cosim_print` of
`tests/baremetal/m7cosim.c`, which prints each case's state before and after its instruction.

A case copies its window into `cosim_win`, adds the window's address to the table entries of the
registers that address memory, sets LR for `BX LR` to the address of a landing word with bit 0
set, loads the state with `MSR APSR_nzcvq`, `MOV SP`, `LDR LR`, and `LDM`, and branches to its
instruction, the halfwords that `encode` gives.  The 16 words on each side of the instruction branch
to landing code that records which word execution reached, so a case observes the program
counter after a branch as well as after any other instruction.  The landing code saves the
registers in the floating-point registers S0 to S16, which no form of the model uses, and then
stores them, APSR, and the window in the case's output.  `check` reads the printed lines, runs
`exec` on each printed state before the instruction, with the instruction's address as the program
counter and the window as the only Normal memory, and compares the result with the printed state
after it.

The harness also holds one copy of `udivmod64` and division cases that call it with `BL`: the
boundary dividends and divisors 0, 1, 2^32 - 1, 2^32, 2^63, and 2^64 - 1 in every combination with
a nonzero divisor, then random pairs.  A case loads r0 to r12, SP, and the flags, with the dividend
in r0 and r1 and the divisor in r2 and r3, and saves the state at the return address as an
instruction case does.  `checkDivLine` runs the model's `step` from the printed state before the
call, with LR at the return address and the routine's halfwords as the only code, until the
program counter reaches the return address, on a platform without Normal memory or devices, so
that any memory access stops the model.  It compares the registers and flags with the printed state
after the call, compares the four result words with Lean's `/` and `%` of `UInt64`, and compares
the number of instructions executed with the count for the case's path.

The seeded cases draw their immediate fields at random, so they may miss a value that the
generated code contains.  The fixed cases of `fixedForms` follow them: each sets one immediate
field, offset, condition, or branch direction that `LeanExe/M7/Gen.lean` and `LeanExe/M7/Div.lean`
emit in the state of a case of its form, and the case lines of the fixed cases are checked as the
others are.  The board's co-simulation of `tests/TestSupport/M7/BoardCosim.lean` runs the same
fixed cases.
-/

namespace TestSupport.M7

open LeanExe.M7

/-- The state of SplitMix64. -/
structure Rng where
  s : UInt64

/-- The next output of SplitMix64 and the next state. -/
def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.s + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

abbrev Gen := StateM Rng

def word64 : Gen UInt64 := modifyGet fun r => r.next

def word : Gen UInt32 := do return (← word64).toUInt32

def below (n : Nat) : Gen Nat := do
  return (← word64).toNat % n

def fin (n : Nat) (h : 0 < n := by decide) : Gen (Fin n) := do
  return ⟨(← below n) % n, Nat.mod_lt _ h⟩

/-- A register value, with the boundary values of signed and unsigned arithmetic weighted. -/
def value : Gen UInt32 := do
  match ← below 10 with
  | 0 => return 0
  | 1 => return 1
  | 2 => return 0xFFFFFFFF
  | 3 => return 0x80000000
  | 4 => return 0x7FFFFFFF
  | 5 => return 0xFFFF
  | 6 => return (← word) &&& 0xFF
  | _ => word

/-- A shift amount for a shift by register, whose bottom byte lies below 64, at 32, or at 255,
or is random. -/
def shiftValue : Gen UInt32 := do
  match ← below 6 with
  | 0 => return UInt32.ofNat (← below 64)
  | 1 => return 32
  | 2 => return 255
  | 3 => return ((← word) &&& 0xFFFFFF00) ||| UInt32.ofNat (← below 40)
  | 4 => return 256 + UInt32.ofNat (← below 64)
  | _ => word

/-- The words on each side of a case's instruction that branch to landing code. -/
def padRange : Nat := 16

/-- A branch's word offset, from -16 to 16 without 0. -/
def offset : Gen Int := do
  let k ← below (2 * padRange)
  return if k < padRange then Int.ofNat k - padRange else Int.ofNat k - padRange + 1

/-- The bytes of the memory window. -/
def windowSize : Nat := 64

/-- A case: the instruction, r0 to r12, SP, LR, and APSR with NZCV in bits 31 to 28, and the
window's bytes, before the harness's changes; the table entries, 0 to 12 for the registers and 13
for SP, to which the harness adds the window's address; and the word offset of a landing word whose
address plus 1 the harness puts in LR. -/
structure Case where
  instr : Instr
  regs : Array UInt32
  sp : UInt32
  lr : UInt32
  apsr : UInt32
  win : Array UInt8
  relWin : List Nat := []
  relPad : Option Int := none

/-- The forms of `Instr`, all of which the co-simulation covers, in the order of `Instr`. -/
def formCount : Nat := 39

/-- The value that puts an access of the window at `o` at `delta` from the base: `o - delta`. -/
def rel (o delta : Nat) : UInt32 := UInt32.ofNat o - UInt32.ofNat delta

/-- A case of form `form`, whose state makes the instruction run without stopping the model. -/
def genCase (form : Nat) : Gen Case := do
  let mut regs := #[]
  for _ in [0:13] do
    regs := regs.push (← value)
  let sp := (← value) &&& 0xFFFFFFFC
  let lr ← value
  let apsr := ((← word) >>> 28) <<< 28
  let mut win := #[]
  for _ in [0:windowSize] do
    win := win.push (← word).toUInt8
  let c : Case := { instr := .dsb, regs, sp, lr, apsr, win }
  match form with
  | 0 =>
      return { c with instr := .addReg (← fin 2) (← fin 8) (← fin 8) (← fin 8) (← fin 8) (← fin 4) }
  | 1 => return { c with instr := .adcReg (← fin 8) (← fin 8) (← fin 8) }
  | 2 => return { c with instr := .subReg (← fin 2) (← fin 8) (← fin 8) (← fin 8) }
  | 3 => return { c with instr := .sbcReg (← fin 2) (← fin 8) (← fin 8) (← fin 8) }
  | 4 => return { c with instr := .andReg (← fin 8) (← fin 8) (← fin 8) }
  | 5 => return { c with instr := .orrReg (← fin 2) (← fin 8) (← fin 8) (← fin 8) }
  | 6 => return { c with instr := .eorReg (← fin 8) (← fin 8) (← fin 8) }
  | 7 => return { c with instr := .cmpReg (← fin 8) (← fin 8) }
  | 8 | 9 =>
      let d ← fin 8
      let n ← fin 8
      let m ← fin 8
      let instr := if form = 8 then Instr.lslReg d n m else Instr.lsrReg d n m
      return { c with instr, regs := c.regs.set! m.val (← shiftValue) }
  | 10 => return { c with instr := .lslImm (← fin 8) (← fin 8) (← fin 8) (← fin 4) }
  | 11 => return { c with instr := .lsrImm (← fin 8) (← fin 8) (← fin 8) (← fin 4) }
  | 12 => return { c with instr := .subImm (← fin 8) (← fin 8) (← fin 256) }
  | 13 => return { c with instr := .andImm (← fin 8) (← fin 8) (← fin 256) }
  | 14 => return { c with instr := .eorImm (← fin 8) (← fin 8) (← fin 256) }
  | 15 => return { c with instr := .cmpImm (← fin 8) (← fin 256) }
  | 16 => return { c with instr := .movImm (← fin 8) (← fin 256) }
  | 17 => return { c with instr := .movw (← fin 8) (← fin 16) (← fin 2) (← fin 8) (← fin 256) }
  | 18 => return { c with instr := .movt (← fin 8) (← fin 16) (← fin 2) (← fin 8) (← fin 256) }
  | 19 => return { c with instr := .addwSp (← fin 8) (← fin 2) (← fin 8) (← fin 256) }
  | 20 => return { c with instr := .subwSp (← fin 8) (← fin 2) (← fin 8) (← fin 256) }
  | 21 => return { c with instr := .addwSpSp (← fin 2) (← fin 8) (← fin 256) }
  | 22 => return { c with instr := .subwSpSp (← fin 2) (← fin 8) (← fin 256) }
  | 23 => return { c with instr := .clz (← fin 8) (← fin 8) }
  | 24 => return { c with instr := umullOf (← fin 8) (← fin 8) (← fin 8) (← fin 8) }
  | 25 => return { c with instr := .mla (← fin 8) (← fin 8) (← fin 8) (← fin 8) }
  | 26 => return { c with instr := .mls (← fin 8) (← fin 8) (← fin 8) (← fin 8) }
  | 27 =>
      let d ← fin 8
      let n ← fin 8
      let m ← fin 8
      let nonzero := (← word) ||| 1
      return { c with
        instr := .udiv d n m
        regs := if c.regs[m.val]! = 0 then c.regs.set! m.val nonzero else c.regs }
  | 28 | 29 =>
      let t ← fin 8
      let n ← fin 8
      let imm ← fin 4096
      let o := 4 * (← below (windowSize / 4))
      let instr := if form = 28 then Instr.ldr t n imm else Instr.str t n imm
      return { c with instr, regs := c.regs.set! n.val (rel o imm.val), relWin := [n.val] }
  | 30 | 31 | 32 | 33 =>
      let t ← fin 8
      let imm := field 4096 (4 * (← below 1024))
      let o := 4 * (← below (windowSize / 4))
      let instr := match form with
        | 30 => Instr.ldrSp t imm
        | 31 => Instr.strSp t imm
        | 32 => Instr.ldrLr imm
        | _ => Instr.strLr imm
      return { c with instr, sp := rel o imm.val, relWin := [13] }
  | 34 => return { c with instr := Instr.bcondTo (← fin 14) (4 * (← offset) - 4) }
  | 35 => return { c with instr := Instr.bTo (4 * (← offset) - 4) }
  | 36 => return { c with instr := Instr.blTo (4 * (← offset) - 4) }
  | 37 => return { c with instr := .bxLr, relPad := some (← offset) }
  | _ => return c

def hex (v : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 v)

/-- The pads' numbers: 0 to 32 without 16, the instruction's place.  Pad `p` lies at the
instruction's address plus `4 * (p - 16)`. -/
def padIds : List Nat := (List.range (2 * padRange + 1)).filter (· ≠ padRange)

/-- The assembly of case `k`: its code, its initialized data, and its output area. -/
def caseAsm (k : Nat) (c : Case) : List String × List String × List String :=
  let l (s : String) := s!"m7c{k}_{s}"
  let pad (p : Nat) := l s!"p{p}"
  let patches := c.relWin.flatMap fun r =>
    ["  ldr r0, =cosim_win", s!"  ldr r1, [r4, #{4 * r}]", "  add r1, r1, r0",
      s!"  str r1, [r4, #{4 * r}]"]
  let padPatch := match c.relPad with
    | some j =>
        [s!"  ldr r0, ={pad (Int.toNat (j + padRange))}", "  orr r0, r0, #1", "  str r0, [r4, #56]"]
    | none => []
  let e := encode c.instr
  let body := match e with
    | [h1, h2] => [s!"{l "test"}: .inst.w {hex (h1.toNat * 65536 + h2.toNat)}"]
    | _ => [s!"{l "test"}: .inst.n {hex (e.headD 0).toNat}", "  .inst.n 0xbf00"]
  let code :=
    [s!"{l "start"}:", s!"  ldr r0, ={l "win"}", "  ldr r1, =cosim_win",
      s!"  movs r2, #{windowSize}", "1:", "  ldrb r3, [r0], #1", "  strb r3, [r1], #1", "  subs r2, r2, #1", "  bne 1b",
      s!"  ldr r0, ={l "out"}", "  ldr r1, =cosim_cur", "  str r0, [r1]", s!"  ldr r0, ={l "end"}",
      "  ldr r1, =cosim_next", "  str r0, [r1]", s!"  ldr r4, ={l "in"}"] ++ patches ++ padPatch ++
    ["  ldr r0, [r4, #60]", "  msr APSR_nzcvq, r0", "  ldr r0, [r4, #52]", "  mov sp, r0",
      "  ldr lr, [r4, #56]", "  ldm.w r4, {r0-r12}", s!"  b.w {l "test"}", "  .ltorg"] ++
    ((List.range padRange).map fun p => s!"{pad p}: b.w cosim_l{p}") ++ body ++
    ((List.range padRange).map fun i =>
      let p := padRange + 1 + i
      s!"{pad p}: b.w cosim_l{p}") ++
    [s!"{l "end"}:"]
  let data :=
    ["  .balign 4", s!"{l "in"}:"] ++
    ((c.regs.toList ++ [c.sp, c.lr, c.apsr]).map fun v => s!"  .word {hex v.toNat}") ++
    [s!"{l "win"}:", "  .byte " ++ ", ".intercalate (c.win.toList.map fun b => hex b.toNat)]
  let bss := ["  .balign 4", s!"{l "out"}:", s!"  .skip {68 + windowSize}"]
  (code, data, bss)

/-- The landing code of every pad and the code that saves a case's state and resumes at the
address in `cosim_next`. -/
def landing : List String :=
  (padIds.flatMap fun p =>
    [s!"cosim_l{p}:", "  vmov s0, r0", s!"  movw r0, #{p}", "  vmov s16, r0",
      "  b.w cosim_save"]) ++
  ["cosim_save:"] ++ ((List.range 12).map fun r => s!"  vmov s{r + 1}, r{r + 1}") ++
  ["  mov r0, sp", "  vmov s13, r0", "  vmov s14, lr", "  mrs r0, apsr", "  vmov s15, r0",
    "  ldr r0, =cosim_cur", "  ldr r0, [r0]", "  vstmia r0!, {s0-s16}", "  ldr r1, =cosim_win",
    s!"  movs r2, #{windowSize}", "1:", "  ldrb r3, [r1], #1", "  strb r3, [r0], #1",
    "  subs r2, r2, #1", "  bne 1b", "  ldr r0, =cosim_sp", "  ldr r0, [r0]", "  mov sp, r0",
    "  ldr r0, =cosim_next", "  ldr r0, [r0]", "  orr r0, r0, #1", "  bx r0", "  .ltorg"]

/-- The boundary values of the division cases. -/
def boundaries : Array UInt64 :=
  #[0, 1, 0xFFFFFFFF, 0x100000000, 0x8000000000000000, 0xFFFFFFFFFFFFFFFF]

/-- A 64-bit operand: a boundary value or a value near one, a random word of 64 or of 32 bits, a
random word shifted right by a random amount, or a random high word above a low word of 0. -/
def value64 : Gen UInt64 := do
  match ← below 7 with
  | 0 => return boundaries[← below boundaries.size]!
  | 1 => return boundaries[← below boundaries.size]! + UInt64.ofNat (← below 3) - 1
  | 2 => return (← word64) &&& 0xFFFFFFFF
  | 3 => return (← word64) <<< 32
  | 4 | 5 => return (← word64) >>> UInt64.ofNat (← below 64)
  | _ => word64

/-- A division case: the dividend, the divisor, r0 to r12 with the operands in r0 to r3, SP, and
APSR with NZCV in bits 31 to 28. -/
structure DivCase where
  n : UInt64
  d : UInt64
  regs : Array UInt32
  sp : UInt32
  apsr : UInt32

def genDiv (n d : UInt64) : Gen DivCase := do
  let mut regs := #[n.toUInt32, (n >>> 32).toUInt32, d.toUInt32, (d >>> 32).toUInt32]
  for _ in [4:13] do
    regs := regs.push (← value)
  let sp := (← value) &&& 0xFFFFFFFC
  let apsr := ((← word) >>> 28) <<< 28
  return { n, d, regs, sp, apsr }

/-- The operands of the division cases: every boundary dividend with every nonzero boundary
divisor, then `count` random pairs, each nonzero divisor drawn again when it is 0. -/
def divOperands (count : Nat) : Gen (Array (UInt64 × UInt64)) := do
  let mut out := #[]
  for n in boundaries do
    for d in boundaries do
      if d ≠ 0 then out := out.push (n, d)
  for _ in [0:count] do
    let n ← value64
    let mut d ← value64
    while d = 0 do
      d ← value64
    out := out.push (n, d)
  return out

/-- The assembly of division case `k`: its code, its initialized data, and its output area. -/
def divAsm (k : Nat) (c : DivCase) : List String × List String × List String :=
  let l (s : String) := s!"m7d{k}_{s}"
  let code :=
    [s!"{l "start"}:", s!"  ldr r0, ={l "out"}", "  ldr r1, =cosim_cur", "  str r0, [r1]",
      s!"  ldr r0, ={l "end"}", "  ldr r1, =cosim_next", "  str r0, [r1]",
      s!"  ldr r4, ={l "in"}", "  ldr r0, [r4, #60]", "  msr APSR_nzcvq, r0",
      "  ldr r0, [r4, #52]", "  mov sp, r0", "  ldm.w r4, {r0-r12}", "  bl m7_udivmod64",
      s!"{l "ret"}:", "  vmov s0, r0", "  movw r0, #0", "  vmov s16, r0", "  b.w cosim_save",
      "  .ltorg", s!"{l "end"}:"]
  let data :=
    ["  .balign 4", s!"{l "in"}:"] ++
    ((c.regs.toList ++ [c.sp, 0, c.apsr]).map fun v => s!"  .word {hex v.toNat}")
  let bss := ["  .balign 4", s!"{l "out"}:", s!"  .skip {68 + windowSize}"]
  (code, data, bss)

/-- The routine's code: its halfwords from `encode`, from an address that is a multiple of 4. -/
def routineAsm : List String :=
  ["  .balign 4", "  .global m7_udivmod64", "  .type m7_udivmod64, %function", "  .thumb_func",
    "m7_udivmod64:"] ++
  udivmod64.map fun i => match encode i with
    | [h1, h2] => s!"  .inst.w {hex (h1.toNat * 65536 + h2.toNat)}"
    | e => s!"  .inst.n {hex (e.headD 0).toNat}"

/-- A fixed case: its name, the form whose case gives its state, and the change of that case's
instruction to an instance that the generated code contains, or `none` when the form's
instruction has another constructor. -/
structure Fixed where
  name : String
  form : Nat
  set : Case → Gen (Option Case)

/-- The instruction `f i` in place of the case's instruction `i`. -/
def instrTo (f : Instr → Option Instr) (c : Case) : Gen (Option Case) :=
  pure ((f c.instr).map fun i => { c with instr := i })

/-- The shift by the immediate `k` of `LSL.W` or `LSR.W`. -/
def shiftBy (k : Nat) : Instr → Option Instr
  | .lslImm d m _ _ => some (Instr.lslBy d m k)
  | .lsrImm d m _ _ => some (Instr.lsrBy d m k)
  | _ => none

/-- `ADD{S}.W` with the S bit `s` and the shift `k`. -/
def addShift (s : Fin 2) (k : Nat) : Instr → Option Instr
  | .addReg _ d n m _ _ => some (Instr.addLsl s d n m k)
  | _ => none

/-- The S bit `s` of `SUB{S}.W`, `SBC{S}.W`, or `ORR{S}.W`. -/
def withS (s : Fin 2) : Instr → Option Instr
  | .subReg _ d n m => some (.subReg s d n m)
  | .sbcReg _ d n m => some (.sbcReg s d n m)
  | .orrReg _ d n m => some (.orrReg s d n m)
  | _ => none

/-- The 8-bit immediate `v` of `MOV.W`, `CMP.W`, `SUB.W`, `AND.W`, or `EOR.W`. -/
def imm8 (v : Fin 256) : Instr → Option Instr
  | .movImm d _ => some (.movImm d v)
  | .cmpImm n _ => some (.cmpImm n v)
  | .subImm d n _ => some (.subImm d n v)
  | .andImm d n _ => some (.andImm d n v)
  | .eorImm d n _ => some (.eorImm d n v)
  | _ => none

/-- The 16-bit immediate `v` of `MOVW` or `MOVT`. -/
def imm16Of (v : Nat) : Instr → Option Instr
  | .movw d .. => some (Instr.movwOf d v)
  | .movt d .. => some (Instr.movtOf d v)
  | _ => none

/-- The 12-bit immediate `v` of `SUBW Rd, SP`, `ADDW SP, SP`, or `SUBW SP, SP`. -/
def imm12Of (v : Nat) : Instr → Option Instr
  | .subwSp d .. => some (Instr.subwSpOf d v)
  | .addwSpSp .. => some (Instr.addwSpSpOf v)
  | .subwSpSp .. => some (Instr.subwSpSpOf v)
  | _ => none

/-- The offset `v` of an SP-relative load or store, with SP moved so that the access reaches the
same word of the window. -/
def spOffset (v : Nat) (c : Case) : Gen (Option Case) :=
  let w := field 4096 v
  let move (i : Instr) (old : Fin 4096) : Option Case :=
    some { c with instr := i, sp := c.sp + UInt32.ofNat old.val - UInt32.ofNat v }
  pure <| match c.instr with
    | .ldrSp t imm => move (.ldrSp t w) imm
    | .strSp t imm => move (.strSp t w) imm
    | .ldrLr imm => move (.ldrLr w) imm
    | .strLr imm => move (.strLr w) imm
    | _ => none

/-- The offset `v` of a load or store at a register, with the base register moved so that the
access reaches the same word of the window. -/
def regOffset (v : Nat) (c : Case) : Gen (Option Case) :=
  let w := field 4096 v
  let move (i : Instr) (n : Fin 8) (old : Fin 4096) : Option Case :=
    some { c with instr := i, regs := c.regs.set! n.val (c.regs[n.val]! + UInt32.ofNat old.val -
      UInt32.ofNat v) }
  pure <| match c.instr with
    | .ldr t n imm => move (.ldr t n w) n imm
    | .str t n imm => move (.str t n w) n imm
    | _ => none

/-- A branch `mk` to a random pad after the instruction when `fwd` holds, and before it otherwise. -/
def branchPad (fwd : Bool) (mk : Int → Instr) (c : Case) : Gen (Option Case) := do
  let k := Int.ofNat ((← below padRange) + 1)
  return some { c with instr := mk (4 * (if fwd then k else -k) - 4) }

/-- The direction of a branch in a fixed case's name. -/
def dir (fwd : Bool) : String := if fwd then "forward" else "backward"

/-- The change `f` with the flags NZCV set to `nzcv`. -/
def withFlags (nzcv : UInt32) (f : Case → Gen (Option Case)) (c : Case) : Gen (Option Case) := do
  return (← f c).map fun c => { c with apsr := nzcv <<< 28 }

/-- The instances of the immediate fields of the model's forms that `LeanExe/M7/Gen.lean`,
`LeanExe/M7/Setup.lean`, and `LeanExe/M7/Div.lean` emit: the shifts by an immediate, `LSL #0` and
`#16` and `LSR #1`, `#5`, `#16`, and `#31`; `ADD` and `ADDS` with no shift and `ADD` with `LSL #1`,
`#2`, and `#31`; both S bits of `SUB`, `SBC`, and `ORR`; the 8-bit immediates `MOV #0`, `#4`, and
`#32`, `CMP #0`, `SUB #1` and `#32`, `AND #63`, and `EOR #1`; `MOVW` and `MOVT` at the ends of their
range, `MOVT` of the stack's limit and of the device window, and `MOVW` and `MOVT` of the area's
header, of its memory, and of its end; the frame sizes of `SUBW Rd, SP` and `ADDW` and
`SUBW SP, SP`, multiples of 8 from 8 to 4088, at both ends; the SP-relative offsets, multiples of 4
from 0 to 4092 and LR's from 0 to 4080, at both ends; the offsets of a load or store at a register,
multiples of 4 from 0 to 4092, at both ends; the conditions EQ, NE, CS, CC, and HI; every branch
both forward and backward; and HI and CS with the flags that take each and those that do not. -/
def fixedForms : List Fixed :=
  [Fixed.mk "lslImm #0" 10 (instrTo (shiftBy 0)),
    Fixed.mk "lslImm #16" 10 (instrTo (shiftBy 16))] ++
  ([1, 5, 16, 31].map fun k => Fixed.mk s!"lsrImm #{k}" 11 (instrTo (shiftBy k))) ++
  ([((1 : Fin 2), 0), (0, 0), (0, 1), (0, 2), (0, 31)].map fun (s, k) =>
    Fixed.mk s!"addReg s{s.val} #{k}" 0 (instrTo (addShift s k))) ++
  ([("subReg", 2), ("sbcReg", 3), ("orrReg", 5)].flatMap fun (nm, f) =>
    [(0 : Fin 2), 1].map fun s => Fixed.mk s!"{nm} s{s.val}" f (instrTo (withS s))) ++
  ([("movImm", 16, (0 : Fin 256)), ("movImm", 16, 4), ("movImm", 16, 32), ("cmpImm", 15, 0),
      ("subImm", 12, 1), ("subImm", 12, 32), ("andImm", 13, 63), ("eorImm", 14, 1)].map
    fun (nm, f, v) =>
    Fixed.mk s!"{nm} #{v.val}" f (instrTo (imm8 v))) ++
  ([("movw", 17, 0), ("movw", 17, 65535), ("movt", 18, 0x2000), ("movt", 18, 0x4000),
      ("movt", 18, 65535), ("movw", 17, 0x1000), ("movt", 18, 0x2001)].map fun (nm, f, v) =>
    Fixed.mk s!"{nm} #{v}" f (instrTo (imm16Of v))) ++
  ([("subwSp", 20), ("addwSpSp", 21), ("subwSpSp", 22)].flatMap fun (nm, f) =>
    [8, 4088].map fun v => Fixed.mk s!"{nm} #{v}" f (instrTo (imm12Of v))) ++
  ([("ldrSp", 30, 4092), ("strSp", 31, 4092), ("ldrLr", 32, 4080), ("strLr", 33, 4080)].flatMap
    fun (nm, f, top) => [0, top].map fun v => Fixed.mk s!"{nm} #{v}" f (spOffset v)) ++
  ([("ldr", 28), ("str", 29)].flatMap fun (nm, f) =>
    [0, 4092].map fun v => Fixed.mk s!"{nm} #{v}" f (regOffset v)) ++
  ([("eq", (0 : Fin 14)), ("ne", 1), ("cs", 2), ("cc", 3), ("hi", 8)].flatMap fun (nm, cond) =>
    [true, false].map fun fwd =>
      Fixed.mk s!"bcond {nm} {dir fwd}" 34 (branchPad fwd (Instr.bcondTo cond))) ++
  ([("b", 35, Instr.bTo), ("bl", 36, Instr.blTo)].flatMap fun (nm, f, mk) =>
    [true, false].map fun fwd => Fixed.mk s!"{nm} {dir fwd}" f (branchPad fwd mk)) ++
  ([("hi", (8 : Fin 14), 0x2, "taken"), ("hi", 8, 0x0, "C clear"), ("hi", 8, 0x6, "Z set"),
      ("cs", 2, 0x2, "taken"), ("cs", 2, 0x0, "C clear")].map fun (nm, cond, nzcv, what) =>
    Fixed.mk s!"bcond {nm} {what}" 34
      (withFlags nzcv (branchPad true (Instr.bcondTo cond))))

/-- The fixed cases of `fixedForms` from the generator's state `rng`: each with the state of a case
of its form, and none when the change does not fit the form. -/
def fixedCases (rng : Rng) : Array (Option Case) × Rng := Id.run do
  let mut rng := rng
  let mut out := #[]
  for x in fixedForms do
    let (c, r) := (do x.set (← genCase x.form)).run rng
    rng := r
    out := out.push c
  return (out, rng)

/-- The harness of `perForm` cases of each form, of the division cases with `divCount` random
pairs, and of the fixed cases, from the seed `seed`.  The fixed cases follow the seeded ones in
the numbering, and their states continue the sequence after the division cases, so the seeded
cases and the division cases stay those of a harness without them. -/
def harness (seed : UInt64) (perForm divCount : Nat) : String := Id.run do
  let mut rng : Rng := ⟨seed⟩
  let mut cases := #[]
  for form in [0:formCount] do
    for _ in [0:perForm] do
      let (c, r) := (genCase form).run rng
      rng := r
      cases := cases.push c
  let (ops, r) := (divOperands divCount).run rng
  rng := r
  let mut divs := #[]
  for (n, d) in ops do
    let (c, r) := (genDiv n d).run rng
    rng := r
    divs := divs.push c
  let (fx, _) := fixedCases rng
  cases := cases ++ fx.filterMap id
  let parts := cases.toList.zipIdx.map fun (c, k) => caseAsm k c
  let dparts := divs.toList.zipIdx.map fun (c, k) => divAsm k c
  let n := cases.size
  let table (name suffix : String) :=
    ["  .balign 4", s!"  .global {name}", s!"{name}:"] ++
      (List.range n).map fun k => s!"  .word m7c{k}_{suffix}"
  let dtable (name suffix : String) :=
    ["  .balign 4", s!"  .global {name}", s!"{name}:"] ++
      (List.range divs.size).map fun k => s!"  .word m7d{k}_{suffix}"
  let lines :=
    ["  .syntax unified", "  .arch armv7e-m", "  .fpu fpv5-d16",
      "  .eabi_attribute Tag_ABI_VFP_args, 1", "  .thumb", "  .text", "  .global main",
      "  .type main, %function", "  .thumb_func", "main:", "  push {r4-r11, lr}", "  vpush {s16}",
      "  ldr r0, =cosim_sp", "  mov r1, sp", "  str r1, [r0]"] ++
    parts.flatMap (·.1) ++ dparts.flatMap (·.1) ++
    ["  vpop {s16}", "  pop {r4-r11, lr}", "  b.w cosim_print"] ++ landing ++ routineAsm ++
    ["  .data"] ++ parts.flatMap (·.2.1) ++ dparts.flatMap (·.2.1) ++
    ["  .bss", "  .balign 8", "  .global cosim_win", "cosim_win:", s!"  .skip {windowSize}",
      "cosim_sp:", "  .skip 4", "cosim_cur:", "  .skip 4", "cosim_next:", "  .skip 4"] ++
    parts.flatMap (·.2.2) ++ dparts.flatMap (·.2.2) ++
    ["  .section .rodata", "  .balign 4", "  .global cosim_count", "cosim_count:",
      s!"  .word {n}", "  .global cosim_dcount", "cosim_dcount:", s!"  .word {divs.size}",
      "  .global cosim_udiv", "cosim_udiv:", "  .word m7_udivmod64"] ++
    table "cosim_in" "in" ++ table "cosim_out" "out" ++ table "cosim_inwin" "win" ++
    table "cosim_test" "test" ++ dtable "cosim_din" "in" ++ dtable "cosim_dout" "out" ++
    dtable "cosim_dret" "ret" ++ ["  .section .note.GNU-stack, \"\", %progbits"]
  return "\n".intercalate lines ++ "\n"

/-- The value of a hexadecimal numeral without a prefix. -/
def parseHex (s : String) : Option Nat :=
  s.foldl (fun acc ch => acc.bind fun v =>
    if '0' ≤ ch ∧ ch ≤ '9' then some (16 * v + (ch.toNat - '0'.toNat))
    else if 'a' ≤ ch ∧ ch ≤ 'f' then some (16 * v + (ch.toNat - 'a'.toNat + 10))
    else none) (if s.isEmpty then none else some 0)

/-- The bytes of a hexadecimal string, two digits each. -/
def parseBytes (s : String) : Option (Array UInt8) := do
  let cs := s.toList
  if cs.length % 2 ≠ 0 then none
  let mut out := #[]
  for i in [0:cs.length / 2] do
    out := out.push (← parseHex (String.ofList [cs[2 * i]!, cs[2 * i + 1]!])).toUInt8
  return out

/-- The form of the instruction of a printed line and the differences between the model's state
after it and the printed state after it, or the reason that the line cannot be checked.  A line
holds "C", the case's number, the instruction's two halfwords, its address, the window's address,
r0 to r12, SP, LR, and APSR before the instruction, the window's bytes before it, the same
registers after it followed by the number of the landing word, and the window's bytes after it. -/
def checkLine (line : String) : Except String (String × List String) := do
  let toks := (line.splitOn " ").filter (· ≠ "") |>.toArray
  if toks.size ≠ 41 then throw s!"a line of {toks.size} fields"
  let num (i : Nat) : Except String Nat :=
    match parseHex toks[i]! with
    | some v => pure v
    | none => throw s!"field {i}, {toks[i]!}, is not hexadecimal"
  let hw1 ← num 2
  let hw2 ← num 3
  let p := UInt32.ofNat (← num 4)
  let winAddr := UInt32.ofNat (← num 5)
  let inRegs ← (List.range 16).mapM fun i => do return UInt32.ofNat (← num (6 + i))
  let inWin ← match parseBytes toks[22]! with
    | some b => pure b
    | none => throw "the window before is not hexadecimal"
  let outRegs ← (List.range 17).mapM fun i => do return UInt32.ofNat (← num (23 + i))
  let outWin ← match parseBytes toks[40]! with
    | some b => pure b
    | none => throw "the window after is not hexadecimal"
  let instr ← match decode [UInt16.ofNat hw1, UInt16.ofNat hw2] with
    | some (i, _) => pure i
    | none => throw s!"the halfwords {hex hw1} {hex hw2} decode to no form"
  let apsr := inRegs[15]!
  let s : State :=
    { regs := fun r => inRegs[r.val]!, sp := inRegs[13]!, lr := inRegs[14]!, pc := p,
      nFlag := (apsr >>> 31) &&& 1 == 1, zFlag := (apsr >>> 30) &&& 1 == 1,
      cFlag := (apsr >>> 29) &&& 1 == 1, vFlag := (apsr >>> 28) &&& 1 == 1,
      mem := fun a => if a - winAddr < UInt32.ofNat windowSize then inWin[(a - winAddr).toNat]!
        else 0,
      trace := [], reads := 0 }
  let plat : Platform :=
    { normal := fun a => a - winAddr < UInt32.ofNat windowSize, device := fun _ => false }
  match exec plat (fun _ => 0) instr s with
  | none => return (formName instr, [s!"{asm instr}: the model stops"])
  | some t =>
      let regDiffs := (List.range 13).filterMap fun r =>
        let want := t.regs ⟨r % 13, Nat.mod_lt _ (by decide)⟩
        if want = outRegs[r]! then none
        else some s!"r{r} {hex outRegs[r]!.toNat}, model {hex want.toNat}"
      let flags := (if t.nFlag then 8 else 0) + (if t.zFlag then 4 else 0) +
        (if t.cFlag then 2 else 0) + (if t.vFlag then 1 else 0)
      let landed := p + (4 : UInt32) * outRegs[16]! - UInt32.ofNat (4 * padRange)
      let winDiffs := (List.range windowSize).filterMap fun i =>
        let want := t.mem (winAddr + UInt32.ofNat i)
        if want = outWin[i]! then none
        else some s!"byte {i} {hex outWin[i]!.toNat}, model {hex want.toNat}"
      let diffs := regDiffs ++
        (if t.sp = outRegs[13]! then [] else
          [s!"sp {hex outRegs[13]!.toNat}, model {hex t.sp.toNat}"]) ++
        (if t.lr = outRegs[14]! then [] else
          [s!"lr {hex outRegs[14]!.toNat}, model {hex t.lr.toNat}"]) ++
        (if UInt32.ofNat flags = outRegs[15]! >>> 28 then [] else
          [s!"nzcv {hex (outRegs[15]! >>> 28).toNat}, model {hex flags}"]) ++
        (if t.pc = landed then [] else
          [s!"pc {hex landed.toNat}, model {hex t.pc.toNat}"]) ++
        winDiffs
      return (formName instr, diffs.map (s!"{asm instr}: " ++ ·))

/-- The routine's halfwords. -/
def udivHalves : Array UInt16 := (udivmod64.flatMap encode).toArray

/-- The code map of the routine placed at `fn`. -/
def udivCode (fn : UInt32) (a : UInt32) : Option UInt16 :=
  let off := a - fn
  if off % 2 = 0 ∧ (off / 2).toNat < udivHalves.size then some udivHalves[(off / 2).toNat]!
  else none

/-- The leading zero bits of a nonzero `UInt64`. -/
def clz64 (x : UInt64) : Nat := 63 - x.toNat.log2

/-- The set bits of `x`. -/
def popcount (x : UInt64) : Nat := (List.range 64).countP fun i => (x >>> UInt64.ofNat i) &&& 1 = 1

/-- The path through `udivmod64` of a division of `n` by a nonzero `d`, the passes of the loop, 0
on the other paths, and the number of instructions that the path executes: 8 on `high` and
`low`, 12 on `small`, and on `loop` 29 and 12 for each pass plus 2 for each pass that restores,
whose quotient bit is 0. -/
def divPath (n d : UInt64) : String × Nat × Nat :=
  if d.toUInt32 = 0 then ("high", 0, 8)
  else if n >>> 32 = 0 ∧ d >>> 32 = 0 then ("low", 0, 8)
  else if n < d then ("small", 0, 12)
  else
    let passes := clz64 d - clz64 n + 1
    ("loop", passes, 29 + 14 * passes - 2 * popcount (n / d))

/-- The model's run from `s` until the program counter reaches `target`, with at most `fuel`
steps: the state there and the number of steps, or `none` when a step stops the model or the fuel
runs out. -/
def runTo (code : UInt32 → Option UInt16) (target : UInt32) (fuel : Nat) (s : State) :
    Option (State × Nat) := Id.run do
  let plat : Platform := { normal := fun _ => false, device := fun _ => false }
  let mut st := s
  let mut k := 0
  for _ in [0:fuel] do
    if st.pc = target then break
    match step plat (fun _ => 0) code st with
    | some t =>
        st := t
        k := k + 1
    | none => break
  return if st.pc = target then some (st, k) else none

/-- The path, the passes, and the instruction count of a printed division line, and the
differences between the model's state at the return and the printed state after the call, between
the result words and Lean's `/` and `%`, and between the count and the path's count, or the reason
that the line cannot be checked.  A line holds "D", the case's number, the routine's address, the
return address, r0 to r12, SP, LR, and APSR before the call, and the same registers after it
followed by the number of the landing word. -/
def checkDivLine (line : String) : Except String (String × Nat × Nat × List String) := do
  let toks := (line.splitOn " ").filter (· ≠ "") |>.toArray
  if toks.size ≠ 37 then throw s!"a division line of {toks.size} fields"
  let num (i : Nat) : Except String Nat :=
    match parseHex toks[i]! with
    | some v => pure v
    | none => throw s!"field {i}, {toks[i]!}, is not hexadecimal"
  let fn := UInt32.ofNat (← num 2)
  let ret := UInt32.ofNat (← num 3)
  let inRegs ← (List.range 16).mapM fun i => do return UInt32.ofNat (← num (4 + i))
  let outRegs ← (List.range 17).mapM fun i => do return UInt32.ofNat (← num (20 + i))
  let apsr := inRegs[15]!
  let s : State :=
    { regs := fun r => inRegs[r.val]!, sp := inRegs[13]!, lr := ret ||| 1, pc := fn,
      nFlag := (apsr >>> 31) &&& 1 == 1, zFlag := (apsr >>> 30) &&& 1 == 1,
      cFlag := (apsr >>> 29) &&& 1 == 1, vFlag := (apsr >>> 28) &&& 1 == 1,
      mem := fun _ => 0, trace := [], reads := 0 }
  let pair (lo hi : UInt32) : UInt64 := hi.toUInt64 <<< 32 ||| lo.toUInt64
  let n := pair inRegs[0]! inRegs[1]!
  let d := pair inRegs[2]! inRegs[3]!
  let (path, passes, count) := divPath n d
  match runTo (udivCode fn) ret 4000 s with
  | none => return (path, passes, 0, [s!"{hex n.toNat} / {hex d.toNat}: the model stops"])
  | some (t, steps) =>
      let regDiffs := (List.range 13).filterMap fun r =>
        let want := t.regs ⟨r % 13, Nat.mod_lt _ (by decide)⟩
        if want = outRegs[r]! then none
        else some s!"r{r} {hex outRegs[r]!.toNat}, model {hex want.toNat}"
      let flags := (if t.nFlag then 8 else 0) + (if t.zFlag then 4 else 0) +
        (if t.cFlag then 2 else 0) + (if t.vFlag then 1 else 0)
      let q := pair outRegs[0]! outRegs[1]!
      let m := pair outRegs[2]! outRegs[3]!
      let diffs := regDiffs ++
        (if t.sp = outRegs[13]! then [] else
          [s!"sp {hex outRegs[13]!.toNat}, model {hex t.sp.toNat}"]) ++
        (if t.lr = outRegs[14]! then [] else
          [s!"lr {hex outRegs[14]!.toNat}, model {hex t.lr.toNat}"]) ++
        (if UInt32.ofNat flags = outRegs[15]! >>> 28 then [] else
          [s!"nzcv {hex (outRegs[15]! >>> 28).toNat}, model {hex flags}"]) ++
        (if q = n / d then [] else [s!"quotient {hex q.toNat}, Lean {hex (n / d).toNat}"]) ++
        (if m = n % d then [] else [s!"remainder {hex m.toNat}, Lean {hex (n % d).toNat}"]) ++
        (if steps = count then [] else [s!"{steps} instructions, the {path} path's {count}"])
      return (path, passes, steps, diffs.map (s!"{hex n.toNat} / {hex d.toNat}: " ++ ·))

end TestSupport.M7
