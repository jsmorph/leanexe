import TestSupport.M7.Cosim
import LeanExe.M7.Board

/-!
The co-simulation of the Cortex-M7 model of `LeanExe/M7/Machine.lean` on the NUCLEO-F767ZI.
`image` writes a flat image that boots as the proved images do: the vector table of
`LeanExe/M7/Board.lean` at the flash's ITCM address `0x00200000` with SP at the top of DTCM, the
self-loop, and the board's initialization, which enables USART3 as `board_init` does.  The
harness follows, written by Lean with the model's encoder and a few harness encodings outside the
model, and the input records after it, in the flash.  No C, startup code, floating-point unit, or
MPU takes part, so each case runs in the processor's configuration of the proved runs: Thread mode
on SP_main from reset, at reset clocking, with the caches off.

The cases of the model's forms are those of `genCase` of `tests/TestSupport/M7/Cosim.lean`, with
the window of 64 bytes at DTCM's base and r12 holding the address of the case's output record.
Two further forms load from and store to USART3's receiver timeout register `USART_RTOR` at
`0x40004814`, in the model's device window, through a base register that puts the access there.
`USART_RTOR` holds 32 bits that read back as written, RM0410 Rev 5 (section 34.8.6) allows writes
"on the fly", and with RTOEN and RTOIE clear, as the board's initialization leaves them, a write
changes neither the transmitter nor the receiver and at most sets the flag RTOF, which no
interrupt follows.  The registers that the gateway uses lack one of these properties: a write to
`USART_TDR` sends a byte, a read of `USART_RDR` clears RXNE, `USART_BRR` and `USART_CR2` may be
written only while UE is 0, and the flags of `USART_ISR` follow the line.  Before every case the
harness
writes the case's device value to `USART_RTOR`, and after it reads the register back, so a load
case knows the value that the device returns and a store case shows the value that reached it.

The seeded cases draw their immediate fields at random, so they may miss a value that the
generated code contains.  Unless `seeded` is given, the fixed cases of `fixed` follow them: one
case for each immediate shift amount, S bit, immediate value, offset class, condition, and branch
direction that `LeanExe/M7/Gen.lean` and `LeanExe/M7/Div.lean` emit, each with the state of a case
of its form that continues the seeded sequence, so the seeded cases stay those of a run without
the fixed ones.

A case's code sets r12 to its input record, calls the setup routine with `BL`, loads SP, LR, r0
to r11, and r12 from the record, and branches to its instruction, which lies between 16 pads on
each side.  The setup routine copies the record's window into DTCM, writes the device value,
stores the case's continuation in the header, and sets NZCV with `MSR APSR_nzcvq` last.  Each pad
branches to landing code that stores r0 and the pad's number in the output record and branches to
the save routine, which stores r1 to r12, SP, LR, APSR from `MRS`, the window, and the device
register's value, counts the case in the header, and branches to the continuation.  The landing
and save code store the registers through r12, which no form of the model can name, so the cases
need no floating-point registers to hold the state, as the QEMU harness does.

DTCM holds the window at `0x20000000`, the header at `0x20000040`, and the output records from
`0x20000060`.  The header holds the word `0x600DCAFE`, which the image writes after the last case,
the number of cases saved, the continuation, the number of cases, the seed's two words, the low
first, and the number of cases of each form.  An input record holds r0 to r11, r12, SP, LR, APSR,
the window's 16 words, the device value, and the continuation with bit 0 set.  An output record
holds r0 to r12, SP, LR, APSR, the pad's number, the window's 16 words, and the device register's
value after the case.

`checkCase` takes a case that `boardCases` regenerates from the seed and the count and the bytes
that `st-flash` read from DTCM.  It runs `exec` with the board's `platform` from the case's state,
with the instruction's address as the program counter, the window as the bytes of memory, and the
device value as every device read, and compares registers, flags, the landing address, the
window, and the device register's value, which the model's device access determines.  With
`mutate`, the model's `ADC` ignores its carry in, a deliberate error that the check must report.
-/

namespace TestSupport.M7.BoardCosim

open LeanExe.M7 LeanExe.M7.Nucleo

/-- The window of `windowSize` bytes that the memory forms access: the first bytes of DTCM. -/
def win : UInt32 := 0x20000000

/-- The header. -/
def hdr : UInt32 := 0x20000040

/-- The first output record. -/
def outBase : UInt32 := 0x20000060

/-- The words of an input record and of an output record. -/
def recWords : Nat := 34

/-- The header's word after the last case. -/
def doneWord : UInt32 := 0x600DCAFE

/-- `USART_RTOR`, the device register of the device cases. -/
def rtor : UInt32 := 0x40004814

/-- The forms of the board's cases: the model's forms, then the load and the store at `rtor`. -/
def kinds : Nat := formCount + 2

/-- The name of form `form` of the board's cases. -/
def kindName (form : Nat) (i : Instr) : String :=
  if form = formCount then "ldrDev" else if form = formCount + 1 then "strDev" else formName i

abbrev Code := List UInt16

def ins (is : List Instr) : Code := is.flatMap encode

def bytesOf (c : Code) : Nat := 2 * c.length

/-- `LDR.W Rt, [Rn, #imm]` (DDI 0403E.e A7.7.43, T3) for `Rt` and `Rn` from r0 to r14, which
admits SP and LR as `Rt` ("This register is permitted to be the SP"). -/
def ldrW (t n imm : Nat) : Code := [UInt16.ofNat (0xF8D0 + n), UInt16.ofNat (t * 4096 + imm)]

/-- `STR.W Rt, [Rn, #imm]` (A7.7.161, T3) for `Rt` and `Rn` from r0 to r14. -/
def strW (t n imm : Nat) : Code := [UInt16.ofNat (0xF8C0 + n), UInt16.ofNat (t * 4096 + imm)]

/-- `MOVW` and `MOVT` (A7.7.76 T3, A7.7.79 T1) that set register `d` of r0 to r12 to `w`. -/
def movW (d : Nat) (w : UInt32) : Code :=
  let half (op v : Nat) : Code := [UInt16.ofNat (op + v / 2048 % 2 * 1024 + v / 4096),
    UInt16.ofNat (v / 256 % 8 * 4096 + d * 256 + v % 256)]
  half 0xF240 (w.toNat % 65536) ++ half 0xF2C0 (w.toNat / 65536)

/-- `MSR APSR_nzcvq, r0` (B5.2.3, T1: mask `0b10`, SYSm 0). -/
def msrApsr : Code := [0xF380, 0x8800]

/-- `MRS r0, APSR` (B5.2.2, T1: SYSm 0). -/
def mrsApsr : Code := [0xF3EF, 0x8000]

/-- `BX r0` (A7.7.20, T1). -/
def bxR0 : Code := [0x4700]

/-- `NOP` (A7.7.88, T1), which follows each 16-bit instruction so that code stays in words. -/
def nop : Code := [0xBF00]

/-- The byte offset of a branch at `here` to `target`. -/
def brOff (here target : UInt32) : Int := (target.toNat : Int) - (here.toNat + 4)

/-- The halfwords of a case's instruction, a 16-bit form followed by `NOP`. -/
def testCode (i : Instr) : Code := if (encode i).length = 2 then encode i else encode i ++ nop

/-- The writes of the header at the start: the magic word and the count of saved cases cleared,
the number of cases, the seed, and the number of cases of each form. -/
def startOps (seed : UInt64) (per n : Nat) : List InitOp :=
  [.write hdr 0, .write (hdr + 4) 0, .write (hdr + 12) (UInt32.ofNat n),
    .write (hdr + 16) seed.toUInt32, .write (hdr + 20) (seed >>> 32).toUInt32,
    .write (hdr + 24) (UInt32.ofNat per)]

/-- The code after the last case: the magic word, then a self-loop. -/
def finCode : Code := ins (initCode [.write hdr doneWord] ++ [Instr.bTo (-4)])

/-- The start of a case at `a` with the input record `inRec`: r12 set to the record, the call of
the setup routine at `setup`, and SP, LR, r0 to r11, and r12 loaded from the record. -/
def preCode (a inRec setup : UInt32) : Code :=
  movW 12 inRec ++ ins [Instr.blTo (brOff (a + 8) setup)] ++ ldrW 13 12 52 ++ ldrW 14 12 56 ++
    (List.range 12).flatMap (fun r => ldrW r 12 (4 * r)) ++ ldrW 12 12 48

/-- The offset of a case's instruction from the case's start. -/
def testOff : Nat := bytesOf (preCode 0 0 0) + 4 + 4 * padRange

/-- The address of pad `p`, from 0 to 32, of the instruction at `test`. -/
def padAddr (test : UInt32) (p : Nat) : UInt32 :=
  test + UInt32.ofNat (4 * p) - UInt32.ofNat (4 * padRange)

/-- The code of a case at `a`: its start, a branch over the pads before the instruction, the pads,
the instruction `t`, and the pads after it, pad `p` a branch to `land p`. -/
def caseCode (a inRec setup : UInt32) (land : Nat → UInt32) (t : Code) : Code :=
  let pre := preCode a inRec setup
  let skip := a + UInt32.ofNat (bytesOf pre)
  let test := a + UInt32.ofNat testOff
  let pad (p : Nat) := ins [Instr.bTo (brOff (padAddr test p) (land p))]
  pre ++ ins [Instr.bTo (brOff skip test)] ++ (List.range padRange).flatMap pad ++ t ++
    ((List.range padRange).map (· + padRange + 1)).flatMap pad

/-- The landing code of pad `p` at `a`: r0 and the pad's number stored, and a branch to the save
routine at `save`. -/
def landCode (save a : UInt32) (p : Nat) : Code :=
  strW 0 12 0 ++ ins [Instr.movwOf 0 p] ++ strW 0 12 64 ++ ins [Instr.bTo (brOff (a + 12) save)]

/-- The save routine. -/
def saveCode : Code :=
  (List.range 12).flatMap (fun r => strW (r + 1) 12 (4 * (r + 1))) ++ strW 13 12 52 ++
    strW 14 12 56 ++ mrsApsr ++ strW 0 12 60 ++ ins (movWord 1 win) ++
    (List.range 16).flatMap (fun i => ins [.ldr 0 1 (field 4096 (4 * i))] ++ strW 0 12 (68 + 4 * i)) ++
    ins (movWord 1 rtor ++ [.ldr 0 1 0]) ++ strW 0 12 132 ++
    ins (movWord 1 hdr ++ [.ldr 0 1 4, .movImm 2 1, Instr.addLsl 0 0 0 2 0, .str 0 1 4, .ldr 0 1 8]) ++
    bxR0 ++ nop

/-- The setup routine, called with r12 at the input record. -/
def setupCode : Code :=
  ins (movWord 1 win) ++
    (List.range 16).flatMap (fun i => ldrW 0 12 (64 + 4 * i) ++ ins [.str 0 1 (field 4096 (4 * i))]) ++
    ins (movWord 1 rtor) ++ ldrW 0 12 128 ++ ins [.str 0 1 0] ++
    ins (movWord 1 hdr) ++ ldrW 0 12 132 ++ ins [.str 0 1 8] ++
    ldrW 0 12 60 ++ msrApsr ++ ins [.bxLr] ++ nop

/-- The addresses of the image's parts for `n` cases. -/
structure Layout where
  n : Nat
  cases : UInt32
  fin : UInt32
  land : UInt32
  save : UInt32
  setup : UInt32
  data : UInt32

def caseBytes : Nat := bytesOf (caseCode 0 0 0 (fun _ => 0) (testCode .dsb))

def layout (n : Nat) : Layout :=
  let cases := boot.base + UInt32.ofNat (bytesOf (ins (initCode (startOps 0 0 0))))
  let fin := cases + UInt32.ofNat (caseBytes * n)
  let land := fin + UInt32.ofNat (bytesOf finCode)
  let save := land + UInt32.ofNat (16 * (2 * padRange))
  let setup := save + UInt32.ofNat (bytesOf saveCode)
  { n, cases, fin, land, save, setup, data := setup + UInt32.ofNat (bytesOf setupCode) }

def Layout.caseAddr (L : Layout) (k : Nat) : UInt32 := L.cases + UInt32.ofNat (caseBytes * k)

def Layout.testAddr (L : Layout) (k : Nat) : UInt32 := L.caseAddr k + UInt32.ofNat testOff

/-- The landing code of pad `p`; pad 16 is the instruction's place and has none. -/
def Layout.landAddr (L : Layout) (p : Nat) : UInt32 :=
  L.land + UInt32.ofNat (16 * (if p < padRange then p else p - 1))

def Layout.inAddr (L : Layout) (k : Nat) : UInt32 := L.data + UInt32.ofNat (4 * recWords * k)

def outAddr (k : Nat) : UInt32 := outBase + UInt32.ofNat (4 * recWords * k)

/-- The bytes of DTCM from `win` that the results occupy for `n` cases. -/
def resultBytes (n : Nat) : Nat := (outAddr n - win).toNat

/-- A case of the board: a case of `genCase` and the value written to `USART_RTOR` before it. -/
structure BCase where
  c : Case
  dev : UInt32

/-- A case of form `form`: the model's forms first, then the load and the store at `rtor`, whose
base register `genCase` sets for the window and which this function sets for `rtor`. -/
def genBoard (form : Nat) : Gen BCase := do
  if form < formCount then
    let c ← genCase form
    return { c, dev := (← value) }
  else
    let c ← genCase (if form = formCount then 28 else 29)
    let c := match c.instr with
      | .ldr _ n imm | .str _ n imm =>
          { c with regs := c.regs.set! n.val (rtor - UInt32.ofNat imm.val), relWin := [] }
      | _ => c
    return { c, dev := (← value) }

/-- A fixed case: its name, the form of `genBoard` whose case gives its state, and the change of
that case's instruction to an instance that the generated code contains, or `none` when the
form's instruction has another constructor. -/
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

/-- The offset 0 of a load or store at `rtor`, whose base register then holds `rtor`. -/
def devZero (c : Case) : Gen (Option Case) :=
  pure <| match c.instr with
    | .ldr t n _ => some { c with instr := .ldr t n 0, regs := c.regs.set! n.val rtor }
    | .str t n _ => some { c with instr := .str t n 0, regs := c.regs.set! n.val rtor }
    | _ => none

/-- A branch `mk` to a random pad after the instruction when `fwd` holds, and before it otherwise. -/
def branchPad (fwd : Bool) (mk : Int → Instr) (c : Case) : Gen (Option Case) := do
  let k := Int.ofNat ((← below padRange) + 1)
  return some { c with instr := mk (4 * (if fwd then k else -k) - 4) }

/-- The direction of a branch in a fixed case's name. -/
def dir (fwd : Bool) : String := if fwd then "forward" else "backward"

/-- The instances of the immediate fields that `LeanExe/M7/Gen.lean` and `LeanExe/M7/Div.lean`
emit: the shifts by an immediate, `LSL #0` and `#16` and `LSR #1`, `#5`, `#16`, and `#31`; `ADDS`
with no shift and `ADD` with `LSL #1`, `#2`, and `#31`; both S bits of `SUB`, `SBC`, and `ORR`; the
8-bit immediates `MOV #0` and `#32`, `CMP #0`, `SUB #1` and `#32`, `AND #63`, and `EOR #1`;
`MOVW` and `MOVT` at the ends of their range and `MOVT` of the stack's limit and of the device
window; the frame sizes of `SUBW Rd, SP` and `ADDW` and `SUBW SP, SP`, multiples of 8 from 8 to
4088, at both ends; the SP-relative offsets, multiples of 4 from 0 to 4092 and LR's from 0 to
4080, at both ends; the offset 0 of a device access; the conditions EQ, NE, CS, and CC; and every
branch both forward and backward. -/
def fixed : List Fixed :=
  [Fixed.mk "lslImm #0" 10 (instrTo (shiftBy 0)),
    Fixed.mk "lslImm #16" 10 (instrTo (shiftBy 16))] ++
  ([1, 5, 16, 31].map fun k => Fixed.mk s!"lsrImm #{k}" 11 (instrTo (shiftBy k))) ++
  ([((1 : Fin 2), 0), (0, 1), (0, 2), (0, 31)].map fun (s, k) =>
    Fixed.mk s!"addReg s{s.val} #{k}" 0 (instrTo (addShift s k))) ++
  ([("subReg", 2), ("sbcReg", 3), ("orrReg", 5)].flatMap fun (nm, f) =>
    [(0 : Fin 2), 1].map fun s => Fixed.mk s!"{nm} s{s.val}" f (instrTo (withS s))) ++
  ([("movImm", 16, (0 : Fin 256)), ("movImm", 16, 32), ("cmpImm", 15, 0), ("subImm", 12, 1),
      ("subImm", 12, 32), ("andImm", 13, 63), ("eorImm", 14, 1)].map fun (nm, f, v) =>
    Fixed.mk s!"{nm} #{v.val}" f (instrTo (imm8 v))) ++
  ([("movw", 17, 0), ("movw", 17, 65535), ("movt", 18, 0x2000), ("movt", 18, 0x4000),
      ("movt", 18, 65535)].map fun (nm, f, v) => Fixed.mk s!"{nm} #{v}" f (instrTo (imm16Of v))) ++
  ([("subwSp", 20), ("addwSpSp", 21), ("subwSpSp", 22)].flatMap fun (nm, f) =>
    [8, 4088].map fun v => Fixed.mk s!"{nm} #{v}" f (instrTo (imm12Of v))) ++
  ([("ldrSp", 30, 4092), ("strSp", 31, 4092), ("ldrLr", 32, 4080), ("strLr", 33, 4080)].flatMap
    fun (nm, f, top) => [0, top].map fun v => Fixed.mk s!"{nm} #{v}" f (spOffset v)) ++
  [Fixed.mk "ldrDev #0" formCount devZero, Fixed.mk "strDev #0" (formCount + 1) devZero] ++
  ([("eq", (0 : Fin 14)), ("ne", 1), ("cs", 2), ("cc", 3)].flatMap fun (nm, cond) =>
    [true, false].map fun fwd =>
      Fixed.mk s!"bcond {nm} {dir fwd}" 34 (branchPad fwd (Instr.bcondTo cond))) ++
  ([("b", 35, Instr.bTo), ("bl", 36, Instr.blTo)].flatMap fun (nm, f, mk) =>
    [true, false].map fun fwd => Fixed.mk s!"{nm} {dir fwd}" f (branchPad fwd mk))

/-- The fixed case `x`: the case of its form, with the dev value of that case, and its change. -/
def genFixed (x : Fixed) : Gen (Option BCase) := do
  let b ← genBoard x.form
  return (← x.set b.c).map fun c => { b with c }

/-- The cases with their names: `per` of each form from the seed `seed`, then, unless `seeded`,
the fixed cases, whose states continue the same sequence. -/
def boardCases (seed : UInt64) (per : Nat) (seeded : Bool) :
    Except String (Array (String × BCase)) := do
  let mut rng : Rng := ⟨seed⟩
  let mut out := #[]
  for form in [0:kinds] do
    for _ in [0:per] do
      let (c, r) := (genBoard form).run rng
      rng := r
      out := out.push (kindName form c.c.instr, c)
  if !seeded then
    for x in fixed do
      let (b, r) := (genFixed x).run rng
      rng := r
      match b with
      | some b => out := out.push (x.name, b)
      | none => throw s!"the fixed case {x.name} does not fit form {x.form}"
  return out

/-- The word of the four bytes from `4 * i` of `b`, the lowest first. -/
def wordOf (b : Array UInt8) (i : Nat) : UInt32 :=
  b[4 * i]!.toUInt32 ||| b[4 * i + 1]!.toUInt32 <<< 8 ||| b[4 * i + 2]!.toUInt32 <<< 16 |||
    b[4 * i + 3]!.toUInt32 <<< 24

/-- The input record of case `k`, with the window's address added to the registers that address
it and LR at the pad that `BX LR` reaches. -/
def inRecord (L : Layout) (k : Nat) (b : BCase) : List UInt32 :=
  let c := b.c
  let regs := (List.range 13).map fun r =>
    if r = 12 then outAddr k else if r ∈ c.relWin then c.regs[r]! + win else c.regs[r]!
  let sp := if 13 ∈ c.relWin then c.sp + win else c.sp
  let lr := match c.relPad with
    | some j => padAddr (L.testAddr k) (Int.toNat (j + padRange)) ||| 1
    | none => c.lr
  regs ++ [sp, lr, c.apsr] ++ (List.range (windowSize / 4)).map (wordOf c.win) ++
    [b.dev, L.caseAddr (k + 1) ||| 1]

/-- The image's bytes and layout for `per` cases of each form from the seed `seed` and, unless
`seeded`, the fixed cases. -/
def image (seed : UInt64) (per : Nat) (seeded : Bool) : Except String (List UInt8 × Layout) := do
  let cases ← boardCases seed per seeded
  let n := cases.size
  if outAddr n > stackTop then
    throw s!"{n} cases need {resultBytes n} bytes of DTCM from {hex win.toNat}"
  let L := layout n
  let code := ins (Instr.bTo (-4) :: boot.init) ++ ins (initCode (startOps seed per n)) ++
    (cases.toList.zipIdx.flatMap fun ((_, b), k) =>
      caseCode (L.caseAddr k) (L.inAddr k) L.setup L.landAddr (testCode b.c.instr)) ++
    finCode ++ (padIds.flatMap fun p => landCode L.save (L.landAddr p) p) ++ saveCode ++ setupCode
  let data := cases.toList.zipIdx.flatMap fun ((_, b), k) => inRecord L k b
  let halfs := boot.table.flatMap wordHalfs ++ code
  if boot.org + UInt32.ofNat (2 * halfs.length) ≠ L.data then
    throw "the code's length differs from the layout's"
  return ((halfs ++ data.flatMap wordHalfs).flatMap halfBytes, L)

/-- `exec`, or with `mutate` the model with `ADC`'s carry in replaced by 0. -/
def execWith (mutate : Bool) (σ : Nat → UInt32) (i : Instr) (s : State) : Option State :=
  match mutate, i with
  | true, .adcReg d n m => some { s.setR d (addWithCarry (s.r n) (s.r m) false).1 with pc := s.pc + 4 }
  | _, _ => exec platform σ i s

/-- The word at byte `o` of `b`, the lowest byte first. -/
def wordAt (b : ByteArray) (o : Nat) : UInt32 :=
  b[o]!.toUInt32 ||| b[o + 1]!.toUInt32 <<< 8 ||| b[o + 2]!.toUInt32 <<< 16 |||
    b[o + 3]!.toUInt32 <<< 24

/-- The two hexadecimal digits of a byte. -/
def byteHex (x : UInt8) : String :=
  let d := Nat.toDigits 16 x.toNat
  String.ofList (if d.length = 1 then '0' :: d else d)

/-- The inputs of case `k`, for a report. -/
def inputs (L : Layout) (k : Nat) (b : BCase) : String :=
  let w := inRecord L k b
  let names := ((List.range 13).map fun r => s!"r{r}") ++ ["sp", "lr", "apsr"]
  " ".intercalate ((names.zip w).map fun (nm, v) => s!"{nm} {hex v.toNat}") ++
    s!" window {String.join (b.c.win.toList.map byteHex)}" ++
    s!" device {hex b.dev.toNat}"

/-- The differences between the model's state after case `k` and the board's output record in
`res`, the bytes from `win`. -/
def checkCase (mutate : Bool) (L : Layout) (res : ByteArray) (k : Nat) (b : BCase) :
    List String :=
  let w := inRecord L k b
  let o := (outAddr k - win).toNat
  let out (i : Nat) := wordAt res (o + 4 * i)
  let apsr := w[15]!
  let s : State :=
    { regs := fun r => w[r.val]!, sp := w[13]!, lr := w[14]!, pc := L.testAddr k,
      nFlag := (apsr >>> 31) &&& 1 == 1, zFlag := (apsr >>> 30) &&& 1 == 1,
      cFlag := (apsr >>> 29) &&& 1 == 1, vFlag := (apsr >>> 28) &&& 1 == 1,
      mem := fun a => if a - win < UInt32.ofNat windowSize then b.c.win[(a - win).toNat]! else 0,
      trace := [], reads := 0 }
  match execWith mutate (fun _ => b.dev) b.c.instr s with
  | none => ["the model stops"]
  | some t =>
      let regs := (List.range 13).filterMap fun r =>
        let want := t.regs ⟨r % 13, Nat.mod_lt _ (by decide)⟩
        if want = out r then none else some s!"r{r} {hex (out r).toNat}, model {hex want.toNat}"
      let flags := (if t.nFlag then 8 else 0) + (if t.zFlag then 4 else 0) +
        (if t.cFlag then 2 else 0) + (if t.vFlag then 1 else 0)
      let landed := padAddr (L.testAddr k) (out 16).toNat
      let window := (List.range windowSize).filterMap fun i =>
        let got := res[o + 68 + i]!
        let want := t.mem (win + UInt32.ofNat i)
        if want = got then none else some s!"byte {i} {hex got.toNat}, model {hex want.toNat}"
      let dev := match t.trace with
        | [] => some b.dev
        | [.read a _] => if a = rtor then some b.dev else none
        | [.write a v] => if a = rtor then some v else none
        | _ => none
      regs ++
        (if t.sp = out 13 then [] else [s!"sp {hex (out 13).toNat}, model {hex t.sp.toNat}"]) ++
        (if t.lr = out 14 then [] else [s!"lr {hex (out 14).toNat}, model {hex t.lr.toNat}"]) ++
        (if UInt32.ofNat flags = out 15 >>> 28 then [] else
          [s!"nzcv {hex (out 15 >>> 28).toNat}, model {hex flags}"]) ++
        (if t.pc = landed then [] else [s!"pc {hex landed.toNat}, model {hex t.pc.toNat}"]) ++
        window ++
        (match dev with
          | some v => if v = out 33 then [] else
              [s!"USART_RTOR {hex (out 33).toNat}, model {hex v.toNat}"]
          | none => [s!"the model's device accesses {repr t.trace}"])

end TestSupport.M7.BoardCosim
