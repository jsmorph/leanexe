import TestSupport.M7.Asm

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

/-- The harness of `perForm` cases of each form from the seed `seed`. -/
def harness (seed : UInt64) (perForm : Nat) : String := Id.run do
  let mut rng : Rng := ⟨seed⟩
  let mut cases := #[]
  for form in [0:formCount] do
    for _ in [0:perForm] do
      let (c, r) := (genCase form).run rng
      rng := r
      cases := cases.push c
  let parts := cases.toList.zipIdx.map fun (c, k) => caseAsm k c
  let n := cases.size
  let table (name suffix : String) :=
    ["  .balign 4", s!"  .global {name}", s!"{name}:"] ++
      (List.range n).map fun k => s!"  .word m7c{k}_{suffix}"
  let lines :=
    ["  .syntax unified", "  .arch armv7e-m", "  .fpu fpv5-d16",
      "  .eabi_attribute Tag_ABI_VFP_args, 1", "  .thumb", "  .text", "  .global main",
      "  .type main, %function", "  .thumb_func", "main:", "  push {r4-r11, lr}", "  vpush {s16}",
      "  ldr r0, =cosim_sp", "  mov r1, sp", "  str r1, [r0]"] ++
    parts.flatMap (·.1) ++
    ["  vpop {s16}", "  pop {r4-r11, lr}", "  b.w cosim_print"] ++ landing ++
    ["  .data"] ++ parts.flatMap (·.2.1) ++
    ["  .bss", "  .balign 8", "  .global cosim_win", "cosim_win:", s!"  .skip {windowSize}",
      "cosim_sp:", "  .skip 4", "cosim_cur:", "  .skip 4", "cosim_next:", "  .skip 4"] ++
    parts.flatMap (·.2.2) ++
    ["  .section .rodata", "  .balign 4", "  .global cosim_count", "cosim_count:",
      s!"  .word {n}"] ++
    table "cosim_in" "in" ++ table "cosim_out" "out" ++ table "cosim_inwin" "win" ++
    table "cosim_test" "test" ++ ["  .section .note.GNU-stack, \"\", %progbits"]
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

end TestSupport.M7
