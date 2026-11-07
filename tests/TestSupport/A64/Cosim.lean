import LeanExe.A64.Encode

/-!
The co-simulation of the AArch64 model of `LeanExe/A64/Machine.lean` against QEMU and the
processor.  `harness` writes an assembly file of cases, each an instruction of one of the model's
forms with a state drawn from SplitMix64: the registers, the floating-point registers D0 to D31,
the stack pointer, the flags, and a window of 64 bytes of memory.  The file's `main` runs every
case on QEMU's `virt` machine under the startup code of `tools/baremetal/start.S` and then calls
`cosim_print` of `tests/baremetal/a64cosim.c`, which prints each case's state before and after its
instruction.  A case copies its window into `cosim_win`, adds the window's address to the
registers that address memory, sets the target register of a `RET` to the address of a landing
pad, loads the state, and runs the instruction's word, which `encode` gives.  The 16 words on each
side of the instruction branch to landing code that records which word execution reached, so a
case observes the program counter after a branch as well as after any other instruction.  `check`
reads the printed lines, runs `exec` on each printed state before the instruction, with the
instruction's address as the program counter and the window as the only Normal memory, and
compares the result with the printed state after it.
-/

namespace TestSupport.A64

open LeanExe.A64

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

def word : Gen UInt64 := modifyGet fun r => r.next

def below (n : Nat) : Gen Nat := do
  return (← word).toNat % n

def fin (n : Nat) (h : 0 < n := by decide) : Gen (Fin n) := do
  return ⟨(← below n) % n, Nat.mod_lt _ h⟩

/-- The word of a double, with zeros, infinities, quiet NaNs with and without a payload, signaling
NaNs, subnormals, the largest and smallest normals, and 1.0, each with either sign, weighted. -/
def fpValue : Gen UInt64 := do
  let sign : UInt64 := if (← below 2) = 0 then 0 else 0x8000000000000000
  match ← below 12 with
  | 0 => return sign
  | 1 => return sign ||| 0x7FF0000000000000
  | 2 => return sign ||| 0x7FF8000000000000
  | 3 => return sign ||| 0x7FF8000000000000 ||| ((← word) &&& 0x7FFFFFFFFFFFF)
  | 4 => return sign ||| 0x7FF0000000000000 ||| ((← word) &&& 0x7FFFFFFFFFFFF) ||| 1
  | 5 => return sign ||| 1
  | 6 => return sign ||| ((← word) &&& 0xFFFFFFFFFFFFF)
  | 7 => return sign ||| 0x7FEFFFFFFFFFFFFF
  | 8 => return sign ||| 0x3FF0000000000000
  | 9 => return sign ||| 0x0010000000000000
  | _ => word

/-- The word of a single, with zeros, infinities, quiet NaNs with and without a payload, signaling
NaNs, subnormals, the largest and smallest normals, 1.0, values from 2^-2 to 2^24, where rounding
to an integral value has a fraction to drop, and values from 2^23 to 2^64, the range of the
integer conversions, each with either sign, weighted. -/
def fpValue32 : Gen UInt32 := do
  let sign : UInt32 := if (← below 2) = 0 then 0 else 0x80000000
  let frac : UInt32 := (← word).toUInt32 &&& 0x7FFFFF
  match ← below 14 with
  | 0 => return sign
  | 1 => return sign ||| 0x7F800000
  | 2 => return sign ||| 0x7FC00000
  | 3 => return sign ||| 0x7FC00000 ||| (frac &&& 0x3FFFFF)
  | 4 => return sign ||| 0x7F800000 ||| (frac &&& 0x3FFFFF) ||| 1
  | 5 => return sign ||| 1
  | 6 => return sign ||| frac
  | 7 => return sign ||| 0x7F7FFFFF
  | 8 => return sign ||| 0x3F800000
  | 9 => return sign ||| 0x00800000
  | 10 | 11 => return sign ||| (UInt32.ofNat (125 + (← below 27)) <<< 23) ||| frac
  | 12 => return sign ||| (UInt32.ofNat (150 + (← below 42)) <<< 23) ||| frac
  | _ => return (← word).toUInt32

/-- A D register's word for a single-precision form: a value of `fpValue32` in the low 32 bits and
random upper bits, which the form ignores. -/
def fpLow32 : Gen UInt64 := do
  return ((← word) &&& 0xFFFFFFFF00000000) ||| (← fpValue32).toUInt64

/-- A register value, with the boundary values of signed and unsigned arithmetic weighted. -/
def value : Gen UInt64 := do
  match ← below 10 with
  | 0 => return 0
  | 1 => return 1
  | 2 => return 0xFFFFFFFFFFFFFFFF
  | 3 => return 0x8000000000000000
  | 4 => return 0x7FFFFFFFFFFFFFFF
  | 5 => return 0xFFFFFFFF
  | 6 => return (← word) &&& 0xFF
  | _ => word

/-- The words on each side of a case's instruction that branch to landing code. -/
def padRange : Nat := 16

/-- A branch's word offset, from -16 to 16 without 0. -/
def offset : Gen Int := do
  let k ← below (2 * padRange)
  return if k < padRange then Int.ofNat k - padRange else Int.ofNat k - padRange + 1

/-- The bytes of the memory window. -/
def windowSize : Nat := 64

/-- A case: the instruction, the 31 registers, the 32 floating-point registers, the stack pointer,
NZCV in bits 31 to 28, and the window's bytes, before the harness's changes; the registers, 31 for
the stack pointer, to which the harness adds the window's address; and a register that the harness
sets to the address of the landing word at an offset. -/
structure Case where
  instr : Instr
  regs : Array UInt64
  dregs : Array UInt64
  sp : UInt64
  nzcv : UInt64
  win : Array UInt8
  relWin : List Nat := []
  relPad : Option (Nat × Int) := none

/-- The forms of `Instr` that the co-simulation covers, every form but the system instructions,
in the order of `Instr`. -/
def formCount : Nat := 52

/-- The value that puts an access of the window at `o` at `delta` from the base: `o - delta`. -/
def rel (o delta : Nat) : UInt64 := UInt64.ofNat o - UInt64.ofNat delta

/-- The 26-bit field of the word offset `j`. -/
def field26 (j : Int) : Fin 67108864 :=
  ⟨(j % 67108864).toNat % 67108864, Nat.mod_lt _ (by decide)⟩

/-- The 19-bit field of the word offset `j`. -/
def field19 (j : Int) : Fin 524288 :=
  ⟨(j % 524288).toNat % 524288, Nat.mod_lt _ (by decide)⟩

/-- A case of form `form`, whose state makes the instruction run without a fault.  A case of
`FCMP` sets its second operand, each with probability 1/4, to its first, to its first with the
sign changed, or to the word after its first, so that equal values, zeros of opposite signs, and
neighbors occur, and a case of `FCMP` on S registers does the same with the low 32 bits.  The D
registers of a single-precision form's case hold values of `fpLow32`. -/
def genCase (form : Nat) : Gen Case := do
  let mut regs := #[]
  for _ in [0:31] do
    regs := regs.push (← value)
  let mut dregs := #[]
  for _ in [0:32] do
    dregs := dregs.push (← if form < 39 then fpValue else fpLow32)
  let sp ← value
  let nzcv := ((← word) >>> 60) <<< 28
  let mut win := #[]
  for _ in [0:windowSize] do
    win := win.push (← word).toUInt8
  let c : Case := { instr := .ret 30, regs, dregs, sp, nzcv, win }
  match form with
  | 0 => return { c with instr := .movz (← fin 32) (← fin 65536) (← fin 4) }
  | 1 => return { c with instr := .movk (← fin 32) (← fin 65536) (← fin 4) }
  | 2 => return { c with instr := .addImm (← fin 32) (← fin 32) (← fin 4096) }
  | 3 => return { c with instr := .subImm (← fin 32) (← fin 32) (← fin 4096) }
  | 4 => return { c with instr := .subsImm (← fin 32) (← fin 32) (← fin 4096) }
  | 5 => return { c with instr := .subsReg (← fin 32) (← fin 32) (← fin 32) }
  | 6 => return { c with instr := .csinc (← fin 32) (← fin 32) (← fin 32) (← fin 16) }
  | 7 => return { c with instr := .orrReg (← fin 32) (← fin 32) (← fin 32) }
  | 8 => return { c with instr := .lsrImm (← fin 32) (← fin 32) (← fin 64) }
  | 9 | 10 =>
      let t ← fin 32
      let n ← fin 32
      let imm ← fin 4096
      let instr := if form = 9 then Instr.ldr t n imm else Instr.str t n imm
      if n.val = 31 then
        let o := 8 * imm.val % 16 + 16 * (← below 3)
        return { c with instr, sp := rel o (8 * imm.val), relWin := [31] }
      else
        let o ← below (windowSize - 7)
        return { c with
          instr, regs := c.regs.set! n.val (rel o (8 * imm.val)), relWin := [n.val] }
  | 11 =>
      let t ← fin 32
      let n ← fin 32
      let imm ← fin 4096
      if n.val = 31 then
        let o := imm.val % 16 + 16 * (← below 3)
        return { c with instr := .strb t n imm, sp := rel o imm.val, relWin := [31] }
      else
        let o ← below windowSize
        return { c with
          instr := .strb t n imm, regs := c.regs.set! n.val (rel o imm.val), relWin := [n.val] }
  | 12 => return { c with instr := .b (field26 (← offset)) }
  | 13 => return { c with instr := .bl (field26 (← offset)) }
  | 14 | 15 =>
      let t ← fin 32
      let j ← offset
      let imm := field19 j
      let zeroed := if t.val < 31 ∧ (← below 2) = 0 then c.regs.set! t.val 0 else c.regs
      return { c with instr := if form = 14 then .cbz t imm else .cbnz t imm, regs := zeroed }
  | 16 =>
      let n ← fin 31
      let j ← offset
      return { c with instr := .ret ⟨n.val, by omega⟩, relPad := some (n.val, j) }
  | 17 => return { c with instr := .udiv (← fin 32) (← fin 32) (← fin 32) }
  | 18 => return { c with instr := .msub (← fin 32) (← fin 32) (← fin 32) (← fin 32) }
  | 19 => return { c with instr := .addReg (← fin 32) (← fin 32) (← fin 32) }
  | 20 => return { c with instr := .subReg (← fin 32) (← fin 32) (← fin 32) }
  | 21 => return { c with instr := .andReg (← fin 32) (← fin 32) (← fin 32) }
  | 22 => return { c with instr := .eorReg (← fin 32) (← fin 32) (← fin 32) }
  | 23 => return { c with instr := .madd (← fin 32) (← fin 32) (← fin 32) (← fin 32) }
  | 24 => return { c with instr := .lslv (← fin 32) (← fin 32) (← fin 32) }
  | 25 => return { c with instr := .lsrv (← fin 32) (← fin 32) (← fin 32) }
  | 26 => return { c with instr := .orrW (← fin 32) (← fin 32) (← fin 32) }
  | 27 => return { c with instr := .bcond (← fin 16) (field19 (← offset)) }
  | 28 => return { c with instr := .adr (← fin 32) (← fin 4) (← fin 524288) }
  | 29 => return { c with instr := .adrp (← fin 32) (← fin 4) (← fin 524288) }
  | 30 => return { c with instr := .fmovDX (← fin 32) (← fin 32) }
  | 31 => return { c with instr := .fmovXD (← fin 32) (← fin 32) }
  | 32 => return { c with instr := .fadd (← fin 32) (← fin 32) (← fin 32) }
  | 33 => return { c with instr := .fsub (← fin 32) (← fin 32) (← fin 32) }
  | 34 => return { c with instr := .fmul (← fin 32) (← fin 32) (← fin 32) }
  | 35 => return { c with instr := .fdiv (← fin 32) (← fin 32) (← fin 32) }
  | 36 => return { c with instr := .fsqrt (← fin 32) (← fin 32) }
  | 37 => return { c with instr := .ucvtf (← fin 32) (← fin 32) }
  | 38 =>
      let n ← fin 32
      let m ← fin 32
      let a := c.dregs[n.val]!
      let ds := match ← below 4 with
        | 0 => c.dregs.set! m.val a
        | 1 => c.dregs.set! m.val (a ^^^ 0x8000000000000000)
        | 2 => c.dregs.set! m.val (a + 1)
        | _ => c.dregs
      return { c with instr := .fcmp n m, dregs := ds }
  | 39 => return { c with instr := .fmovSW (← fin 32) (← fin 32) }
  | 40 => return { c with instr := .fmovWS (← fin 32) (← fin 32) }
  | 41 => return { c with instr := .faddS (← fin 32) (← fin 32) (← fin 32) }
  | 42 => return { c with instr := .fsubS (← fin 32) (← fin 32) (← fin 32) }
  | 43 => return { c with instr := .fmulS (← fin 32) (← fin 32) (← fin 32) }
  | 44 => return { c with instr := .fdivS (← fin 32) (← fin 32) (← fin 32) }
  | 45 => return { c with instr := .fsqrtS (← fin 32) (← fin 32) }
  | 46 => return { c with instr := .frintnS (← fin 32) (← fin 32) }
  | 47 => return { c with instr := .ucvtfSX (← fin 32) (← fin 32) }
  | 48 => return { c with instr := .scvtfSW (← fin 32) (← fin 32) }
  | 49 => return { c with instr := .fcvtzuXS (← fin 32) (← fin 32) }
  | 50 => return { c with instr := .fcvtzsWS (← fin 32) (← fin 32) }
  | _ =>
      let n ← fin 32
      let m ← fin 32
      let a := c.dregs[n.val]!
      let low := a &&& 0xFFFFFFFF
      let ds := match ← below 4 with
        | 0 => c.dregs.set! m.val ((c.dregs[m.val]! &&& 0xFFFFFFFF00000000) ||| low)
        | 1 => c.dregs.set! m.val ((c.dregs[m.val]! &&& 0xFFFFFFFF00000000) ||| (low ^^^ 0x80000000))
        | 2 => c.dregs.set! m.val ((c.dregs[m.val]! &&& 0xFFFFFFFF00000000) |||
            ((low + 1) &&& 0xFFFFFFFF))
        | _ => c.dregs
      return { c with instr := .fcmpS n m, dregs := ds }

def hex (v : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 v)

/-- The byte offset of register `r`, 31 for the stack pointer, in a case's table. -/
def slot (r : Nat) : Nat := 8 * r

/-- The assembly of case `k`: its code and its data. -/
def caseAsm (k : Nat) (c : Case) : List String × List String :=
  let l (s : String) := s!"a64c{k}_{s}"
  let pad (id : Nat) := l s!"p{id}"
  let land (id : Nat) := l s!"l{id}"
  let ids := (List.range (2 * padRange + 1)).filter (· ≠ padRange)
  let patches := c.relWin.flatMap fun r =>
    [s!"  ldr x0, =cosim_win", s!"  ldr x1, [x30, #{slot r}]", "  add x1, x1, x0",
      s!"  str x1, [x30, #{slot r}]"]
  let padPatch := match c.relPad with
    | some (r, j) =>
        [s!"  ldr x0, ={pad (Int.toNat (j + padRange))}", s!"  str x0, [x30, #{slot r}]"]
    | none => []
  let loads := (List.range 15).map fun p => s!"  ldp x{2 * p}, x{2 * p + 1}, [x30, #{16 * p}]"
  let saves := (List.range 15).map fun p => s!"  stp x{2 * p}, x{2 * p + 1}, [x30, #{16 * p}]"
  let dloads := (List.range 16).map fun p =>
    s!"  ldp d{2 * p}, d{2 * p + 1}, [x30, #{264 + 16 * p}]"
  let dsaves := (List.range 16).map fun p => s!"  stp d{2 * p}, d{2 * p + 1}, [x1, #{16 * p}]"
  let code :=
    [l "start:", s!"  ldr x0, ={l "win"}", "  ldr x1, =cosim_win", s!"  mov x2, #{windowSize}",
      "1:", "  ldrb w3, [x0], #1", "  strb w3, [x1], #1", "  subs x2, x2, #1", "  b.ne 1b",
      s!"  ldr x30, ={l "in"}"] ++ patches ++ padPatch ++
    ["  ldr x0, [x30, #256]", "  msr nzcv, x0", "  ldr x0, [x30, #248]", "  mov sp, x0"] ++
    loads ++ dloads ++ ["  ldr x30, [x30, #240]", s!"  b {l "test"}"] ++
    ((List.range padRange).map fun id => s!"{pad id}: b {land id}") ++
    [s!"{l "test"}: .inst {hex (encode c.instr).toNat}"] ++
    ((List.range padRange).map fun i =>
      let id := padRange + 1 + i
      s!"{pad id}: b {land id}") ++
    (ids.flatMap fun id =>
      [s!"{land id}:", "  msr tpidr_el1, x30", s!"  mov x30, #{id}", "  msr tpidrro_el0, x30",
        "  mrs x30, tpidr_el1", s!"  b {l "save"}"]) ++
    [s!"{l "save"}:", "  msr tpidr_el1, x30", s!"  ldr x30, ={l "out"}"] ++ saves ++
    ["  mrs x0, tpidr_el1", "  str x0, [x30, #240]", "  mov x0, sp", "  str x0, [x30, #248]",
      "  mrs x0, nzcv", "  str x0, [x30, #256]", "  mrs x0, tpidrro_el0", "  str x0, [x30, #264]",
      s!"  ldr x0, ={l "test"}", "  str x0, [x30, #272]", "  ldr x0, =cosim_win",
      "  str x0, [x30, #280]", s!"  add x1, x30, #{288 + windowSize}"] ++ dsaves ++
      ["  add x1, x30, #288", s!"  mov x2, #{windowSize}", "1:", "  ldrb w3, [x0], #1",
      "  strb w3, [x1], #1", "  subs x2, x2, #1", "  b.ne 1b",
      "  ldr x0, =cosim_sp", "  ldr x0, [x0]", "  mov sp, x0", s!"  b {l "end"}", "  .ltorg",
      s!"{l "end"}:"]
  let data :=
    ["  .balign 8", s!"{l "in"}:"] ++
    ((c.regs.toList ++ [c.sp, c.nzcv] ++ c.dregs.toList).map fun v =>
      s!"  .quad {hex v.toNat}") ++
    [s!"{l "win"}:", "  .byte " ++ ", ".intercalate (c.win.toList.map fun b => hex b.toNat),
      "  .balign 8", s!"{l "out"}:", s!"  .skip {288 + windowSize + 256}"]
  (code, data)

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
    [s!"  .global {name}", s!"{name}:"] ++
      (List.range n).map fun k => s!"  .quad a64c{k}_{suffix}"
  let saved := (List.range 6).map (fun p =>
      s!"  stp x{19 + 2 * p}, x{20 + 2 * p}, [x9, #{16 * p}]") ++
    (List.range 4).map fun p => s!"  stp d{8 + 2 * p}, d{9 + 2 * p}, [x9, #{96 + 16 * p}]"
  let restored := (List.range 6).map (fun p =>
      s!"  ldp x{19 + 2 * p}, x{20 + 2 * p}, [x9, #{16 * p}]") ++
    (List.range 4).map fun p => s!"  ldp d{8 + 2 * p}, d{9 + 2 * p}, [x9, #{96 + 16 * p}]"
  let lines :=
    ["  .text", "  .global main", "main:", "  ldr x9, =cosim_saved"] ++ saved ++
    ["  mov x10, sp", "  ldr x11, =cosim_sp", "  str x10, [x11]"] ++
    parts.flatMap (·.1) ++
    ["  ldr x9, =cosim_saved"] ++ restored ++ ["  b cosim_print", "  .ltorg",
      "  .data", "  .balign 16", "cosim_win:", s!"  .skip {windowSize}", "cosim_sp:", "  .quad 0",
      "cosim_saved:", "  .skip 160", "  .balign 8", "  .global cosim_count", "cosim_count:",
      s!"  .quad {n}"] ++
    table "cosim_in" "in" ++ table "cosim_out" "out" ++ table "cosim_inwin" "win" ++
    parts.flatMap (·.2)
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

/-- The differences between the model's state after the instruction of a printed line and the
printed state after it, or the reason that the line cannot be checked. -/
def checkLine (line : String) : Except String (List String) := do
  let toks := (line.splitOn " ").filter (· ≠ "") |>.toArray
  if toks.size ≠ 138 then throw s!"a line of {toks.size} fields"
  let num (i : Nat) : Except String Nat :=
    match parseHex toks[i]! with
    | some v => pure v
    | none => throw s!"field {i}, {toks[i]!}, is not hexadecimal"
  let w ← num 2
  let p := UInt64.ofNat (← num 3)
  let winAddr := UInt64.ofNat (← num 4)
  let inRegs ← (List.range 33).mapM fun i => do return UInt64.ofNat (← num (5 + i))
  let inWin ← match parseBytes toks[38]! with
    | some b => pure b
    | none => throw "the window before is not hexadecimal"
  let outRegs ← (List.range 34).mapM fun i => do return UInt64.ofNat (← num (39 + i))
  let outWin ← match parseBytes toks[73]! with
    | some b => pure b
    | none => throw "the window after is not hexadecimal"
  let inD ← (List.range 32).mapM fun i => do return UInt64.ofNat (← num (74 + i))
  let outD ← (List.range 32).mapM fun i => do return UInt64.ofNat (← num (106 + i))
  let instr ← match decodeNat w with
    | some i => pure i
    | none => throw s!"the word {hex w} decodes to no form"
  let nzcv := inRegs[32]!
  let s : State :=
    { regs := fun r => inRegs[r.val]!, dregs := fun r => inD[r.val]!, sp := inRegs[31]!, pc := p,
      nFlag := (nzcv >>> 31) &&& 1 == 1, zFlag := (nzcv >>> 30) &&& 1 == 1,
      cFlag := (nzcv >>> 29) &&& 1 == 1, vFlag := (nzcv >>> 28) &&& 1 == 1,
      mem := fun a => if a - winAddr < UInt64.ofNat windowSize then inWin[(a - winAddr).toNat]!
        else 0,
      out := [] }
  let plat : Platform :=
    { normal := fun a => a - winAddr < UInt64.ofNat windowSize, uart := 0x09000000 }
  match exec plat instr s with
  | none => return [s!"the model stops on {repr instr}"]
  | some t =>
      let regDiffs := (List.range 31).filterMap fun r =>
        let want := t.regs ⟨r % 31, Nat.mod_lt _ (by decide)⟩
        if want = outRegs[r]! then none
        else some s!"x{r} {hex outRegs[r]!.toNat}, model {hex want.toNat}"
      let flags := (if t.nFlag then 8 else 0) + (if t.zFlag then 4 else 0) +
        (if t.cFlag then 2 else 0) + (if t.vFlag then 1 else 0)
      let landed := p + (4 : UInt64) * outRegs[33]! - UInt64.ofNat (4 * padRange)
      let winDiffs := (List.range windowSize).filterMap fun i =>
        let want := t.mem (winAddr + UInt64.ofNat i)
        if want = outWin[i]! then none
        else some s!"byte {i} {hex outWin[i]!.toNat}, model {hex want.toNat}"
      let dDiffs := (List.range 32).filterMap fun r =>
        let want := t.dregs ⟨r % 32, Nat.mod_lt _ (by decide)⟩
        if want = outD[r]! then none
        else some s!"d{r} {hex outD[r]!.toNat}, model {hex want.toNat}"
      return regDiffs ++ dDiffs ++
        (if t.sp = outRegs[31]! then [] else
          [s!"sp {hex outRegs[31]!.toNat}, model {hex t.sp.toNat}"]) ++
        (if UInt64.ofNat (flags * 0x10000000) = outRegs[32]! then [] else
          [s!"nzcv {hex outRegs[32]!.toNat}, model {hex (flags * 0x10000000)}"]) ++
        (if t.pc = landed then [] else
          [s!"pc {hex landed.toNat}, model {hex t.pc.toNat}"]) ++
        winDiffs |>.map (s!"{repr instr}: " ++ ·)

end TestSupport.A64
