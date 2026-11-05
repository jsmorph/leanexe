import LeanExe.A64.Encode

/-!
The co-simulation of the AArch64 model of `LeanExe/A64/Machine.lean` against QEMU and the
processor.  `harness` writes an assembly file of cases, each an instruction of one of the model's
forms with a state drawn from SplitMix64: the registers, the stack pointer, the flags, and a
window of 64 bytes of memory.  The file's `main` runs every case on QEMU's `virt` machine under
the startup code of `tools/baremetal/start.S` and then calls `cosim_print` of
`tests/baremetal/a64cosim.c`, which prints each case's state before and after its instruction.
A case copies its window into `cosim_win`, adds the window's address to the registers that
address memory, sets the target register of a `RET` to the address of a landing pad, loads the
state, and runs the instruction's word, which `encode` gives.  The 16 words on each side of the
instruction branch to landing code that records which word execution reached, so a case
observes the program counter after a branch as well as after any other instruction.  `check`
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

/-- A case: the instruction, the 31 registers, the stack pointer, NZCV in bits 31 to 28, and the
window's bytes, before the harness's changes; the registers, 31 for the stack pointer, to which
the harness adds the window's address; and a register that the harness sets to the address of
the landing word at an offset. -/
structure Case where
  instr : Instr
  regs : Array UInt64
  sp : UInt64
  nzcv : UInt64
  win : Array UInt8
  relWin : List Nat := []
  relPad : Option (Nat × Int) := none

/-- The 19 forms in the order of `Instr`. -/
def formCount : Nat := 19

/-- The value that puts an access of the window at `o` at `delta` from the base: `o - delta`. -/
def rel (o delta : Nat) : UInt64 := UInt64.ofNat o - UInt64.ofNat delta

/-- The 26-bit field of the word offset `j`. -/
def field26 (j : Int) : Fin 67108864 :=
  ⟨(j % 67108864).toNat % 67108864, Nat.mod_lt _ (by decide)⟩

/-- The 19-bit field of the word offset `j`. -/
def field19 (j : Int) : Fin 524288 :=
  ⟨(j % 524288).toNat % 524288, Nat.mod_lt _ (by decide)⟩

/-- A case of form `form`, whose state makes the instruction run without a fault. -/
def genCase (form : Nat) : Gen Case := do
  let mut regs := #[]
  for _ in [0:31] do
    regs := regs.push (← value)
  let sp ← value
  let nzcv := ((← word) >>> 60) <<< 28
  let mut win := #[]
  for _ in [0:windowSize] do
    win := win.push (← word).toUInt8
  let c : Case := { instr := .ret 30, regs, sp, nzcv, win }
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
  | _ => return { c with instr := .msub (← fin 32) (← fin 32) (← fin 32) (← fin 32) }

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
  let code :=
    [l "start:", s!"  ldr x0, ={l "win"}", "  ldr x1, =cosim_win", s!"  mov x2, #{windowSize}",
      "1:", "  ldrb w3, [x0], #1", "  strb w3, [x1], #1", "  subs x2, x2, #1", "  b.ne 1b",
      s!"  ldr x30, ={l "in"}"] ++ patches ++ padPatch ++
    ["  ldr x0, [x30, #256]", "  msr nzcv, x0", "  ldr x0, [x30, #248]", "  mov sp, x0"] ++
    loads ++ ["  ldr x30, [x30, #240]", s!"  b {l "test"}"] ++
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
      "  str x0, [x30, #280]", "  add x1, x30, #288", s!"  mov x2, #{windowSize}", "1:",
      "  ldrb w3, [x0], #1", "  strb w3, [x1], #1", "  subs x2, x2, #1", "  b.ne 1b",
      "  ldr x0, =cosim_sp", "  ldr x0, [x0]", "  mov sp, x0", s!"  b {l "end"}", "  .ltorg",
      s!"{l "end"}:"]
  let data :=
    ["  .balign 8", s!"{l "in"}:"] ++
    ((c.regs.toList ++ [c.sp, c.nzcv]).map fun v => s!"  .quad {hex v.toNat}") ++
    [s!"{l "win"}:", "  .byte " ++ ", ".intercalate (c.win.toList.map fun b => hex b.toNat),
      "  .balign 8", s!"{l "out"}:", s!"  .skip {288 + windowSize}"]
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
  let saved := (List.range 6).map fun p => s!"  stp x{19 + 2 * p}, x{20 + 2 * p}, [x9, #{16 * p}]"
  let restored := (List.range 6).map fun p =>
    s!"  ldp x{19 + 2 * p}, x{20 + 2 * p}, [x9, #{16 * p}]"
  let lines :=
    ["  .text", "  .global main", "main:", "  ldr x9, =cosim_saved"] ++ saved ++
    ["  mov x10, sp", "  ldr x11, =cosim_sp", "  str x10, [x11]"] ++
    parts.flatMap (·.1) ++
    ["  ldr x9, =cosim_saved"] ++ restored ++ ["  b cosim_print", "  .ltorg",
      "  .data", "  .balign 16", "cosim_win:", s!"  .skip {windowSize}", "cosim_sp:", "  .quad 0",
      "cosim_saved:", "  .skip 96", "  .balign 8", "  .global cosim_count", "cosim_count:",
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
  if toks.size ≠ 74 then throw s!"a line of {toks.size} fields"
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
  let instr ← match decodeNat w with
    | some i => pure i
    | none => throw s!"the word {hex w} decodes to no form"
  let nzcv := inRegs[32]!
  let s : State :=
    { regs := fun r => inRegs[r.val]!, sp := inRegs[31]!, pc := p,
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
      return regDiffs ++
        (if t.sp = outRegs[31]! then [] else
          [s!"sp {hex outRegs[31]!.toNat}, model {hex t.sp.toNat}"]) ++
        (if UInt64.ofNat (flags * 0x10000000) = outRegs[32]! then [] else
          [s!"nzcv {hex outRegs[32]!.toNat}, model {hex (flags * 0x10000000)}"]) ++
        (if t.pc = landed then [] else
          [s!"pc {hex landed.toNat}, model {hex t.pc.toNat}"]) ++
        winDiffs |>.map (s!"{repr instr}: " ++ ·)

end TestSupport.A64
