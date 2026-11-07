import Std.Data.HashMap
import LeanExe.M7.Div
import LeanExe.M7.Image
import TestSupport.M7.Asm
import TestSupport.M7.Crc
import TestSupport.Bare.Req
import Demos.Energy.Loop

/-!
The instruction counts of the windows of the programs with requests that `LeanExe/M7/Gen.lean`
generates, the echo's steps `usart3Tick` and `cmsdkTick`, the gateway's steps `gwTickUsart3`
and `gwTick`, and the CRC-32 steps `crcUsart3Tick` and `crcCmsdkTick`, measured by running the
generated code in the model of `LeanExe/M7/Machine.lean`.  A window runs from the loop's head of
`main` to its next arrival there: the call of the step and the request's register access.

`runProgram` places the code at `codeBase`, in the ITCM alias of the board's flash, with SP at the
top of DTCM and DTCM as the only Normal memory.  For a program with an area, the stack's limit is
the area's end and DTCM starts with the area's first bytes, `areaPrefixBytes` of
`LeanExe/Area.lean`, the bytes that the setup of `LeanExe/M7/Setup.lean` writes; every other byte
is 0.  The run executes the code instruction by instruction with `exec`, the model's step after
its fetch and decoding.  The code never changes, so the decoding of
every halfword address is computed once, by the model's `decode`, before the run.  The model's
registers and memory are functions, and a step builds them from an array of registers and a byte
array of DTCM and writes the step's result back to those arrays, so that each step takes the same
time.  The far end of the UART answers each read of a device register: the status register shows
a received byte while bytes remain and a transmitter with room, except that the first status read
before the first byte of each input record and the first before the first byte of each output
record show neither, so that every kind of window occurs.  A read of the receive register takes
the next input byte, and a write of the transmit register appends to the output.

At each return from the step, the run compares the step's results in `main`'s outgoing area with
the words of the state and the request that the step computes in native Lean, and at the end it
compares the output with the expected bytes: for the echo, the input with bit 5 of each byte
flipped, and for CRC-32, the low byte of the CRC-32 of each prefix of the input, which `crc32Bits`
computes bit by bit with the reflected polynomial `0xEDB88320`.  The program holds the code of
`udivmod64`, which
the run does not execute: at its entry the run sets r0:r1 to the quotient and r2:r3 to the
remainder of Lean's `UInt64` division, sets r4 to r7 to a marker word, returns to LR, and counts
the call by the routine's path, both high words 0, the divisor's low word 0, or the loop, so that
the windows' counts exclude the routine's instructions.

`longest` computes, over the generated code, the largest number of instructions on a path from a
function's entry to its `BX LR`, with a call costing its callee's longest path and each call of
`udivmod64` costing nothing, and the largest number of calls of `udivmod64` on a path.  It fails on
a backward branch, so it succeeds only on loop-free code.
-/

namespace TestSupport.M7.Windows

open LeanExe.M7 Wasm

def memBase : UInt32 := 0x20000000
def memSize : UInt32 := 0x20000
def stackTop : UInt32 := 0x20020000
def stackLimit : UInt32 := 0x20000000
def devBase : UInt32 := 0x40000000
def codeBase : UInt32 := 0x00200200

/-- DTCM as Normal memory and the device window of `lx_reg`. -/
def platform : Platform :=
  { normal := fun b => b - memBase < memSize, device := fun a => a - devBase < 0x40000 }

/-- A UART in `lx_reg`, as `Uart` of `LeanExe/Requests/Records.lean` has it. -/
structure Port where
  rx : UInt64
  tx : UInt64
  status : UInt64
  rxFull : UInt64
  txMask : UInt64
  txRoom : UInt64

def usart3 : Port := ⟨0x1209, 0x120A, 0x1207, 0x20, 0x80, 0x80⟩
def cmsdk : Port := ⟨0x1000, 0x1000, 0x1001, 2, 1, 0⟩

/-- A program with requests: its module, the index of its step, the step's state type, initial
state, words, and native step, its UART, the phase of a state, the kind of a window from the
state and the last value, the bytes of an input record and of an output record, the stack's limit,
the bytes of DTCM from its base at the start, and the expected output for an input. -/
structure Prog where
  name : String
  module : Module
  k : Nat
  G : Type
  s0 : G
  words : G → List UInt64
  tick : G → UInt64 → G × UInt64
  port : Port
  phase : G → UInt64
  kind : G → UInt64 → String
  inRec : Nat
  outRec : Nat
  limit : UInt32
  start : List UInt8
  answer : Array UInt8 → Array UInt8

def echoKind (p : Port) (s v : UInt64) : String :=
  match s &&& 255 with
  | 0 => if v &&& p.rxFull != 0 then "rxne" else "idle"
  | 1 => "byte"
  | 2 => if v &&& p.txMask == p.txRoom then "tx" else "txwait"
  | _ => "sent"

def gwKind (p : Port) (f : Demos.Energy.GwFrame) (v : UInt64) : String :=
  if f.phase == 0 then (if v &&& p.rxFull != 0 then "rxne" else "idle")
  else if f.phase == 1 then
    (if f.nbyte < 7 then "byte" else if f.nword < 17 then "word" else "tick")
  else if f.phase == 2 then (if v &&& p.txMask == p.txRoom then "tx" else "txwait")
  else if f.nbyte < 7 then "sent" else if f.nword < 5 then "sentword" else "sentrecord"

/-- The CRC-32 register after the byte `b` from the register `r`, bit by bit with the reflected
polynomial `0xEDB88320`. -/
def crc32Bits (r : UInt32) (b : UInt8) : UInt32 :=
  (List.range 8).foldl (fun c _ => if c &&& 1 = 1 then (c >>> 1) ^^^ 0xEDB88320 else c >>> 1)
    (r ^^^ b.toUInt32)

/-- The replies of the CRC-32 step to the bytes `input`: the low byte of the CRC-32 of each
prefix. -/
def crcReplies (input : Array UInt8) : Array UInt8 :=
  (input.foldl (fun (r, out) b => let r' := crc32Bits r b; (r', out.push (~~~r').toUInt8))
    ((0xFFFFFFFF : UInt32), #[])).2

def echoProg (name : String) (k : Nat) (tick : UInt64 → UInt64 → UInt64 × UInt64) (p : Port) :
    Prog :=
  { name, module := TestSupport.Bare.reqCompiled.module, k, G := UInt64, s0 := 3,
    words := fun s => [s], tick, port := p, phase := fun s => s &&& 255, kind := echoKind p,
    inRec := 1, outRec := 1, limit := stackLimit, start := [],
    answer := fun input => input.map (· ^^^ 0x20) }

def gwProg (name : String) (k : Nat) (tick : Demos.Energy.GwFrame → UInt64 →
    Demos.Energy.GwFrame × UInt64) (p : Port) : Prog :=
  { name, module := Demos.Energy.gwCompiled.module, k, G := Demos.Energy.GwFrame,
    s0 := Demos.Energy.gwInit, words := Demos.Energy.gwWords, tick, port := p,
    phase := fun f => f.phase, kind := gwKind p, inRec := 144, outRec := 48, limit := stackLimit,
    start := [], answer := fun _ => #[] }

def crcProg (name : String) (m : Module) (tick : UInt64 → UInt64 → UInt64 × UInt64) (p : Port) :
    Prog :=
  { name, module := m, k := 5, G := UInt64, s0 := TestSupport.M7.Crc.crcInit,
    words := fun s => [s], tick, port := p, phase := fun s => s &&& 255, kind := echoKind p,
    inRec := 1, outRec := 1, limit := areaEnd, start := LeanExe.areaPrefixBytes m,
    answer := crcReplies }

def programs : List Prog :=
  [echoProg "echo-usart3" 9 TestSupport.Bare.usart3Tick usart3,
    echoProg "echo-cmsdk" 5 TestSupport.Bare.cmsdkTick cmsdk,
    gwProg "gateway-usart3" 34 Demos.Energy.gwTickUsart3 usart3,
    gwProg "gateway-cmsdk" 33 Demos.Energy.gwTick cmsdk,
    crcProg "crc-usart3" TestSupport.M7.Crc.crcStepCompiled.module
      TestSupport.M7.Crc.crcUsart3Tick usart3,
    crcProg "crc-cmsdk" TestSupport.M7.Crc.crcCmsdkCompiled.module
      TestSupport.M7.Crc.crcCmsdkTick cmsdk]

/-- The generated program of `P`, with the code of `udivmod64`. -/
def generate (P : Prog) : GenM (List Instr) :=
  genProgram P.module P.k (P.words P.s0) codeBase P.limit devBase udivmod64

/-- The address of the loop's head of `main`. -/
def headOf (P : Prog) : UInt32 := after codeBase (mainStart (P.words P.s0))

/-- The functions of `P`'s program, with their entries, as `genProgram` lays them out, the end of
the functions, and the address of `udivmod64` after the trap stubs. -/
def layout (P : Prog) : GenM (List (Nat × Function) × List (Nat × UInt32 × List ValueType ×
    List ValueType) × (Nat → Option (Nat × Nat)) × UInt32 × UInt32) := do
  let fs ← (LeanExe.CallGraph.reachFrom P.module P.k).mapM (LeanExe.CallGraph.funcOf P.module)
  let sig := LeanExe.CallGraph.sigIn (LeanExe.CallGraph.callTargets P.module P.k) fs
  let first := after codeBase (mainSize (P.words P.s0))
  let traps := endOf sig first fs
  let area ← areaOf P.module fs P.limit
  return (fs, entriesFrom sig first fs, sig, traps, (progShared traps P.limit area).udivmod)

/-- The address of `udivmod64` in `P`'s program. -/
def divOf (P : Prog) : GenM UInt32 := do
  let (_, _, _, _, divA) ← layout P
  return divA

/-- The name that the module exports for function `j`, or its index. -/
def nameOf (m : Module) (j : Nat) : String :=
  match m.exports.find? (·.funcIdx = j) with
  | some e => e.name
  | none => s!"f{j}"

/-- One line for each function of `P`'s program: its parameters, results, declared and named
locals, outgoing slots, operand slots, frame size, largest offset from SP, and code size. -/
def frames (P : Prog) : GenM (List String) := do
  let (fs, entries, sig, _, _) ← layout P
  return fs.map fun (j, f) =>
    let fr := frameOf sig f
    let p := f.params.length
    let r := f.results.length
    let entry := ((entries.find? (·.1 = j)).map (·.2.1)).getD 0
    s!"{nameOf P.module j} index {j} entry {entry} params {p} results {r} " ++
      s!"locals {f.locals.length} named {fr.named.length} out {fr.out} height {fr.height} " ++
      s!"frame {fr.size} reach {fr.size + 8 * max p r - 4} units {functionSize sig f}"

/-- The halfwords of the code `is`. -/
def halfwords (is : List Instr) : Array UInt16 := (is.flatMap encode).toArray

/-- The instruction that `decode` reads at each halfword of `hs`. -/
def decodeAll (hs : Array UInt16) : Array (Option Instr) :=
  Array.ofFn fun j : Fin hs.size =>
    (decode (hs[j] :: (hs[j.val + 1]?).toList)).map (·.1)

/-- The machine's state outside the model: r0 to r12, SP, LR, the program counter, the flags, and
DTCM's bytes. -/
structure Machine where
  regs : Array UInt32
  sp : UInt32
  lr : UInt32
  pc : UInt32
  n : Bool
  z : Bool
  c : Bool
  v : Bool
  mem : ByteArray

/-- The address of a word load by `i` in the state with registers `regs` and SP `sp`. -/
def loadAddr (regs : Array UInt32) (sp : UInt32) : Instr → Option UInt32
  | .ldr _ n imm => some (regs[n.val]! + UInt32.ofNat imm.val)
  | .ldrSp _ imm | .ldrLr imm => some (sp + UInt32.ofNat imm.val)
  | _ => none

/-- The address of a word store by `i`. -/
def storeAddr (regs : Array UInt32) (sp : UInt32) : Instr → Option UInt32
  | .str _ n imm => some (regs[n.val]! + UInt32.ofNat imm.val)
  | .strSp _ imm | .strLr imm => some (sp + UInt32.ofNat imm.val)
  | _ => none

/-- The machine after `exec` of `i`, with `dev` the value of a device read, and the device
accesses of the step. -/
def execMachine (i : Instr) (dev : UInt32) (m : Machine) : Except String (Machine × List Access) :=
  let ⟨regs, sp, lr, pc, nf, zf, cf, vf, mem⟩ := m
  let st := storeAddr regs sp i
  let s : State :=
    { regs := fun r => regs[r.val]!, sp, lr, pc, nFlag := nf, zFlag := zf, cFlag := cf,
      vFlag := vf,
      mem := fun b => let o := b - memBase; if o < memSize then mem.get! o.toNat else 0,
      trace := [], reads := 0 }
  match exec platform (fun _ => dev) i s with
  | none => .error s!"the model stops at {pc}: {asm i}"
  | some s' =>
      let regs' := Array.ofFn fun r : Fin 13 => s'.regs r
      let bytes := match st with
        | some a =>
            if a - memBase < memSize then some ((a - memBase).toNat, s'.mem a, s'.mem (a + 1),
              s'.mem (a + 2), s'.mem (a + 3)) else none
        | none => none
      let m' : Machine :=
        ⟨regs', s'.sp, s'.lr, s'.pc, s'.nFlag, s'.zFlag, s'.cFlag, s'.vFlag, mem⟩
      let tr := s'.trace
      match bytes with
      | some (o, b0, b1, b2, b3) =>
          .ok ({ m' with mem := ((((m'.mem.set! o b0).set! (o + 1) b1).set! (o + 2) b2).set!
            (o + 3) b3) }, tr)
      | none => .ok (m', tr)

/-- The word of DTCM at `a`. -/
def Machine.word (m : Machine) (a : UInt32) : UInt32 :=
  let o := (a - memBase).toNat
  (m.mem.get! o).toUInt32 ||| (m.mem.get! (o + 1)).toUInt32 <<< 8 |||
    (m.mem.get! (o + 2)).toUInt32 <<< 16 ||| (m.mem.get! (o + 3)).toUInt32 <<< 24

/-- The value of the slot at `a`, its low word first. -/
def Machine.slot (m : Machine) (a : UInt32) : UInt64 :=
  (m.word a).toUInt64 ||| (m.word (a + 4)).toUInt64 <<< 32

/-- The statistics of one kind of window. -/
structure Stat where
  count : Nat := 0
  total : Nat := 0
  least : Nat := 0
  most : Nat := 0
  divFast : Nat := 0
  divLow : Nat := 0
  divLoop : Nat := 0
  divLoopPasses : Nat := 0
  deriving Inhabited

/-- The divisions of a window by `udivmod64`'s path. -/
structure Divs where
  fast : Nat := 0
  low : Nat := 0
  loop : Nat := 0
  passes : Nat := 0

def Stat.add (s : Stat) (n : Nat) (d : Divs) : Stat :=
  { count := s.count + 1, total := s.total + n,
    least := if s.count = 0 then n else min s.least n, most := max s.most n,
    divFast := max s.divFast d.fast, divLow := max s.divLow d.low,
    divLoop := max s.divLoop d.loop, divLoopPasses := max s.divLoopPasses d.passes }

/-- The number of leading zero bits of a 64-bit word. -/
def clz64 (x : UInt64) : Nat := if x = 0 then 64 else 63 - x.toNat.log2

/-- The bytes of a word, the most significant first. -/
def beBytes (w : UInt64) : List UInt8 :=
  (List.range 8).reverse.map fun j => (w >>> (8 * j).toUInt64).toUInt8

/-- The result of a run: the statistics by kind, the number of windows and of instructions, the
first trace of each kind and the longest trace of each traced kind, the output, one line for each
call of `udivmod64` in a window of a traced kind, and a failure, if any. -/
structure Run where
  stats : Std.HashMap String Stat
  windows : Nat
  steps : Nat
  traces : Std.HashMap String (Array String)
  longest : Std.HashMap String (Array String)
  output : Array UInt8
  divisions : Array String
  failure : Option String

/-- The value that the far end of `p` gives a read of the status register: a received byte while
`rxOk` and room in the transmitter while `txOk`. -/
def statusValue (p : Port) (rxOk txOk : Bool) : UInt32 :=
  (if rxOk then p.rxFull else 0).toUInt32 |||
    (if txOk then p.txRoom else p.txMask ^^^ p.txRoom).toUInt32

/-- Runs `P`'s program on the input bytes `input` until the far end has sent every byte, received
`expected.size` bytes, and the step is in phase 0, or until `maxWindows` windows.  It keeps the
trace of the first window of each kind and of the longest window of each kind in `traced`. -/
def runProgram (P : Prog) (input expected : Array UInt8) (maxWindows : Nat)
    (traced : List String) : IO Run := do
  let is ← match generate P with
    | .ok is => pure is
    | .error e => throw <| IO.userError s!"{P.name}: {e}"
  let divA ← match divOf P with
    | .ok a => pure a
    | .error e => throw <| IO.userError e
  let dec := decodeAll (halfwords is)
  let head := headOf P
  let ret := after head 1
  let n := (P.words P.s0).length
  let mut m : Machine :=
    ⟨Array.replicate 13 0, stackTop, 0xFFFFFFFF, codeBase, false, false, false, false,
      ByteArray.mk (P.start.toArray ++ Array.replicate (memSize.toNat - P.start.length) 0)⟩
  let mut stats : Std.HashMap String Stat := {}
  let mut traces : Std.HashMap String (Array String) := {}
  let mut longest : Std.HashMap String (Array String) := {}
  let mut output : Array UInt8 := #[]
  let mut failure : Option String := none
  let mut divisions : Array String := #[]
  let mut windows := 0
  let mut steps := 0
  let mut g := P.s0
  let mut vIn : UInt64 := 0
  let mut pos := 0
  let mut idled := 0
  let mut waited := 0
  let mut startSteps := 0
  let mut kind := "start"
  let mut divs : Divs := {}
  let mut trace : Array String := #[]
  let mut tracing := true
  while failure.isNone do
    if m.pc = head then
      let cnt := steps - startSteps
      let old := stats.getD kind {}
      stats := stats.insert kind (old.add cnt divs)
      if kind ≠ "start" then windows := windows + 1
      if old.count = 0 then traces := traces.insert kind trace
      if kind ∈ traced ∧ cnt > old.most then longest := longest.insert kind trace
      startSteps := steps
      divs := {}
      vIn := m.slot (m.sp + UInt32.ofNat (8 * n))
      kind := P.kind g vIn
      tracing := (stats.getD kind {}).count = 0 ∨ kind ∈ traced
      trace := #[]
      if (pos ≥ input.size ∧ P.phase g == 0 ∧ output.size ≥ expected.size) ∨
          windows ≥ maxWindows then
        break
    if m.pc = ret then
      let got := (List.range (n + 1)).map fun i => m.slot (m.sp + UInt32.ofNat (8 * i))
      let (g', q) := P.tick g vIn
      let want := P.words g' ++ [q]
      if got ≠ want then
        failure := some s!"window {windows}: the step's results {got} differ from {want}"
        break
      g := g'
    if m.pc = divA then
      let x := m.regs[0]!.toUInt64 ||| m.regs[1]!.toUInt64 <<< 32
      let d := m.regs[2]!.toUInt64 ||| m.regs[3]!.toUInt64 <<< 32
      if d = 0 then
        failure := some s!"window {windows}: udivmod64 with divisor 0"
        break
      let passes := if x < d then 0 else clz64 d - clz64 x + 1
      let path := if x >>> 32 = 0 ∧ d >>> 32 = 0 then "fast"
        else if d &&& 0xFFFFFFFF = 0 then "low" else "loop"
      if path = "fast" then divs := { divs with fast := divs.fast + 1 }
      else if path = "low" then divs := { divs with low := divs.low + 1 }
      else divs := { divs with loop := divs.loop + 1, passes := max divs.passes passes }
      if kind ∈ traced then
        divisions := divisions.push
          s!"window {windows} {kind} path {path} dividend {x} divisor {d} passes {passes}"
      let q := x / d
      let rem := x % d
      let mark : UInt32 := 0xDEADBEEF
      let regs := (((((((m.regs.set! 0 q.toUInt32).set! 1 (q >>> 32).toUInt32).set! 2
        rem.toUInt32).set! 3 (rem >>> 32).toUInt32).set! 4 mark).set! 5 mark).set! 6 mark).set! 7
        mark
      if tracing then trace := trace.push s!"{m.pc} udivmod64"
      m := { m with regs := regs, pc := m.lr &&& 0xFFFFFFFE }
      continue
    match dec[(m.pc - codeBase).toNat / 2]? with
    | some (some i) =>
        let la := loadAddr m.regs m.sp i
        let mut dev : UInt32 := 0
        if let some a := la then
          if a - devBase < 0x40000 then
            let reg := ((a - devBase) / 4).toUInt64
            if reg == P.port.status then
              let ph := P.phase g
              let rxGate := ph == 0 ∧ pos < input.size ∧ pos % P.inRec = 0 ∧
                idled ≤ pos / P.inRec
              let txGate := ph == 2 ∧ output.size % P.outRec = 0 ∧
                waited ≤ output.size / P.outRec
              if rxGate then idled := pos / P.inRec + 1
              if txGate then waited := output.size / P.outRec + 1
              dev := statusValue P.port (pos < input.size ∧ !rxGate) !txGate
            else if reg == P.port.rx then
              dev := (input[pos]?.getD 0).toUInt32
              pos := pos + 1
        if tracing then
          let addr := match la, storeAddr m.regs m.sp i with
            | some a, _ => s!" @{a}"
            | _, some a => s!" @{a}"
            | _, _ => ""
          trace := trace.push s!"{m.pc} {asm i}{addr}"
        match execMachine i dev m with
        | .error e => failure := some s!"window {windows}: {e}"
        | .ok (m', acc) =>
            for e in acc do
              if let .write a w := e then
                if ((a - devBase) / 4).toUInt64 == P.port.tx then output := output.push w.toUInt8
            m := m'
            steps := steps + 1
    | _ => failure := some s!"window {windows}: no instruction at {m.pc}"
  if failure.isNone ∧ output ≠ expected.extract 0 output.size then
    failure := some "the output differs from the expected bytes"
  if failure.isNone ∧ output.size ≠ expected.size then
    failure := some s!"{output.size} output bytes against {expected.size}"
  return ⟨stats, windows, steps, traces, longest, output, divisions, failure⟩

/-- The target of the branch `i` at `a`, if `i` branches to an address that it encodes. -/
def targetOf (a : UInt32) : Instr → Option UInt32
  | .bcond _ s j1 j2 imm6 imm11 => some (a + 4 + bcondOffset s j1 j2 imm6 imm11)
  | .b s j1 j2 imm10 imm11 | .bl s j1 j2 imm10 imm11 =>
      some (a + 4 + branchOffset s j1 j2 imm10 imm11)
  | _ => none

/-- A path's length that ends in a trap stub, below every length of a path that returns. -/
def trapped : Int := -1000000000

/-- The longest path of the step of `P`'s program: for each function, the largest number of
instructions from its entry to its `BX LR` and the largest number of calls of `udivmod64` on a
path, with the routine's instructions excluded, as lines, and the length for the step's entry. -/
def longest (P : Prog) : Except String (List String × Int × Nat) := do
  let is ← generate P
  let (fs, entries, _, traps, divA) ← layout P
  let first := after codeBase (mainSize (P.words P.s0))
  let starts : Array (UInt32 × Instr) := Id.run do
    let mut a := codeBase
    let mut out := #[]
    for i in is do
      out := out.push (a, i)
      a := a + UInt32.ofNat (2 * (encode i).length)
    return out
  let next : Std.HashMap UInt32 UInt32 := Id.run do
    let mut h := {}
    for (a, i) in starts do h := h.insert a (a + UInt32.ofNat (2 * (encode i).length))
    return h
  let mut val : Std.HashMap UInt32 (Int × Nat) := {}
  let mut changed := true
  while changed do
    changed := false
    for (a, i) in starts.reverse do
      if a < first ∨ traps ≤ a ∨ val.contains a then continue
      let nx := val.get? (next.getD a 0)
      let tgt (t : UInt32) : Option (Int × Nat) :=
        if traps ≤ t ∧ t < divA then some (trapped, 0) else val.get? t
      let t := (targetOf a i).getD 0
      if (i matches .b .. ∨ i matches .bcond ..) ∧ t ≤ a ∧ first ≤ t then
        throw s!"a backward branch at {a}"
      let r : Option (Int × Nat) := match i with
        | .bxLr => some (1, 0)
        | .b .. => (tgt t).map fun (l, d) => (1 + l, d)
        | .bcond .. =>
            match nx, tgt t with
            | some (l1, d1), some (l2, d2) => some (1 + max l1 l2, max d1 d2)
            | _, _ => none
        | .bl .. =>
            if t = divA then nx.map fun (l, d) => (1 + l, d + 1)
            else match val.get? t, nx with
              | some (l1, d1), some (l2, d2) => some (1 + l1 + l2, d1 + d2)
              | _, _ => none
        | _ => nx.map fun (l, d) => (1 + l, d)
      if let some v := r then
        val := val.insert a v
        changed := true
  let lines := fs.map fun (j, _) =>
    let e := ((entries.find? (·.1 = j)).map (·.2.1)).getD 0
    match val.get? e with
    | some (l, d) => s!"{nameOf P.module j} longest {l} divisions {d}"
    | none => s!"{nameOf P.module j} longest unknown"
  let stepE := ((entries.find? (·.1 = P.k)).map (·.2.1)).getD 0
  match val.get? stepE with
  | some (l, d) => return (lines, l, d)
  | none => throw "the step's longest path is unknown"

end TestSupport.M7.Windows
