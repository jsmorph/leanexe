import TestSupport.Native.Gcd
import LeanExe.Native.Bare
import LeanExe.A64.Gen

/-!
The bare-metal programs of the AArch64 back end, the counterparts of the programs of
`tests/baremetal/programs.sh` that it covers so far: GCD's loop on 1071 and 462.  For each
program `run` places the generated instructions after the exit word at `base`, runs them in the
model from `main` with the stack pointer at `stackTop` and a return address outside the code,
and reports the UART's bytes, the status in X0, and the number of steps when `main` returns.
`assembly` writes the exit word as a branch to `lx_exit` for the linker and the instructions as
words after it, from `main`, which the startup code calls.
-/

namespace TestSupport.A64

open LeanExe.A64

/-- The address of the UART's data register on QEMU's `virt` machine (`tools/baremetal/link.ld`). -/
def uart : UInt64 := 0x09000000

/-- The address of the exit word in `run`, and the top of its stack. -/
def base : UInt64 := 0x40200000
def stackTop : UInt64 := 0x40800000

/-- A program: its name, its instructions, and the bytes it must write. -/
structure Program where
  name : String
  code : Except String (List Instr)
  bytes : List UInt8

def programs : List Program := [
  { name := "gcd"
    code := genProgram TestSupport.Native.Gcd.loopCompiled.module 2 [1071, 462] uart base
    bytes := LeanExe.Native.encodeWord (TestSupport.Native.Gcd.gcd 1071 462) }]

/-- The UART's bytes, X0, and the number of steps when `main` returns to the address below the
code, after at most `fuel` steps from `main` at `base + 4`; or the reason that it did not. -/
def run (code : List Instr) (fuel : Nat) : Except String (List UInt8 × UInt64 × Nat) := do
  let words := (code.map encode).toArray
  let fetch (a : UInt64) : Option UInt32 :=
    if base + 4 ≤ a ∧ (a - base) % 4 = 0 then words[((a - base) / 4).toNat - 1]? else none
  let P : Platform :=
    { normal := fun a => 0x40000000 ≤ a ∧ a < 0x80000000, uart := uart }
  let ret := base - 8
  let mut s : State :=
    { regs := fun r => if r.val = 30 then ret else 0, sp := stackTop, pc := base + 4,
      nFlag := false, zFlag := false, cFlag := false, vFlag := false, mem := fun _ => 0,
      out := [] }
  for k in [0:fuel] do
    if s.pc = ret then return (s.out, s.x 0, k)
    if s.pc = base then throw s!"the exit word with X0 {s.x 0} after {k} steps"
    match step P fetch s with
    | some t => s := t
    | none => throw s!"the model stops at {s.pc} after {k} steps"
  throw s!"no return within {fuel} steps"

/-- The assembly of the program: the exit word, a branch to `lx_exit`, then `main` and the
rest of the instructions. -/
def assembly (code : List Instr) : String :=
  "  .text\n  .balign 4\n  b lx_exit\n  .global main\nmain:\n" ++
    String.join (code.map fun i =>
      s!"  .inst 0x{String.ofList (Nat.toDigits 16 (encode i).toNat)}\n")

end TestSupport.A64
