import TestSupport.Native.Gcd
import LeanExe.Native.Bare
import LeanExe.A64.Gen

/-!
The bare-metal programs of the AArch64 back end, the counterparts of the programs of
`tests/baremetal/programs.sh` that it covers so far: GCD's loop on 1071 and 462.  For each
program `run` places the generated words from `base`, runs them in the model from `main` with
the stack pointer at `stackTop` and a return address outside the code, and reports the UART's
bytes, the status in X0, and the number of steps when `main` returns.  `assembly` writes the
words as an assembly file whose `main` the startup code calls, with the branches to `lx_exit`
as symbolic branches for the linker.
-/

namespace TestSupport.A64

open LeanExe.A64

/-- The address of the UART's data register on QEMU's `virt` machine (`tools/baremetal/link.ld`). -/
def uart : UInt64 := 0x09000000

/-- Where `run` places the code, the top of its stack, and the address it gives `lx_exit`. -/
def base : UInt64 := 0x40200000
def stackTop : UInt64 := 0x40800000
def exitAddr : UInt64 := base - 4

/-- A program: its name, its items, and the bytes it must write. -/
structure Program where
  name : String
  items : Except String (List Item)
  bytes : List UInt8

def programs : List Program := [
  { name := "gcd"
    items := genProgram TestSupport.Native.Gcd.loopCompiled.module 2 [1071, 462] uart
    bytes := LeanExe.Native.encodeWord (TestSupport.Native.Gcd.gcd 1071 462) }]

/-- The encoding of a placed word at `here`, with `B` to `exitAddr` for the branch to
`lx_exit`. -/
def resolve (here : UInt64) : Word → Except String UInt32
  | .inst w => pure w
  | .exit => do
      let f ← branchField 26 here exitAddr
      return encode (.b ⟨f % 67108864, Nat.mod_lt _ (by decide)⟩)

/-- The UART's bytes, X0, and the number of steps when `main` returns to the address below the
code, after at most `fuel` steps from `main` at `base`; or the reason that it did not. -/
def run (words : List Word) (fuel : Nat) : Except String (List UInt8 × UInt64 × Nat) := do
  let mut code := #[]
  for (w, i) in words.zipIdx do
    code := code.push (← resolve (base + UInt64.ofNat (4 * i)) w)
  let fetch (a : UInt64) : Option UInt32 :=
    if base ≤ a ∧ (a - base) % 4 = 0 then code[((a - base) / 4).toNat]? else none
  let P : Platform :=
    { normal := fun a => 0x40000000 ≤ a ∧ a < 0x80000000, uart := uart }
  let ret := base - 8
  let mut s : State :=
    { regs := fun r => if r.val = 30 then ret else 0, sp := stackTop, pc := base,
      nFlag := false, zFlag := false, cFlag := false, vFlag := false, mem := fun _ => 0,
      out := [] }
  for k in [0:fuel] do
    if s.pc = ret then return (s.out, s.x 0, k)
    if s.pc = exitAddr then throw s!"lx_exit with X0 {s.x 0} after {k} steps"
    match step P fetch s with
    | some t => s := t
    | none => throw s!"the model stops at {s.pc} after {k} steps"
  throw s!"no return within {fuel} steps"

/-- The assembly of the words, with `main` at the first. -/
def assembly (words : List Word) : String :=
  "  .text\n  .balign 4\n  .global main\nmain:\n" ++
    String.join (words.map fun
      | .inst w => s!"  .inst 0x{String.ofList (Nat.toDigits 16 w.toNat)}\n"
      | .exit => "  b lx_exit\n")

end TestSupport.A64
