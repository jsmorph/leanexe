import LeanExe.A64.Wasi
import LeanExe.A64.Proof.WasiLaunch

/-!
A process that meets the premises of the file theorems of an executable that `genWasiElf` writes,
for the witnesses of the executables' corollaries.  `loadedMem b t d stack` holds, below `2^32`, the
`t` bytes of the text segment of the file `b` at 0x400000 and the `d` bytes of its data segment at
0x410000, as Linux's loader places the two segments that `genWasiElf` writes, with zeros elsewhere,
and from `2^32` on the bytes `stack` and zeros after them.  `loadedMem_loaded` states that it meets
`ElfLoaded` for a file whose program headers are those two segments, and `loadedMem_initial` that it
meets `InitialStack` at SP `2^32` when `stackMem stack`, which holds only the stack, does.
`witnessStack` is the initial stack at `2^32` of the arguments `witnessArgs`, `h` and `1`, with no
environment, and `loadedMem_stack` states that `loadedMem` with that stack meets `InitialStack` with
the top `witnessTop`.  `witnessProc` is the process with a memory, the program counter at the entry,
SP at `2^32`, every other register 0, and no event.
-/

namespace TestSupport.A64.ElfWitness

open LeanExe LeanExe.A64

/-- The arguments of the witnesses: `h` and `1`. -/
def witnessArgs : List (List UInt8) := [[104], [49]]

/-- The initial stack of `witnessArgs` at `2^32`: `argc`, 2; the pointers to `h` at
`2^32 + 40` and to `1` at `2^32 + 42`; the zero words that end `argv` and `envp`; and the strings
`h` and `1`, each with its zero byte. -/
def witnessStack : List UInt8 :=
  [2, 0, 0, 0, 0, 0, 0, 0, 40, 0, 0, 0, 1, 0, 0, 0, 42, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 104, 0, 49, 0]

/-- The top of the witnesses' initial stack. -/
def witnessTop : UInt64 := 2 ^ 32 + 4096

/-- The memory that holds the bytes `stack` from `2^32` on and zeros elsewhere. -/
def stackMem (stack : List UInt8) (a : UInt64) : UInt8 :=
  if a.toNat < 2 ^ 32 then 0 else stack.getD (a.toNat - 2 ^ 32) 0

/-- The memory that holds, below `2^32`, the `t` bytes of the text segment of the file `b` at
0x400000 and the `d` bytes of its data segment at 0x410000, with zeros elsewhere, and from `2^32`
on the bytes `stack` and zeros after them. -/
def loadedMem (b : Nat → UInt8) (t d : Nat) (stack : List UInt8) (a : UInt64) : UInt8 :=
  if a.toNat < 2 ^ 32 then
    if 0x400000 ≤ a.toNat ∧ a.toNat < 0x400000 + t then b (a.toNat - 0x400000)
    else if 0x410000 ≤ a.toNat ∧ a.toNat < 0x410000 + d then b (0x10000 + (a.toNat - 0x410000))
    else 0
  else stack.getD (a.toNat - 2 ^ 32) 0

/-- The process with the memory `mem`, the program counter at the entry, SP at `2^32`, every other
register 0, and no event. -/
def witnessProc (mem : UInt64 → UInt8) : Proc :=
  ⟨⟨fun _ => 0, fun _ => 0, 2 ^ 32, wasiEntry, false, false, false, false, mem, ⟨[], 0, 0⟩⟩, 0, []⟩

theorem loadedMem_loaded {b : Nat → UInt8} {t d memsz : Nat} {stack : List UInt8}
    (segments : elfSegments b =
      [⟨1, 5, 0, 0x400000, t, t⟩, ⟨1, 6, 0x10000, 0x410000, d, memsz⟩])
    (text : 0x400000 + t ≤ 0x410000) (high : 0x410000 + memsz ≤ 2 ^ 32) :
    ElfLoaded b (loadedMem b t d stack) := by
  intro seg member _ j inside
  rw [segments] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · simp only at inside ⊢
    have wide : (UInt64.ofNat (0x400000 + j)).toNat = 0x400000 + j :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
    simp only [loadedMem, wide]
    rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega)]
    exact congrArg b (by omega)
  · simp only at inside ⊢
    have wide : (UInt64.ofNat (0x410000 + j)).toNat = 0x410000 + j :=
      UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
    simp only [loadedMem, wide]
    rw [ite_eq_left (by omega), ite_eq_right (by omega)]
    by_cases low : j < d
    · rw [ite_eq_left (by omega), ite_eq_left low]
      exact congrArg b (by omega)
    · rw [ite_eq_right (by omega), ite_eq_right low]

theorem stackMem_stack :
    InitialStack witnessArgs [] (2 ^ 32) witnessTop (stackMem witnessStack) where
  above := by decide
  below := by decide
  words := by decide
  argc := by decide +kernel
  argv := by
    intro i h
    unfold StringAt
    have : i = 0 ∨ i = 1 := by
      simp only [witnessArgs, List.length_cons, List.length_nil] at h
      omega
    rcases this with rfl | rfl <;>
      simp only [witnessArgs, List.getElem_cons_zero, List.getElem_cons_succ] <;> decide +kernel
  argvEnd := by decide +kernel
  envp := fun _ h => absurd h (Nat.not_lt_zero _)
  envpEnd := by decide +kernel

theorem loadedMem_initial {args environ : List (List UInt8)} {top : UInt64} {stack : List UInt8}
    (b : Nat → UInt8) (t d : Nat) (h : InitialStack args environ (2 ^ 32) top (stackMem stack)) :
    InitialStack args environ (2 ^ 32) top (loadedMem b t d stack) :=
  h.congr fun a high => by
    simp only [loadedMem, stackMem, Nat.not_lt.mpr high, ↓reduceIte]

theorem loadedMem_stack (b : Nat → UInt8) (t d : Nat) :
    InitialStack witnessArgs [] (2 ^ 32) witnessTop (loadedMem b t d witnessStack) :=
  loadedMem_initial b t d stackMem_stack

end TestSupport.A64.ElfWitness
