import LeanExe.A64.Boot
import LeanExe.A64.Encode

/-!
Facts about runs of the boot model.  `BootReach.trans` joins runs.  While the MMU is off in both
the written and the effective `SCTLR_EL1`, every instruction fetch succeeds, so `boot_plain` and
`boot_sys` take one step of an instruction that `CodeAt`-style premises place at the program
counter: an instruction that touches no memory, or a system instruction.
-/

namespace LeanExe.A64

variable {h : Hw} {R : UInt64 → Bool} {code : UInt64 → Option UInt32}

theorem BootReach.trans {b c d : Boot} (h1 : BootReach h R code b c)
    (h2 : BootReach h R code c d) : BootReach h R code b d := by
  induction h1 with
  | refl => exact h2
  | next hs _ ih => exact .next hs (ih h2)

theorem BootReach.single {b c : Boot} (hs : BootStep h R code b c) : BootReach h R code b c :=
  .next hs (.refl _)

/-- `SysReg.ofCode` gives back every register from the 15 bits of its field. -/
theorem SysReg.ofCode_code (r : SysReg) : SysReg.ofCode (r.code % 32768) = some r := by
  cases r <;> rfl

/-- The MMU is off in both copies of `SCTLR_EL1`. -/
def Boot.mmuOff (b : Boot) : Prop := b.eff.sctlr &&& 1 = 0 ∧ b.written.sctlr &&& 1 = 0

/-- A step of an instruction that touches no memory while the MMU is off. -/
theorem boot_plain {b : Boot} {i : Instr} {c : State} (hc : code b.core.pc = some (encode i))
    (hsp : b.spSel = true) (hoff : b.mmuOff) (hn : i.isSys = false)
    (hm : i.accessesMemory = false) (he : exec noMemory i b.core = some c)
    (ht : c.pc.toNat < 2 ^ 55) : BootStep h R code b { b with core := c } :=
  .plain hc (decode_encode i) hsp (.inl hoff.1) (.inl hoff.2) hn hm he (.inl ht)

/-- A step of a system instruction while the MMU is off. -/
theorem boot_sys {b b' : Boot} {i : Instr} (hc : code b.core.pc = some (encode i))
    (hsp : b.spSel = true ∨ i = .spsel1) (hoff : b.mmuOff) (he : sysExec h i b = some b') :
    BootStep h R code b b' :=
  .sys hc (decode_encode i) hsp (.inl hoff.1) (.inl hoff.2) he

end LeanExe.A64
