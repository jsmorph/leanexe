import LeanExe.A64.Machine

/-!
The model of the machine from the entry of an arm64 Linux Image, through the startup that turns on
the MMU, to the program and its exit.  The entry state that Linux's `booting.rst` documents has the
MMU off, so every data access is Device memory, and leaves the system registers at values that
firmware chose.  The startup writes complete values to the registers that translation and traps
read, synchronizes them with `ISB`, invalidates the TLBs, and turns the MMU on with one level-1
translation table of 1 GiB blocks.  `BootStep` takes one step of that machine.

The state `Boot` extends the program's `State` with two copies of the writable system registers:
`written`, which `MSR` sets, and `eff`, the values that translation and the traps of floating point
use, which an `ISB` makes equal to `written`.  An instruction must be fetched successfully under
both copies, since the architecture may use either until an `ISB`.  `FPCR` is among the copied
registers, although the architecture puts its writes in effect in program order, so the model is
stricter than the architecture there.  `tlb` records whether the TLBs may hold entries that a walk
under `eff` would not give: a write of a register that a TLB may cache makes it `unknown`,
`TLBI VMALLE1` after an `ISB` makes it `pending`, and a `DSB` makes a `pending` one `clean`.
`spSel` records that SP_EL1 is the stack pointer, which every step but `MSR SPSel, #1` requires.
`uartDone` records that every byte store to the UART has completed, which a `DSB` ensures.

`classify` gives the type of memory at an address from the table's bytes for the one configuration
that the model covers, `covered`, and `none` for every other configuration, descriptor, or address,
where the model stops.  The covered configuration includes floating point enabled with `cpacrValue`
and `fpcrValue`.  A system instruction steps by `sysExec`, in which `MSR FPCR` stops unless both
copies of `CPACR_EL1` let EL1 access floating point.  Another instruction that touches no memory
steps by `exec` while the MMU may be off, when its next program counter lies below 2^55 or address
tagging is off, since a branch under tagging changes the top byte of a larger target, and, for a
floating-point instruction, when both copies of `CPACR_EL1` and `FPCR` hold their covered values.
Every instruction other than a system instruction steps by `exec` with the platform `Boot.platform`
once translation is on in the covered configuration with valid TLBs: its Normal memory is the
writable Normal memory of the table outside the protected bytes `R`, the image's code, vectors, and
table, which no store may change, so the fixed map of code words stays the memory's, and its UART is
QEMU's at `uartAddr`, which the table must map as writable Device memory.  `HVC` has no step: a run
that reaches it with `X0` holding PSCI's `SYSTEM_OFF` has finished, and the platform's firmware
turns the machine off.
-/

namespace LeanExe.A64

/-- The system registers that the startup writes or reads. -/
inductive SysReg where
  | sctlr | cpacr | mair | tcr | tcr2 | ttbr0 | vbar | fpcr | currentEL | mmfr3
  deriving DecidableEq, Repr

/-- The field `op0<0>:op1:CRn:CRm:op2` of `MSR` and `MRS` for each register: `SCTLR_EL1`,
`CPACR_EL1`, `MAIR_EL1`, `TCR_EL1`, `TCR2_EL1`, `TTBR0_EL1`, `VBAR_EL1`, `FPCR`, `CurrentEL`, and
`ID_AA64MMFR3_EL1`. -/
def SysReg.code : SysReg → Nat
  | .sctlr => 0x4080
  | .cpacr => 0x4082
  | .mair => 0x4510
  | .tcr => 0x4102
  | .tcr2 => 0x4103
  | .ttbr0 => 0x4100
  | .vbar => 0x4600
  | .fpcr => 0x5A20
  | .currentEL => 0x4212
  | .mmfr3 => 0x403B

/-- The register whose field is `k`, if the model covers it. -/
def SysReg.ofCode (k : Nat) : Option SysReg :=
  [SysReg.sctlr, .cpacr, .mair, .tcr, .tcr2, .ttbr0, .vbar, .fpcr, .currentEL, .mmfr3].find?
    (·.code = k)

/-- The values of the writable system registers. -/
structure Sys where
  sctlr : UInt64
  cpacr : UInt64
  mair : UInt64
  tcr : UInt64
  tcr2 : UInt64
  ttbr0 : UInt64
  vbar : UInt64
  fpcr : UInt64
  deriving DecidableEq

/-- What the TLBs may hold for the EL1&0 translation regime. -/
inductive Tlb where
  | unknown
  | pending
  | clean
  deriving DecidableEq

/-- What the model leaves open about the processor: the value of `ID_AA64MMFR3_EL1`. -/
structure Hw where
  mmfr3 : UInt64

/-- The processor implements `TCR2_EL1` (FEAT_TCR2): `ID_AA64MMFR3_EL1.TCRX` is not 0. -/
def Hw.tcrx (h : Hw) : Bool := h.mmfr3 &&& 0xF != 0

/-- The machine during the startup and after it. -/
structure Boot where
  core : State
  written : Sys
  eff : Sys
  tlb : Tlb
  spSel : Bool
  uartDone : Bool

/-- `s` with `r` written as `v`, or `none` for a register that `MSR` cannot write: `CurrentEL`,
`ID_AA64MMFR3_EL1`, and `TCR2_EL1` on a processor without FEAT_TCR2. -/
def Sys.set (h : Hw) (s : Sys) : SysReg → UInt64 → Option Sys
  | .sctlr, v => some { s with sctlr := v }
  | .cpacr, v => some { s with cpacr := v }
  | .mair, v => some { s with mair := v }
  | .tcr, v => some { s with tcr := v }
  | .tcr2, v => if h.tcrx then some { s with tcr2 := v } else none
  | .ttbr0, v => some { s with ttbr0 := v }
  | .vbar, v => some { s with vbar := v }
  | .fpcr, v => some { s with fpcr := v }
  | .currentEL, _ | .mmfr3, _ => none

/-- A write of `r` that changes `s` to `s'` leaves the TLBs' contents valid: a write of
`VBAR_EL1`, `CPACR_EL1`, or `FPCR`, which no TLB caches, or of `SCTLR_EL1` that changes no field
but M. -/
def keepsTlb (r : SysReg) (s s' : Sys) : Bool :=
  match r with
  | .vbar | .cpacr | .fpcr => true
  | .sctlr => s.sctlr ||| 1 == s'.sctlr ||| 1
  | _ => false

/-- The value of `SCTLR_EL1` with the MMU on: M, C, I, and SA set, the fields that are RES1 when
their feature is absent set, and every other field clear. -/
def sctlrOn : UInt64 := 0x30D0198D

/-- The value of `TCR_EL1`: a 32-bit input address space from `TTBR0_EL1` with 4 KiB granules,
walks Write-Back and Inner Shareable, `TTBR1_EL1` walks disabled, and 32-bit output addresses. -/
def tcrValue : UInt64 := 0x80A03520

/-- The value of `MAIR_EL1`: attribute 0 Device-nGnRnE, attribute 1 Normal Write-Back. -/
def mairValue : UInt64 := 0xFF00

/-- The value of `CPACR_EL1`: FPEN, bits 21 and 20, `0b11`, so that no access to the SIMD and
floating-point registers, `FPCR`, or `FPSR` traps at EL1, and every other field clear, which keeps
SVE and SME instructions trapped. -/
def cpacrValue : UInt64 := 0x300000

/-- The value of `FPCR`: DN set, so that every NaN result is the default NaN, and every other field
clear: rounding to nearest with ties to even, no flushing of denormalized numbers, AH and NEP clear,
and every trap enable clear. -/
def fpcrValue : UInt64 := 0x02000000

/-- `CPACR_EL1.FPEN` lets EL1 access the SIMD and floating-point registers and `FPCR`: its bit 20 is
set, since the values `0b00` and `0b10` trap those accesses at EL1. -/
def Sys.fpAccess (s : Sys) : Bool := s.cpacr &&& 0x100000 != 0

/-- Floating point is enabled with the covered control: `CPACR_EL1` holds `cpacrValue` and `FPCR`
holds `fpcrValue`. -/
def Sys.fpOn (s : Sys) : Bool := s.cpacr == cpacrValue && s.fpcr == fpcrValue

/-- Address tagging is off: `TCR_EL1.TBI0` and `TBI1`, bits 37 and 38, are clear, so a branch
keeps the top byte of its target. -/
def Sys.untagged (s : Sys) : Bool := s.tcr &&& 0x6000000000 == 0

/-- `s` is the configuration that the model covers: translation with the image's table and
floating point enabled with the covered control. -/
def Sys.covered (h : Hw) (s : Sys) : Bool :=
  s.sctlr == sctlrOn && s.tcr == tcrValue && s.mair == mairValue && (!h.tcrx || s.tcr2 == 0) &&
    s.ttbr0 % 32 == 0 && s.ttbr0 < 0x100000000 && s.fpOn

/-- A type of memory: Device memory or Normal memory, each with or without write permission at EL1,
and Normal memory with or without execute permission at EL1. -/
inductive MemType where
  | device (write : Bool)
  | normal (write exec : Bool)
  deriving DecidableEq

/-- The bits of a level-1 block descriptor that the model reads: valid, AttrIndx, AP[2], SH, AF,
the output address below 2 ^ 32, PXN, and UXN.  Every other bit must be 0. -/
def descMask : UInt64 := 0x00600000C000079D

/-- The type of memory that translation under `s` gives the address `a`, from the table in `mem`,
or `none` where the model does not cover the result: a configuration other than the covered one,
an address at or above 2 ^ 32, which faults, and a descriptor that is invalid, has its access flag
clear, sets a bit outside `descMask`, maps `a` to another address, or names an attribute other than
Device-nGnRnE or Normal Write-Back. -/
def classify (h : Hw) (s : Sys) (mem : UInt64 → UInt8) (a : UInt64) : Option MemType :=
  if !s.covered h || 0x100000000 ≤ a then none
  else
    let d := load64 mem (s.ttbr0 + (8 : UInt64) * (a >>> (30 : UInt64)))
    if d &&& ~~~descMask != 0 || d &&& 1 == 0 || d &&& 0x400 == 0 ||
        d &&& 0xC0000000 != a &&& 0xC0000000 then none
    else
      let attr := (s.mair >>> ((8 : UInt64) * ((d >>> (2 : UInt64)) &&& 7))) &&& 0xFF
      if attr = 0xFF then some (.normal (d &&& 0x80 == 0) (d &&& 0x0020000000000000 == 0))
      else if attr = 0 then some (.device (d &&& 0x80 == 0))
      else none

/-- An instruction fetch at `a` succeeds under `s`: with the MMU off every fetch is from Normal
memory, and with it on the TLBs must be valid and translation must give executable Normal
memory. -/
def fetchOk (h : Hw) (s : Sys) (tlb : Tlb) (mem : UInt64 → UInt8) (a : UInt64) : Prop :=
  s.sctlr &&& 1 = 0 ∨ (tlb = .clean ∧ ∃ w, classify h s mem a = some (.normal w true))

/-- The address of the UART's data register on QEMU's virt machine. -/
def uartAddr : UInt64 := 0x09000000

/-- The memory type is writable Normal memory. -/
def writableNormal : Option MemType → Bool
  | some (.normal true _) => true
  | _ => false

/-- The platform of the program under `b`: writable Normal memory outside the protected bytes
`R`, and the UART at `uartAddr`. -/
def Boot.platform (h : Hw) (R : UInt64 → Bool) (b : Boot) : Platform :=
  { normal := fun a => !R a && writableNormal (classify h b.eff b.core.mem a), uart := uartAddr }

/-- The platform with no memory, for the instructions that touch none. -/
def noMemory : Platform := { normal := fun _ => false, uart := uartAddr }

/-- A system instruction. -/
def Instr.isSys : Instr → Bool
  | .msr _ _ | .mrs _ _ | .spsel1 | .isb | .dsbIsh | .dsbSy | .tlbiVmalle1 | .hvc0 => true
  | _ => false

/-- An instruction other than a system instruction that `CPACR_EL1.FPEN` traps, one that accesses
the SIMD and floating-point registers: the double-precision and single-precision forms. -/
def Instr.isFP : Instr → Bool
  | .fmovDX _ _ | .fmovXD _ _ | .fadd _ _ _ | .fsub _ _ _ | .fmul _ _ _ | .fdiv _ _ _
  | .fsqrt _ _ | .ucvtf _ _ | .fcmp _ _ | .fmovSW _ _ | .fmovWS _ _ | .faddS _ _ _
  | .fsubS _ _ _ | .fmulS _ _ _ | .fdivS _ _ _ | .fsqrtS _ _ | .frintnS _ _ | .ucvtfSX _ _
  | .scvtfSW _ _ | .fcvtzuXS _ _ | .fcvtzsWS _ _ | .fcmpS _ _ => true
  | _ => false

/-- A load or a store. -/
def Instr.accessesMemory : Instr → Bool
  | .ldr _ _ _ | .str _ _ _ | .strb _ _ _ => true
  | _ => false

/-- `MSR` of `r` traps at EL1 under `b`: `MSR FPCR` while `CPACR_EL1.FPEN` traps EL1's accesses
to floating point in either copy, since the access's check reads `CPACR_EL1`, whose write may take
effect for it only after an `ISB`. -/
def Boot.msrTraps (b : Boot) : SysReg → Bool
  | .fpcr => !(b.eff.fpAccess && b.written.fpAccess)
  | _ => false

/-- The step of a system instruction from `b`, or `none` where the model stops: `HVC`, `MSR` of a
register that it cannot write or whose write traps, and `MRS` of a register other than
`CurrentEL`, which reads 4 for EL1, and `ID_AA64MMFR3_EL1`. -/
def sysExec (h : Hw) (i : Instr) (b : Boot) : Option Boot :=
  let core := { b.core with pc := b.core.pc + 4 }
  match i with
  | .spsel1 => some { b with core := core, spSel := true }
  | .isb => some { b with core := core, eff := b.written }
  | .dsbIsh | .dsbSy =>
      some { b with
        core := core
        tlb := if b.tlb = .pending then .clean else b.tlb
        uartDone := true }
  | .tlbiVmalle1 =>
      some { b with core := core, tlb := if b.written = b.eff then .pending else .unknown }
  | .msr k t =>
      match SysReg.ofCode k.val with
      | some r =>
          if b.msrTraps r then none
          else match b.written.set h r (b.core.x t) with
            | some w => some { b with
                core := core
                written := w
                tlb := if keepsTlb r b.written w then b.tlb else .unknown }
            | none => none
      | none => none
  | .mrs t k =>
      match SysReg.ofCode k.val with
      | some .currentEL => some { b with core := core.setX t 4 }
      | some .mmfr3 => some { b with core := core.setX t h.mmfr3 }
      | _ => none
  | _ => none

/-- One step of the machine from `b` with the code map `code`, the processor `h`, and the protected
bytes `R`. -/
inductive BootStep (h : Hw) (R : UInt64 → Bool) (code : UInt64 → Option UInt32) :
    Boot → Boot → Prop
  /-- A system instruction. -/
  | sys {b b' : Boot} {w : UInt32} {i : Instr} (hc : code b.core.pc = some w)
      (hd : decode w = some i) (hsp : b.spSel = true ∨ i = .spsel1)
      (hf : fetchOk h b.eff b.tlb b.core.mem b.core.pc)
      (hw : fetchOk h b.written b.tlb b.core.mem b.core.pc)
      (he : sysExec h i b = some b') : BootStep h R code b b'
  /-- An instruction that touches no memory, with the MMU on or off.  The next program counter
  lies below 2^55, or address tagging is off in both copies of `TCR_EL1`, since a branch under
  `TCR_EL1.TBI0` or `TBI1` replaces the top byte of a target at or above 2^55.  A floating-point
  instruction requires `CPACR_EL1` and `FPCR` at their covered values in both copies. -/
  | plain {b : Boot} {w : UInt32} {i : Instr} {c : State} (hc : code b.core.pc = some w)
      (hd : decode w = some i) (hsp : b.spSel = true)
      (hf : fetchOk h b.eff b.tlb b.core.mem b.core.pc)
      (hw : fetchOk h b.written b.tlb b.core.mem b.core.pc)
      (hn : i.isSys = false) (hm : i.accessesMemory = false)
      (hfp : i.isFP = false ∨ (b.eff.fpOn = true ∧ b.written.fpOn = true))
      (he : exec noMemory i b.core = some c)
      (ht : c.pc.toNat < 2 ^ 55 ∨ (b.eff.untagged = true ∧ b.written.untagged = true)) :
      BootStep h R code b { b with core := c }
  /-- An instruction other than a system instruction, with translation on in the covered
  configuration, synchronized, with valid TLBs, and the UART mapped. -/
  | prog {b : Boot} {w : UInt32} {i : Instr} {c : State} (hc : code b.core.pc = some w)
      (hd : decode w = some i) (hsp : b.spSel = true) (hsync : b.written = b.eff)
      (hcov : b.eff.covered h = true) (htlb : b.tlb = .clean)
      (hf : fetchOk h b.eff b.tlb b.core.mem b.core.pc)
      (hu : classify h b.eff b.core.mem uartAddr = some (.device true))
      (he : exec (b.platform h R) i b.core = some c) :
      BootStep h R code b { b with core := c, uartDone := b.uartDone && c.out == b.core.out }

/-- The states that steps of `BootStep` reach from `b`. -/
inductive BootReach (h : Hw) (R : UInt64 → Bool) (code : UInt64 → Option UInt32) :
    Boot → Boot → Prop
  | refl (b : Boot) : BootReach h R code b b
  | next {b c d : Boot} : BootStep h R code b c → BootReach h R code c d →
      BootReach h R code b d

end LeanExe.A64
