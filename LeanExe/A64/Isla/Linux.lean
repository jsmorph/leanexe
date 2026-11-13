import LeanExe.A64.Isla.Profile

/-!
The profile of the traces of a Linux process at EL0, those of `tests/isla/linux-traces.sh`, which
run with the stack pointer `.el0` of the semantics.  The script's two kernels share the profile
`linux`: `vhe`, the host's kernel at EL2 with FEAT_VHE, under which the registers of EL2 govern
EL0, and `el1`, a kernel at EL1 under KVM on a host with VHE.  The registers of the kernel's or
the firmware's configuration that a trace reads are unknown, fields of `LinuxUnknown`, but for
the fixed values below.  `LinuxUnknown.Holds` states the values that Linux 7.0 or the boot
protocol gives the bits that the script's reset constraints fix, and of `HCR_EL2.RW`.  A theorem
over these traces takes `linux u` as its profile and holds for every `u` with `u.Holds ℓ`, so it
covers every value of the other bits, among them the bits that the traces test and no constraint
fixes.

The fixed values are those of the profile `kvm` of `Profile.lean` for the features, which are the
KVM guest's on the host's cores and lack the host's FEAT_SPE, `SEE`, `DBGEN`,
`__supported_pa_size`, the debug registers `OSLSR_EL1`, `OSDLR_EL1`, `DBGPRCR_EL1`, `MDCCSR_EL0`,
and `_EDSCR`, `VTCR_EL2`, and Isla's defaults, and `FPCR` at `0x02000000`, which the executable's
runtime writes before its program runs.  The IR's initializer sets `__GIC_Pending` to `None`, no
interrupt pending, and Isla's configuration sets `__ThisInstrEnc` to `__A64`.  `PSTATE` has `EL`
and `SP` at 0, the state of a process, `nRW` at 0, AArch64, and its other fields unknown.
-/

namespace LeanExe.A64.Isla

/-- The kernel of a Linux process's traces: `vhe`, the host's kernel at EL2 with FEAT_VHE, and
`el1`, a kernel at EL1 under KVM on a host with VHE. -/
inductive LinuxKernel where
  | vhe
  | el1
  deriving DecidableEq

/-- The values that the traces of a Linux process leave unknown: the last element of
`FeatureImpl`; `HCR_EL2`, `SCR_EL3`, `MDCR_EL2`, `MDSCR_EL1`, and `HFGITR_EL2`; `SCTLR_ELx`,
`TCR_ELx`, `VBAR_ELx`, and `SPSR_ELx` of EL1 and EL2, and `HPFAR_EL2`; `CPACR_EL1`, `CPTR_EL2`,
`CPTR_EL3`, and `ZCR_ELx` and `SMCR_ELx` of EL1 to EL3; the fields `A`, `D`, `F`, `I`, `IL`,
`SS`, `BTYPE`, `DIT`, `SSBS`, `UAO`, and `PAN` of `PSTATE`; and the bits of Z0 to Z31 above bit
63. -/
structure LinuxUnknown where
  feature : Bool
  hcr : BitVec 64
  scr : BitVec 64
  mdcr : BitVec 64
  mdscr : BitVec 64
  hfgitr : BitVec 64
  sctlr1 : BitVec 64
  sctlr2 : BitVec 64
  tcr1 : BitVec 64
  tcr2 : BitVec 64
  vbar1 : BitVec 64
  vbar2 : BitVec 64
  spsr1 : BitVec 64
  spsr2 : BitVec 64
  hpfar2 : BitVec 64
  cpacr : BitVec 64
  cptr2 : BitVec 64
  cptr3 : BitVec 64
  zcr1 : BitVec 64
  zcr2 : BitVec 64
  zcr3 : BitVec 64
  smcr1 : BitVec 64
  smcr2 : BitVec 64
  smcr3 : BitVec 64
  a : BitVec 1
  d : BitVec 1
  f : BitVec 1
  i : BitVec 1
  il : BitVec 1
  ss : BitVec 1
  btype : BitVec 2
  dit : BitVec 1
  ssbs : BitVec 1
  uao : BitVec 1
  pan : BitVec 1
  z : Fin 32 → BitVec 1984

/-- The registers outside the model of the traces of a Linux process at EL0, for the unknown
values `u`. -/
def linux (u : LinuxUnknown) : Sys
  | "SEE" => some (.bits 128 (2 ^ 128 - 1))
  | "DBGEN" => some (.enum "Signal_Low")
  | "FeatureImpl" => some (.vec (kvm.features.impl.map .bool ++ [.bool u.feature]))
  | "__isla_vector_gpr" => some (.bool true)
  | "__supported_pa_size" => some (.bits 128 40)
  | "__GIC_Pending" => some (.enum "None")
  | "__ThisInstrEnc" => some (.enum "__A64")
  | "__max_implemented_smeveclen" => some (.bits 128 512)
  | "PSTATE" => some (.struct [("EL", .bits 2 0), ("SP", .bits 1 0), ("nRW", .bits 1 0),
      ("A", bv u.a), ("D", bv u.d), ("F", bv u.f), ("I", bv u.i), ("IL", bv u.il),
      ("SS", bv u.ss), ("BTYPE", bv u.btype), ("DIT", bv u.dit), ("SSBS", bv u.ssbs),
      ("UAO", bv u.uao), ("PAN", bv u.pan)])
  | "HCR_EL2" => some (sysreg 64 u.hcr.toNat)
  | "SCR_EL3" => some (sysreg 64 u.scr.toNat)
  | "MDCR_EL2" => some (sysreg 64 u.mdcr.toNat)
  | "MDSCR_EL1" => some (sysreg 64 u.mdscr.toNat)
  | "HFGITR_EL2" => some (sysreg 64 u.hfgitr.toNat)
  | "OSLSR_EL1" => some (sysreg 64 0x8)
  | "OSDLR_EL1" => some (sysreg 64 0)
  | "DBGPRCR_EL1" => some (sysreg 64 0)
  | "MDCCSR_EL0" => some (sysreg 64 0)
  | "_EDSCR" => some (sysreg 32 0x02000002)
  | "VTCR_EL2" => some (sysreg 64 0)
  | "SCTLR_EL1" => some (sysreg 64 u.sctlr1.toNat)
  | "SCTLR_EL2" => some (sysreg 64 u.sctlr2.toNat)
  | "TCR_EL1" => some (sysreg 64 u.tcr1.toNat)
  | "TCR_EL2" => some (sysreg 64 u.tcr2.toNat)
  | "VBAR_EL1" => some (.bits 64 u.vbar1.toNat)
  | "VBAR_EL2" => some (.bits 64 u.vbar2.toNat)
  | "SPSR_EL1" => some (sysreg 64 u.spsr1.toNat)
  | "SPSR_EL2" => some (sysreg 64 u.spsr2.toNat)
  | "HPFAR_EL2" => some (sysreg 64 u.hpfar2.toNat)
  | "CPACR_EL1" => some (sysreg 64 u.cpacr.toNat)
  | "CPTR_EL2" => some (sysreg 64 u.cptr2.toNat)
  | "CPTR_EL3" => some (sysreg 64 u.cptr3.toNat)
  | "ZCR_EL1" => some (sysreg 64 u.zcr1.toNat)
  | "ZCR_EL2" => some (sysreg 64 u.zcr2.toNat)
  | "ZCR_EL3" => some (sysreg 64 u.zcr3.toNat)
  | "SMCR_EL1" => some (sysreg 64 u.smcr1.toNat)
  | "SMCR_EL2" => some (sysreg 64 u.smcr2.toNat)
  | "SMCR_EL3" => some (sysreg 64 u.smcr3.toNat)
  | "FPCR" => some (sysreg 64 0x02000000)
  | "_Z" => some (zHigh u.z)
  | r => (kvm.features.settings.lookup r).map .bool

theorem linux_get (u : LinuxUnknown) (r : String) (al : List String) :
    (linux u).get r al = (linux u r).bind (acc al) := rfl

/-- The bits of the registers outside the model that the reset constraints of
`tests/isla/linux-traces.sh` fix, and `HCR_EL2.RW`, at the values that Linux 7.0 and its firmware
give them under the kernel `ℓ`: `HCR_EL2.E2H` 1, `TGE` 1 under `vhe` and 0 under `el1`, and `RW`
1; `SCR_EL3.NS` and `RW` 1; `MDCR_EL2.TDE`, `MDSCR_EL1.SS`, and `HFGITR_EL2.SVC_EL0` 0; and under
`vhe`, for the floating-point forms, `FPEN` at 0b11 and `ZEN` at 0b01 of `CPTR_EL2`, `CPTR_EL3.TFP`
0, and the vector length `ZCR_EL2.LEN` 0.  `SMCR_EL3.LEN` 0 is a choice of the model: the host's
cores lack FEAT_SME and with it `SMCR_EL3`, while the Sail model computes the streaming vector
length from it in each write of a D register, and the floating-point traces fix it so that the
length is 128 bits. -/
structure LinuxUnknown.Holds (ℓ : LinuxKernel) (u : LinuxUnknown) : Prop where
  e2h : u.hcr.toNat / 2 ^ 34 % 2 = 1
  tge : u.hcr.toNat / 2 ^ 27 % 2 = if ℓ = .vhe then 1 else 0
  hcrRw : u.hcr.toNat / 2 ^ 31 % 2 = 1
  ns : u.scr.toNat % 2 = 1
  rw : u.scr.toNat / 2 ^ 10 % 2 = 1
  tde : u.mdcr.toNat / 2 ^ 8 % 2 = 0
  ss : u.mdscr.toNat % 2 = 0
  svc : u.hfgitr.toNat / 2 ^ 52 % 2 = 0
  fpen : ℓ = .vhe → u.cptr2.toNat / 2 ^ 20 % 4 = 3
  zen : ℓ = .vhe → u.cptr2.toNat / 2 ^ 16 % 4 = 1
  tfp : u.cptr3.toNat / 2 ^ 10 % 2 = 0
  len : ℓ = .vhe → u.zcr2.toNat % 16 = 0
  smlen : ℓ = .vhe → u.smcr3.toNat % 16 = 0

/-- The bits of `HCR_EL2` and `SCR_EL3` that the reset constraints of every trace of a Linux
process fix under the host's kernel, in the form in which a walk evaluates them. -/
theorem holds_vhe {u : LinuxUnknown} (hu : u.Holds .vhe) :
    u.hcr.toNat / 17179869184 % 2 = 1 ∧ u.hcr.toNat / 134217728 % 2 = 1 ∧
      u.scr.toNat % 2 = 1 ∧ u.scr.toNat / 1024 % 2 = 1 :=
  ⟨hu.e2h, by simpa using hu.tge, hu.ns, hu.rw⟩

/-- The bits of `HCR_EL2` and `SCR_EL3` that the reset constraints of every trace of a Linux
process fix under a kernel at EL1, in the form in which a walk evaluates them. -/
theorem holds_el1 {u : LinuxUnknown} (hu : u.Holds .el1) :
    u.hcr.toNat / 17179869184 % 2 = 1 ∧ u.hcr.toNat / 134217728 % 2 = 0 ∧
      u.scr.toNat % 2 = 1 ∧ u.scr.toNat / 1024 % 2 = 1 :=
  ⟨hu.e2h, by simpa using hu.tge, hu.ns, hu.rw⟩

/-- The floating-point enables and vector lengths that the reset constraints of the traces of the
floating-point forms fix under the host's kernel, in the form in which a walk evaluates them. -/
theorem holds_vhe_fp {u : LinuxUnknown} (hu : u.Holds .vhe) :
    u.cptr2.toNat / 1048576 % 4 = 3 ∧ u.cptr2.toNat / 65536 % 4 = 1 ∧
      u.cptr3.toNat / 1024 % 2 = 0 ∧ u.zcr2.toNat % 16 = 0 ∧ u.smcr3.toNat % 16 = 0 :=
  ⟨hu.fpen rfl, hu.zen rfl, hu.tfp, hu.len rfl, hu.smlen rfl⟩

/-- The smaller of 0 and `x` as a walk evaluates it: the vector length of EL0 under the host's
kernel takes the smaller of the LEN fields of `ZCR_EL2`, 0, and `ZCR_EL3`. -/
theorem len_min (x : Nat) : (bif decide ((0 : Int) < (x : Int)) then 0 else x) = 0 := by
  simp

end LeanExe.A64.Isla
