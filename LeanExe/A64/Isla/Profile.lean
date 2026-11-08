import LeanExe.A64.Isla.Trace

/-!
The processor profiles of the traces of `tests/isla/traces.sh`, `tcg` and `kvm`, as the registers
outside the model that each configuration fixes, with the values that it leaves UNKNOWN as the
fields of `Unknown`.  A theorem of `Agrees` takes `p.sys g u` as its profile and holds for every
`u`.

A trace's configuration comes from four sources.  The model's register initializers and Isla's
`configs/armv9p4.toml`, with its defaults and its reset registers, give the base.  `traces.sh` sets
registers before the entry point with `-I`, from the profile's `features` file and for
`__isla_vector_gpr` and `__supported_pa_size`, and replaces reset values with `-R`.  The entry
point `isla_footprint_no_init` runs `InitFeatureImpl`, which sets element `num_of_Feature(F)` of
`FeatureImpl` to the register `F_IMPLEMENTED` for each member `F` of the enumeration `Feature`,
sets `SEE` to -1 and `DBGEN` to `Signal_Low`, and runs the reset (`armv9p4.ir` 10266 and
3771797-3771845).  The profile holds each register that some committed trace reads, with the value
of the last source that sets it, and the registers that the `features` file sets.

`isla_features% "PATH"` reads a `features` file, relative to the directory in which Lean runs,
when the term elaborates, so a profile holds the settings that the traces used.  Lake does not
rebuild this module when a file changes, and `tests/TestSupport/A64/Isla/Profiles.lean`, which
`tests/isla/theorems.sh` elaborates on every run, checks the profiles against the files.  The
reader `parseFeatures` is trusted as `parse` is.  A file lists the features in the order of
`Feature`, so the values of its lines whose names begin with `FEAT_` are the first 258 elements of
`FeatureImpl`.  Element 258 names no feature and keeps the register's undefined value,
`Unknown.feature`.  A theorem whose trace reads `FeatureImpl` compares the whole vector with the
one Isla read.

A system register is a struct whose one field `bits` holds its value, and an integer of the model
is a bit vector of width 128, as Isla prints them.  The memory forms' reset constraints and the
descriptors that `--fixed-memory` places concern the opcode's fields, `TTBR0_NS`, and memory, so
their theorems carry them as premises.
-/

namespace LeanExe.A64.Isla

/-- The settings of a profile's `features` file: `settings` holds the pair `(NAME, b)` of each line
`NAME=b` in order, which `traces.sh` passes as `-I NAME=b`, and `impl` the values `b` of the lines
whose names begin with `FEAT_`, in order. -/
structure Features where
  settings : List (String × Bool)
  impl : List Bool
  deriving Lean.ToExpr

/-- The settings of the text `s` of a `features` file, whose nonempty lines are `NAME=true` or
`NAME=false`. -/
def parseFeatures (s : String) : Except String Features := do
  let settings ← ((s.splitOn "\n").filter (· ≠ "")).mapM fun l =>
    match l.splitOn "=" with
    | [n, "true"] => .ok (n, true)
    | [n, "false"] => .ok (n, false)
    | _ => .error s!"bad setting {l}"
  return ⟨settings,
    settings.filterMap fun (n, b) => if n.startsWith "FEAT_" then some b else none⟩

open Lean Elab Term in
/-- The features in the file at the path, read when the term elaborates. -/
elab "isla_features% " path:str : term => do
  let s ← IO.FS.readFile path.getString
  match parseFeatures s with
  | .ok f => return toExpr f
  | .error e => throwError "{path.getString}: {e}"

/-- What a processor profile of `traces.sh` sets: the features, `__supported_pa_size`, and the
values of `HCR_EL2`, `OSLSR_EL1`, and, for the floating-point forms, `CPTR_EL2`, `CPTR_EL3`, and
`SMCR_EL3`. -/
structure Profile where
  features : Features
  paSize : Nat
  hcr : Nat
  oslsr : Nat
  cptr2 : Nat
  cptr3 : Nat
  smcr3 : Nat

/-- The profile `tcg` of `traces.sh`, QEMU 8.2.2's Cortex-A57 under TCG. -/
def tcg : Profile where
  features := isla_features% "tests/isla/tcg/features"
  paSize := 44
  hcr := 0x80000000
  oslsr := 0xa
  cptr2 := 0
  cptr3 := 0
  smcr3 := 0

/-- The profile `kvm` of `traces.sh`, the guest of KVM in Linux 7.0 on the Cortex-X925 and
Cortex-A725 cores of edgexpert-18ff. -/
def kvm : Profile where
  features := isla_features% "tests/isla/kvm/features"
  paSize := 40
  hcr := 0x480000000
  oslsr := 0x8
  cptr2 := 0x50330000
  cptr3 := 0x100
  smcr3 := 0

/-- The profile `sme` of `traces.sh`: `kvm` on a processor that also implements FEAT_SME and
FEAT_SME_FA64, with the settings that Linux's boot protocol requires of it, for the floating-point
forms. -/
def sme : Profile where
  features := isla_features% "tests/isla/sme/features"
  paSize := 40
  hcr := 0x480000000
  oslsr := 0x8
  cptr2 := 0x53330000
  cptr3 := 0x1100
  smcr3 := 0x80000000

/-- The arguments of `traces.sh` that differ among the forms: `tcr` for the arithmetic, logical,
move, and address forms, which fix `TCR_EL1`, `branch` for the branches, which leave it undefined,
`memory` for the loads and stores, which fix `TCR_EL1`, leave `VBAR_EL1` undefined, and set
`ZCR_EL3` and `SMCR_EL3` to 0, the values of `armv9p4.toml`, and `fp` for the floating-point
forms, which fix `TCR_EL1`, `CPACR_EL1`, `CPTR_EL2`, `CPTR_EL3`, and `FPCR`. -/
inductive Group where
  | tcr
  | branch
  | memory
  | fp
  deriving DecidableEq

/-- The values that the configuration leaves UNKNOWN and some committed trace reads: the last
element of `FeatureImpl`; `TCR_EL1` of the branches and `VBAR_EL1` of the loads and stores;
`TTBR0_NS`, which holds `TTBR0_EL1`, and the model's 128-bit register `_TTBR0_EL1`; `SCTLR_EL2`,
`SPSR_EL1`, `ZCR_EL1`, `ZCR_EL2`, `SMCR_EL1`, and `SMCR_EL2`; the fields `A`, `F`, `I`, `IL`,
`SS`, `BTYPE`, `DIT`, `SSBS`, `UAO`, and `SM` of `PSTATE`, the last of which only the traces of
the profile `sme` read; and the bits of Z0 to Z31 above bit 63, the upper 1984 bits of each
element of `_Z`, whose low 64 bits the model holds. -/
structure Unknown where
  feature : Bool
  tcr : BitVec 64
  vbar : BitVec 64
  ttbr0 : BitVec 64
  ttbr0el1 : BitVec 128
  sctlr2 : BitVec 64
  spsr : BitVec 64
  zcr1 : BitVec 64
  zcr2 : BitVec 64
  smcr1 : BitVec 64
  smcr2 : BitVec 64
  a : BitVec 1
  f : BitVec 1
  i : BitVec 1
  il : BitVec 1
  ss : BitVec 1
  btype : BitVec 2
  dit : BitVec 1
  ssbs : BitVec 1
  uao : BitVec 1
  sm : BitVec 1
  z : Fin 32 → BitVec 1984

/-- A system register whose one field `bits` holds `n`. -/
def sysreg (w n : Nat) : Val := .struct [("bits", .bits w n)]

/-- The bit vector `x` as a value. -/
def bv {w : Nat} (x : BitVec w) : Val := .bits w x.toNat

/-- The upper bits of Z0 to Z31 as the vector that `σ` holds for `_Z`. -/
def zHigh (z : Fin 32 → BitVec 1984) : Val :=
  .vec [bv (z 0), bv (z 1), bv (z 2), bv (z 3), bv (z 4), bv (z 5), bv (z 6), bv (z 7), bv (z 8),
    bv (z 9), bv (z 10), bv (z 11), bv (z 12), bv (z 13), bv (z 14), bv (z 15), bv (z 16),
    bv (z 17), bv (z 18), bv (z 19), bv (z 20), bv (z 21), bv (z 22), bv (z 23), bv (z 24),
    bv (z 25), bv (z 26), bv (z 27), bv (z 28), bv (z 29), bv (z 30), bv (z 31)]

/-- The registers outside the model under the profile `p` for the forms of the group `g`.  The
entry point sets `SEE` and `DBGEN` and builds `FeatureImpl` from the `features` file.  `-I` sets
`__isla_vector_gpr`, `__supported_pa_size`, and each register that the `features` file names.
`-R` sets the fields `EL`, `SP`, `D`, and `PAN` of `PSTATE`, `SCTLR_EL1` to `0x30d0198d`,
`MAIR_EL1` to `0xff00`, `HCR_EL2`, `SCR_EL3` to `0x401`, `OSLSR_EL1`, `_EDSCR` to `0x02000002`,
with PipeAdv set as `__InstructionExecute` sets it before the decode, `MDCR_EL2`, `VTCR_EL2`,
`MDSCR_EL1`, `OSDLR_EL1`, `DBGPRCR_EL1`, and `MDCCSR_EL0` to 0, and the group's `TCR_EL1` and
`VBAR_EL1`, and for the floating-point forms `CPACR_EL1` to `0x300000` and `FPCR` to `0x02000000`,
the startup's values, and the profile's `CPTR_EL2` and `CPTR_EL3`, and under `sme` `SMCR_EL3`.  The
reset of `armv9p4.toml` sets `PSTATE.nRW` to 0.  The defaults of `armv9p4.toml` and the model's
initializers set `SPESampleInFlight`, `__tlb_enabled`, and the three `__monomorphize` flags to
false, `ZCR_EL3` and `SMCR_EL3` to 0, `VBAR_EL1` to 0 outside the loads and stores,
`__max_implemented_smeveclen` to 512, and `__block_bbm_implemented` to 2. -/
def Profile.sys (p : Profile) (g : Group) (u : Unknown) : Sys
  | "SEE" => some (.bits 128 (2 ^ 128 - 1))
  | "DBGEN" => some (.enum "Signal_Low")
  | "FeatureImpl" => some (.vec (p.features.impl.map .bool ++ [.bool u.feature]))
  | "__isla_vector_gpr" => some (.bool true)
  | "__supported_pa_size" => some (.bits 128 p.paSize)
  | "PSTATE" => some (.struct [("EL", .bits 2 1), ("SP", .bits 1 1), ("D", .bits 1 1),
      ("PAN", .bits 1 0), ("nRW", .bits 1 0), ("A", bv u.a), ("F", bv u.f), ("I", bv u.i),
      ("IL", bv u.il), ("SS", bv u.ss), ("BTYPE", bv u.btype), ("DIT", bv u.dit),
      ("SSBS", bv u.ssbs), ("UAO", bv u.uao), ("SM", bv u.sm)])
  | "SCTLR_EL1" => some (sysreg 64 0x30d0198d)
  | "MAIR_EL1" => some (sysreg 64 0xff00)
  | "HCR_EL2" => some (sysreg 64 p.hcr)
  | "SCR_EL3" => some (sysreg 64 0x401)
  | "MDCR_EL2" => some (sysreg 64 0)
  | "VTCR_EL2" => some (sysreg 64 0)
  | "MDSCR_EL1" => some (sysreg 64 0)
  | "OSLSR_EL1" => some (sysreg 64 p.oslsr)
  | "OSDLR_EL1" => some (sysreg 64 0)
  | "DBGPRCR_EL1" => some (sysreg 64 0)
  | "MDCCSR_EL0" => some (sysreg 64 0)
  | "_EDSCR" => some (sysreg 32 0x02000002)
  | "TCR_EL1" => some (sysreg 64 (if g = .branch then u.tcr.toNat else 0x80a03520))
  | "VBAR_EL1" => some (.bits 64 (if g = .memory then u.vbar.toNat else 0))
  | "ZCR_EL3" => some (sysreg 64 0)
  | "SMCR_EL3" => some (sysreg 64 (if g = .fp then p.smcr3 else 0))
  | "SPESampleInFlight" => some (.bool false)
  | "__tlb_enabled" => some (.bool false)
  | "__monomorphize_reads" => some (.bool false)
  | "__monomorphize_writes" => some (.bool false)
  | "__monomorphize_descriptors" => some (.bool false)
  | "__max_implemented_smeveclen" => some (.bits 128 512)
  | "__block_bbm_implemented" => some (.bits 128 2)
  | "TTBR0_NS" => some (sysreg 64 u.ttbr0.toNat)
  | "_TTBR0_EL1" => some (sysreg 128 u.ttbr0el1.toNat)
  | "SCTLR_EL2" => some (sysreg 64 u.sctlr2.toNat)
  | "SPSR_EL1" => some (sysreg 64 u.spsr.toNat)
  | "ZCR_EL1" => some (sysreg 64 u.zcr1.toNat)
  | "ZCR_EL2" => some (sysreg 64 u.zcr2.toNat)
  | "SMCR_EL1" => some (sysreg 64 u.smcr1.toNat)
  | "SMCR_EL2" => some (sysreg 64 u.smcr2.toNat)
  | "CPACR_EL1" => if g = .fp then some (sysreg 64 0x300000) else none
  | "CPTR_EL2" => if g = .fp then some (sysreg 64 p.cptr2) else none
  | "CPTR_EL3" => if g = .fp then some (sysreg 64 p.cptr3) else none
  | "FPCR" => if g = .fp then some (sysreg 64 0x02000000) else none
  | "_Z" => some (zHigh u.z)
  | r => (p.features.settings.lookup r).map .bool

theorem Profile.sys_get (p : Profile) (g : Group) (u : Unknown) (r : String) (al : List String) :
    (p.sys g u).get r al = (p.sys g u r).bind (acc al) := rfl

end LeanExe.A64.Isla
