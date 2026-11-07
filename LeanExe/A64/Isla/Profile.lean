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
values of `HCR_EL2` and `OSLSR_EL1`. -/
structure Profile where
  features : Features
  paSize : Nat
  hcr : Nat
  oslsr : Nat

/-- The profile `tcg` of `traces.sh`, QEMU 8.2.2's Cortex-A57 under TCG. -/
def tcg : Profile where
  features := isla_features% "tests/isla/tcg/features"
  paSize := 44
  hcr := 0x80000000
  oslsr := 0xa

/-- The profile `kvm` of `traces.sh`, the guest of KVM in Linux 7.0 on the Cortex-X925 and
Cortex-A725 cores of edgexpert-18ff. -/
def kvm : Profile where
  features := isla_features% "tests/isla/kvm/features"
  paSize := 40
  hcr := 0x480000000
  oslsr := 0x8

/-- The arguments of `traces.sh` that differ among the forms: `tcr` for the arithmetic, logical,
move, and address forms, which fix `TCR_EL1`, `branch` for the branches, which leave it undefined,
and `memory` for the loads and stores, which fix `TCR_EL1`, leave `VBAR_EL1` undefined, and set
`ZCR_EL3` and `SMCR_EL3` to 0, the values of `armv9p4.toml`. -/
inductive Group where
  | tcr
  | branch
  | memory
  deriving DecidableEq

/-- The values that the configuration leaves UNKNOWN and some committed trace reads: the last
element of `FeatureImpl`; `TCR_EL1` of the branches and `VBAR_EL1` of the loads and stores;
`TTBR0_NS`, which holds `TTBR0_EL1`, and the model's 128-bit register `_TTBR0_EL1`; `SCTLR_EL2`,
`SPSR_EL1`, `ZCR_EL1`, `ZCR_EL2`, `SMCR_EL1`, and `SMCR_EL2`; and the fields `A`, `F`, `I`, `IL`,
`SS`, `BTYPE`, `DIT`, `SSBS`, and `UAO` of `PSTATE`. -/
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

/-- A system register whose one field `bits` holds `n`. -/
def sysreg (w n : Nat) : Val := .struct [("bits", .bits w n)]

/-- The bit vector `x` as a value. -/
def bv {w : Nat} (x : BitVec w) : Val := .bits w x.toNat

/-- The registers outside the model under the profile `p` for the forms of the group `g`.  The
entry point sets `SEE` and `DBGEN` and builds `FeatureImpl` from the `features` file.  `-I` sets
`__isla_vector_gpr`, `__supported_pa_size`, and each register that the `features` file names.
`-R` sets the fields `EL`, `SP`, `D`, and `PAN` of `PSTATE`, `SCTLR_EL1` to `0x30d0198d`,
`MAIR_EL1` to `0xff00`, `HCR_EL2`, `SCR_EL3` to `0x401`, `OSLSR_EL1`, `_EDSCR` to `0x02000002`,
with PipeAdv set as `__InstructionExecute` sets it before the decode, `MDCR_EL2`, `VTCR_EL2`,
`MDSCR_EL1`, `OSDLR_EL1`, `DBGPRCR_EL1`, and `MDCCSR_EL0` to 0, and the group's `TCR_EL1` and
`VBAR_EL1`.  The reset of `armv9p4.toml` sets `PSTATE.nRW` to 0.  The defaults of
`armv9p4.toml` and the model's initializers set `SPESampleInFlight`, `__tlb_enabled`, and the three
`__monomorphize` flags to false, `ZCR_EL3` and `SMCR_EL3` to 0, `VBAR_EL1` to 0 outside the loads
and stores, `__max_implemented_smeveclen` to 512, and `__block_bbm_implemented` to 2. -/
def Profile.sys (p : Profile) (g : Group) (u : Unknown) : Sys
  | "SEE" => some (.bits 128 (2 ^ 128 - 1))
  | "DBGEN" => some (.enum "Signal_Low")
  | "FeatureImpl" => some (.vec (p.features.impl.map .bool ++ [.bool u.feature]))
  | "__isla_vector_gpr" => some (.bool true)
  | "__supported_pa_size" => some (.bits 128 p.paSize)
  | "PSTATE" => some (.struct [("EL", .bits 2 1), ("SP", .bits 1 1), ("D", .bits 1 1),
      ("PAN", .bits 1 0), ("nRW", .bits 1 0), ("A", bv u.a), ("F", bv u.f), ("I", bv u.i),
      ("IL", bv u.il), ("SS", bv u.ss), ("BTYPE", bv u.btype), ("DIT", bv u.dit),
      ("SSBS", bv u.ssbs), ("UAO", bv u.uao)])
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
  | "SMCR_EL3" => some (sysreg 64 0)
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
  | r => (p.features.settings.lookup r).map .bool

theorem Profile.sys_get (p : Profile) (g : Group) (u : Unknown) (r : String) (al : List String) :
    (p.sys g u).get r al = (p.sys g u r).bind (acc al) := rfl

end LeanExe.A64.Isla
