import LeanExe.A64.Isla.Profile

/-!
The profile of the traces of `tests/isla/m7-traces.sh`: the registers outside the model that some
committed trace reads, with the values that the configuration gives them, and the values that it
leaves UNKNOWN as the fields of `Unknown`.  A theorem of `Agrees` takes `sys u` as its profile and
holds for every `u`.

The sources are those of the A64 profiles (`LeanExe/A64/Isla/Profile.lean`): the model's register
initializers and Isla's `configs/armv9p4.toml`, the settings that `m7-traces.sh` passes with `-I`,
which include the feature settings of `tests/isla/tcg/features`, the reset values that it passes
with `-R`, and the harness function `isla_footprint_t32` or `isla_footprint_t16`, which runs
`InitFeatureImpl` and sets `SEE` to -1 and `DBGEN` to `Signal_Low` before the trace starts.
The harness writes `__currentCond` inside the trace, so its initial value is UNKNOWN.  Only the
loads and stores read `SCTLR_EL1`, `MAIR_EL1`, `TCR_EL1`, and `TTBR0_NS`, and they set them, so
one profile serves every form.
-/

namespace LeanExe.M7.Isla

open LeanExe.A64.Isla (Val Sys acc sysreg bv tcg)

/-- The values that the configuration leaves UNKNOWN and some committed trace reads: the last
element of `FeatureImpl`, the initial `__currentCond`, the field `D` of `PSTATE`, the AArch32
register `_HCR`, `SCTLR_EL2`, and the model's 128-bit register `_TTBR0_EL1`. -/
structure Unknown where
  feature : Bool
  cond : BitVec 4
  d : BitVec 1
  hcr32 : BitVec 32
  sctlr2 : BitVec 64
  ttbr0el1 : BitVec 128

/-- The registers outside the model of the traces of `m7-traces.sh`.  `-R` sets the fields `nRW`,
`T`, `EL`, `M`, `IT`, and `E` of `PSTATE` for AArch32 User mode in Thumb state outside an IT block
with little-endian data, `HCR_EL2` to `0x80000000`, `SCR_EL3` to `0x401`, `VTCR_EL2` and
`MDCCSR_EL0` to 0, `OSLSR_EL1` to `0xa`, `OSDLR_EL1` to 0, and `_EDSCR` to `0x02000002`, and for the
loads and stores `SCTLR_EL1` to `0x30d0198d`, `MAIR_EL1` to `0xff00`, `TCR_EL1` to `0x180a03520`,
and `TTBR0_NS` to `0x100000000`.  `-I` sets `__isla_vector_gpr`, `__supported_pa_size`, and each
register that the `features` file names, and the defaults of `armv9p4.toml` set
`SPESampleInFlight`, `__tlb_enabled`, and the three `__monomorphize` flags to false. -/
def sys (u : Unknown) : Sys
  | "SEE" => some (.bits 128 (2 ^ 128 - 1))
  | "DBGEN" => some (.enum "Signal_Low")
  | "FeatureImpl" => some (.vec (tcg.features.impl.map .bool ++ [.bool u.feature]))
  | "__isla_vector_gpr" => some (.bool true)
  | "__supported_pa_size" => some (.bits 128 44)
  | "__currentCond" => some (bv u.cond)
  | "PSTATE" => some (.struct [("nRW", .bits 1 1), ("T", .bits 1 1), ("EL", .bits 2 0),
      ("M", .bits 5 16), ("IT", .bits 8 0), ("E", .bits 1 0), ("D", bv u.d)])
  | "HCR_EL2" => some (sysreg 64 0x80000000)
  | "_HCR" => some (sysreg 32 u.hcr32.toNat)
  | "SCR_EL3" => some (sysreg 64 0x401)
  | "VTCR_EL2" => some (sysreg 64 0)
  | "MDCCSR_EL0" => some (sysreg 64 0)
  | "OSLSR_EL1" => some (sysreg 64 0xa)
  | "OSDLR_EL1" => some (sysreg 64 0)
  | "_EDSCR" => some (sysreg 32 0x02000002)
  | "SCTLR_EL1" => some (sysreg 64 0x30d0198d)
  | "MAIR_EL1" => some (sysreg 64 0xff00)
  | "TCR_EL1" => some (sysreg 64 0x180a03520)
  | "TTBR0_NS" => some (sysreg 64 0x100000000)
  | "SCTLR_EL2" => some (sysreg 64 u.sctlr2.toNat)
  | "_TTBR0_EL1" => some (sysreg 128 u.ttbr0el1.toNat)
  | "SPESampleInFlight" => some (.bool false)
  | "__tlb_enabled" => some (.bool false)
  | "__monomorphize_reads" => some (.bool false)
  | "__monomorphize_writes" => some (.bool false)
  | "__monomorphize_descriptors" => some (.bool false)
  | r => (tcg.features.settings.lookup r).map .bool

theorem sys_get (u : Unknown) (r : String) (al : List String) :
    (sys u).get r al = (sys u r).bind (acc al) := rfl

end LeanExe.M7.Isla
