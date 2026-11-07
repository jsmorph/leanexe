import LeanExe.A64.Isla.Check
import LeanExe.A64.Isla.Profile

/-!
The theorem of `SUBS X3, X4, X5` from the trace of one encoding, `tests/isla/subs.trace`.  Isla
e9b5d945 without the patch produced it, with Z3 4.12.6 and `armv9p4.ir` of isla-snapshots
d8b31014 as built in `~/isla-probe` on edgexpert-18ff, from the entry point
`isla_footprint_no_init` with Isla's `configs/armv9p4.toml` and `-s --simplify-registers --tree`.
The processor runs at EL1 with SP_EL1 and debug exceptions masked (`-R PSTATE.EL=0b01`,
`PSTATE.SP=0b1`, and `PSTATE.D=0b1`), with `_EDSCR` 2, `MDCCSR_EL0`, `OSLSR_EL1`, `OSDLR_EL1`,
and `DBGPRCR_EL1` 0, and `SCTLR_EL1` `0x04000208`: the MMU, the alignment check, and big-endian
data are off, and SA, the stack pointer's alignment check, is on.  The opcode `eb050083` is a
concrete word (`-x -e big -i`), which `subs.opcode` holds in binary, and SUBS runs with
`-L AddWithCarry`.
-/

namespace TestSupport.A64.Isla.Stage1

open LeanExe.A64 LeanExe.A64.Isla

/-- The values that this configuration leaves UNKNOWN and the traces read: six system registers
and the last element of `FeatureImpl`, which names no feature. -/
structure Unknown where
  mair : UInt64
  mair2 : UInt64
  pir : UInt64
  pire0 : UInt64
  sctlr2 : UInt64
  s2pir : UInt64
  feature : Bool

/-- `FeatureImpl` but its last element under this configuration, one character per feature, `1`
for an implemented one, as the model's initializers and `armv9p4.toml` set the features. -/
def features : String :=
  "10001111111111111110111111111111111110111111111111111111111111111111111101110000011111" ++
  "10011111100110111111111110111111111110111111111001111111111111111111111111111101111111" ++
  "11111011111111111111111111111111111111111111011011111110110100111011111111111111111111"

/-- The registers outside the model that the traces read under this configuration: the values
that `armv9p4.toml` and the arguments above set, `PSTATE.nRW` 0 from the reset of `armv9p4.toml`,
`SEE` -1 and `DBGEN` `Signal_Low` from the entry point, and `FeatureImpl`. -/
def config (u : Unknown) : Sys
  | "__isla_vector_gpr" => some (.bool false)
  | "__monomorphize_reads" => some (.bool false)
  | "SPESampleInFlight" => some (.bool false)
  | "__supported_pa_size" => some (.bits 128 52)
  | "SEE" => some (.bits 128 (2 ^ 128 - 1))
  | "PSTATE" =>
    some (.struct [("EL", .bits 2 1), ("SP", .bits 1 1), ("D", .bits 1 1), ("nRW", .bits 1 0)])
  | "SCTLR_EL1" => some (sysreg 64 0x04000208)
  | "TCR_EL1" => some (sysreg 64 0)
  | "MDSCR_EL1" => some (sysreg 64 0)
  | "HCR_EL2" => some (sysreg 64 0x80000000)
  | "MDCR_EL2" => some (sysreg 32 0)
  | "SCR_EL3" => some (sysreg 64 0x401)
  | "VTCR_EL2" => some (sysreg 64 0)
  | "_EDSCR" => some (sysreg 32 2)
  | "MDCCSR_EL0" => some (sysreg 64 0)
  | "OSLSR_EL1" => some (sysreg 64 0)
  | "OSDLR_EL1" => some (sysreg 64 0)
  | "DBGEN" => some (.enum "Signal_Low")
  | "FeatureImpl" =>
    some (.vec (features.toList.map (fun c => .bool (c == '1')) ++ [.bool u.feature]))
  | "MAIR_EL1" => some (sysreg 64 u.mair.toNat)
  | "MAIR2_EL1" => some (sysreg 64 u.mair2.toNat)
  | "PIR_EL1" => some (sysreg 64 u.pir.toNat)
  | "PIRE0_EL1" => some (sysreg 64 u.pire0.toNat)
  | "SCTLR_EL2" => some (sysreg 64 u.sctlr2.toNat)
  | "S2PIR_EL2" => some (sysreg 64 u.s2pir.toNat)
  | _ => none

theorem config_get (u : Unknown) (r : String) (al : List String) :
    (config u).get r al = (config u r).bind (acc al) := rfl

/-- The footprint of `SUBS X3, X4, X5`. -/
def subsFp : Footprint := isla_trace% "tests/isla/subs"

/-- Reduces an equation between two functions that update register 3 of the same registers to
the equation between the values written. -/
macro "regs_end" : tactic => `(tactic| (
  funext j
  by_cases hj : j = 3 <;> simp only [hj, eq_self_iff_true, ↓reduceIte]))

/-- Proves that the state at the end of the trace of `SUBS` from the state `s` is `exec`'s.  The
flags of the trace are the bits of a word of 4 bits, and its V flag compares the sign-extended
result with the sum of the sign-extended operands, which `omega` decides once the signs of the
operands and the result and the carry are known. -/
syntax "subs_end " term : tactic
macro_rules
  | `(tactic| subs_end $s) => `(tactic| (
    done_end
    simp only [Bool.cond_eq_ite, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
    simp only [State.subs, setX_eq (d := 3) (i := 3) rfl, x_eq (d := 4) (i := 4) rfl,
      x_eq (d := 5) (i := 5) rfl, vflag]
    simp only [nflag, zflag, cflag, UInt64.toNat_sub, State.mk.injEq, eq_self_iff_true,
      true_and, and_true]
    simp (disch := first | omega | (split <;> omega)) only [word_n, word_z, word_c, word_v]
    simp (disch := omega) only [Nat.mod_eq_of_lt, decide_eq_decide]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · regs_end
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_ofNat', UInt64.toNat_sub]
      omega
    · (repeat' split) <;> omega
    · (repeat' split) <;> omega
    · (repeat' split) <;> omega
    · rcases Nat.lt_or_ge (State.regs $s 4).toNat (2 ^ 63) with _ | _ <;>
        rcases Nat.lt_or_ge (State.regs $s 5).toNat (2 ^ 63) with _ | _ <;>
        rcases Nat.lt_or_ge ((State.regs $s 4).toNat + (2 ^ 64 - (State.regs $s 5).toNat))
          (2 ^ 64) with _ | _ <;>
        rcases Nat.lt_or_ge (((State.regs $s 4).toNat + (2 ^ 64 - (State.regs $s 5).toNat)) %
          2 ^ 64) (2 ^ 63) with _ | _ <;>
        (repeat' split) <;> omega))

set_option maxHeartbeats 1000000 in
/-- The trace of `SUBS X3, X4, X5` agrees with `exec` from every state.  The proof of the V flag
takes 32 cases of `omega`, beyond the default budget of heartbeats. -/
theorem subs (P : Platform) (u : Unknown) (s : State) :
    Agrees P (config u) ["SEE", "__BranchTaken"] subsFp [] (.subsReg 3 4 5) s := by
  refine ⟨rfl, by decide, by decide, fun σ hσ s' hs => ?_⟩
  simp only [exec, Option.some.injEq] at hs
  subst hs
  isla_reads [subsFp, config_get, config] at hσ
  have := toNat_lt (s.regs 4)
  have := toNat_lt (s.regs 5)
  refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 17),
    fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
  · unfold Footprint.Run at h
    simp only [subsFp, Footprint.vars, List.foldl] at h
    isla_fwd h using omega with [hσ]
    subs_end s
  · subst h
    unfold Footprint.Run
    simp only [subsFp, Footprint.vars, List.foldl]
    isla_bwd [s.pc.toNat, (s.regs 4).toNat, (s.regs 5).toNat] using omega with [hσ]
    all_goals first
      | exact toNat_lt _
      | (apply Eq.symm; subs_end s)

end TestSupport.A64.Isla.Stage1

#print axioms TestSupport.A64.Isla.Stage1.subs
