import LeanExe.A64.Isla.Check
import LeanExe.A64.Isla.Profile

/-!
The theorem of `LDR X3, [X4, #24]` from the trace of one encoding, `tests/isla/ldr.trace`.  Isla
e9b5d945 without the patch produced it, with Z3 4.12.6 and `armv9p4.ir` of isla-snapshots d8b31014
as built in `~/isla-probe` on edgexpert-18ff, from the entry point `isla_footprint_no_init` with
Isla's `configs/armv9p4.toml` and `-s --simplify-registers --tree`.  The processor runs at EL1
with SP_EL1 and debug exceptions masked (`-R PSTATE.EL=0b01`, `PSTATE.SP=0b1`, and
`PSTATE.D=0b1`), with `_EDSCR` 2, `MDCCSR_EL0`, `OSLSR_EL1`, `OSDLR_EL1`, and `DBGPRCR_EL1` 0, and
`SCTLR_EL1` `0x04000208`: the MMU, the alignment check, and big-endian data are off, and SA, the
stack pointer's alignment check, is on.  The opcode `f9400c83` is a concrete word
(`-x -e big -i`), which `ldr.opcode` holds in binary.  The trace runs with the reset constraint
`(X4 + 24) & 0xFFFFFFFFC0000007 = 0x40000000`, which puts the address at a multiple of 8 in
`0x40000000`-`0x7FFFFFFF`.
-/

namespace TestSupport.A64.Isla.Stage1

open LeanExe.A64 LeanExe.A64.Isla

/-- The values that this configuration leaves UNKNOWN and the trace reads: six system registers
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

/-- The registers outside the model that the trace reads under this configuration: the values
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

/-- The footprint of `LDR X3, [X4, #24]`. -/
def ldrFp : Footprint := isla_trace% "tests/isla/ldr"

/-- Reduces an equation between two functions that update register 3 of the same registers to
the equation between the values written. -/
macro "regs_end" : tactic => `(tactic| (
  funext j
  by_cases hj : j = 3 <;> simp only [hj, eq_self_iff_true, ↓reduceIte]))

/-- An address `a` with `a &&& 0xFFFFFFFFC0000007 = 0x40000000`, the constraint of the load's
trace, is a multiple of 8 in `0x40000000`-`0x7FFFFFFF` whose bits 52 to 63 are clear. -/
theorem ram {a : Nat} (h : a &&& 18446744072635809799 = 1073741824) (ha : a < 2 ^ 64) :
    a % 8 = 0 ∧ a / 2 ^ 30 = 1 ∧ a &&& 18442240474082181120 = 0 := by
  have and_eq : ∀ m, m &&& 18446744072635809799 = m → a &&& m = 1073741824 &&& m := by
    intro m hm
    calc a &&& m = a &&& (18446744072635809799 &&& m) := by
          rw [Nat.and_comm 18446744072635809799, hm]
      _ = 1073741824 &&& m := by rw [← Nat.and_assoc, h]
  have h7 : a &&& 7 = 0 := (and_eq 7 (by decide)).trans (by decide)
  have h8 : a % 8 = a &&& 7 := (Nat.and_two_pow_sub_one_eq_mod a 3).symm
  have hs : a >>> 30 &&& 17179869183 = 1 := by
    have := congrArg (· >>> 30) h
    simpa only [Nat.shiftRight_and_distrib, Nat.reduceShiftRight] using this
  have hm : a >>> 30 &&& 17179869183 = a >>> 30 % 2 ^ 34 := Nat.and_two_pow_sub_one_eq_mod _ 34
  rw [hm, Nat.shiftRight_eq_div_pow] at hs
  exact ⟨by omega, by omega, (and_eq _ (by decide)).trans (by decide)⟩

/-- Proves that the state at the end of the trace of `LDR` is `exec`'s: the trace writes to X3
the eight bytes at an address that the constraint on `X4 + 24` makes equal to it. -/
macro "ldr_end" : tactic => `(tactic| (
  done_end
  simp only [setX_eq (d := 3) (i := 3) rfl, load64_eq, State.mk.injEq, eq_self_iff_true,
    and_true]
  all_goals
    regs_end
    refine congrArg (fun a => UInt64.ofNat (bytes _ a 8)) ?_
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_ofNat', UInt64.toNat_add, UInt64.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod]
    omega))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
/-- The trace of `LDR X3, [X4, #24]` agrees with `exec` from every state whose address `X4 + 24`
is a multiple of 8 in `0x40000000`-`0x7FFFFFFF`, as the trace's constraint states.  The
comparison of `FeatureImpl`, a vector of 259 Booleans, recurses deeper than the default limit,
and the trace's 98 events take more than the default budget of heartbeats. -/
theorem ldr (P : Platform) (u : Unknown) (s : State)
    (ha : (s.regs 4 + 24) &&& 0xFFFFFFFFC0000007 = 0x40000000) :
    Agrees P (config u) ["SEE", "__BranchTaken", "InGuardedPage"] ldrFp [] (.ldr 3 4 3) s := by
  have h4 := toNat_lt (s.regs 4)
  have hA : ((s.regs 4).toNat + 24) % 18446744073709551616 &&& 18446744072635809799 =
      1073741824 := by
    have := congrArg UInt64.toNat ha
    simpa [UInt64.toNat_and, UInt64.toNat_add] using this
  obtain ⟨h8, h30, hh⟩ := ram hA (Nat.mod_lt _ (by decide))
  have h4' : (s.regs 4).toNat % 18446744073709551616 = (s.regs 4).toNat := Nat.mod_eq_of_lt h4
  have hx : s.xsp 4 + UInt64.ofNat (8 * (3 : Fin 4096).val) = s.regs 4 + 24 := rfl
  refine ⟨rfl, by decide, by decide, fun σ hσ s' hs => ?_⟩
  simp only [exec, hx] at hs
  split at hs
  · simp only [Option.some.injEq] at hs
    subst hs
    isla_reads [ldrFp, config_get, config] at hσ
    refine ⟨((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)).set
      "InGuardedPage" (.bool false), fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · unfold Footprint.Run at h
      simp only [ldrFp, Footprint.vars, List.foldl] at h
      isla_fwd h using exact hA with [hσ, features, sysreg]
      ldr_end
    · subst h
      unfold Footprint.Run
      simp only [ldrFp, Footprint.vars, List.foldl]
      isla_bwd [u.feature, (s.regs 4).toNat, s.pc.toNat, u.mair.toNat, u.mair2.toNat,
        u.pir.toNat, u.pire0.toNat, u.sctlr2.toNat, u.s2pir.toNat,
        bytes s.mem (s.regs 4 + 24) 8] using exact hA
        with [hσ, features, sysreg]
      all_goals first
        | exact toNat_lt _
        | exact hA
        | (apply Eq.symm; ldr_end)
        | (rw [← load64_toNat]; exact toNat_lt _)
        | (simp only [h4'] at *; first | exact hh | omega)
        | (simp only [sint, sdiv, udiv, neg]; (repeat' split) <;> omega)
        | (refine congrArg (fun a => bytes _ a 8) ?_
           apply UInt64.toNat_inj.mp
           simp only [UInt64.toNat_ofNat', UInt64.toNat_add, UInt64.toNat_ofNat, Nat.reducePow,
             Nat.reduceMod]
           omega)
  · cases hs

end TestSupport.A64.Isla.Stage1

#print axioms TestSupport.A64.Isla.Stage1.ldr
