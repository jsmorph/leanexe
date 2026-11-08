import LeanExe.M7.Isla.Check
import LeanExe.M7.Isla.Profile

/-!
The theorem of `Agrees` for `DSB SY` of `LeanExe/M7/Machine.lean`, from the trace of `tests/isla/m7`
under the profile `sys` of `LeanExe/M7/Isla/Profile.lean`.  It holds for every machine whose
program counter plus 4 is below 2^32, every platform, and every sequence of device values.
`tests/isla/m7-theorems.sh` elaborates the module and prints the axioms of its theorem.

The opcode of `DSB SY` matches the decode clause of B T3 with the condition 1110, which writes
`__currentCond` and sends the opcode to another encoding through an SEE exception, so the trace
writes `SEE` and `__currentCond` twice before the barrier's own clause.  The barrier is a
`sail_barrier` event, which the reader of `LeanExe/A64/Isla/Trace.lean` reads as a skip, and the
trace has one path, which ends with the program counter advanced by 4.
-/

namespace TestSupport.M7.Isla

open LeanExe.M7 LeanExe.M7.Isla
open LeanExe.A64.Isla (Footprint Fields Opcode)

/-- The footprint of `DSB SY`. -/
def dsbT : Footprint := isla_trace% "tests/isla/m7/dsb"

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- The trace of `DSB SY` agrees with `exec` for every machine whose program counter plus 4 is
below 2^32. -/
theorem dsb_agrees (P : Platform) (δ : Nat → UInt32) (u : Unknown) (m : Mach)
    (hpc : m.s.pc.toNat + 4 < 4294967296) :
    Agrees P δ (sys u) ["SEE", "__BranchTaken", "__currentCond"] dsbT [] .dsb m := by
  without_info
    refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
    · apply decode_halves (by decide) (by intro h; cases h)
      simp only [Opcode.word, LeanExe.A64.Isla.Opcode.wordFrom, dsbT, encodeNat, List.lookup,
        Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] <;> omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      t32_reads [dsbT, sys_get, sys] at hσ
      refine ⟨((((σ.set "__BranchTaken" (.bool false)).set "__currentCond" (.bits 4 14)).set "SEE"
        (.bits 128 2854)).set "__currentCond" (.bits 4 14)).set "SEE" (.bits 128 2902),
        fun o h => ?_, ?_, by t32_frame⟩
      · unfold footRun at h
        simp only [dsbT, LeanExe.A64.Isla.Footprint.vars, List.foldl,
          LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd, Nat.reduceDiv] at h
        t32_fwd h using omega with [hσ]
        all_goals
          simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
          t32_pc
          exact ⟨m.hi, rfl⟩
      · unfold footRun
        simp only [dsbT, LeanExe.A64.Isla.Footprint.vars, List.foldl,
          LeanExe.A64.Isla.Opcode.width, Nat.reduceAdd, Nat.reduceDiv]
        t32_bwd [u.feature, m.s.pc.toNat, u.hcr32.toNat] using omega with [hσ]
        all_goals first
          | (simp only [finish, LeanExe.A64.Isla.Sys.set_apply, String.reduceEq, ↓reduceIte]
             t32_pc
             rfl)
          | exact BitVec.isLt _
          | t32_side

#print axioms dsb_agrees

end TestSupport.M7.Isla
