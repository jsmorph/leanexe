import LeanExe.A64.Isla.Check
import LeanExe.A64.Isla.Profile

/-!
Theorems of `Agrees` for register forms of `LeanExe/A64/Machine.lean`, from the traces of
`tests/isla/tcg` and `tests/isla/kvm` under the profiles `tcg` and `kvm` with the arguments `tcr`.
The two traces of a register form are equal, so the theorem under `kvm` follows from the theorem
under `tcg`: the kernel checks that the two footprints are equal, and `Agrees.of_reads` carries the
theorem to `kvm`, which agrees with `tcg` on the registers that the trace reads.
`tests/isla/theorems.sh` elaborates the module and prints the axioms of its theorems.
-/

namespace TestSupport.A64.Isla

open LeanExe.A64 LeanExe.A64.Isla

/-- The footprint of `ADD Xd, Xn, Xm` under the profile `tcg`. -/
def addRegTcg : Footprint := isla_trace% "tests/isla/tcg/add-reg"

/-- The footprint of `ADD Xd, Xn, Xm` under the profile `kvm`. -/
def addRegKvm : Footprint := isla_trace% "tests/isla/kvm/add-reg"

/-- The fields of `ADD Xd, Xn, Xm` for the registers `d`, `n`, and `m`. -/
def addRegFields (d n m : Fin 32) : Fields := [("Rd", d.val), ("Rn", n.val), ("Rm", m.val)]

set_option maxHeartbeats 4000000 in
/-- The trace of `ADD Xd, Xn, Xm` under `tcg` agrees with `exec` for every register number, with
register 31 the zero register, and every state.  The backward direction builds the path of each of
the 8 cases of register 31 among `d`, `n`, and `m`, and the 706 events that the two directions
evaluate take more than the default budget of heartbeats. -/
theorem addReg_tcg (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (tcg.sys .tcr u) ["SEE", "__BranchTaken"] addRegTcg (addRegFields d n m)
      (.addReg d n m) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : addRegTcg.opcode.word (addRegFields d n m) = encodeNat (.addReg d n m) := by
      simp only [Opcode.word, Opcode.wordFrom, addRegTcg, addRegFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · simp only [exec, Option.some.injEq] at hs
    subst hs
    isla_reads [addRegTcg, Profile.sys_get, Profile.sys] at hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 14),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · unfold Footprint.Run at h
      simp only [addRegTcg, Footprint.vars, addRegFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD] at h
      isla_fwd h using omega with [hσ]
      all_goals gpr_end
    · subst h
      unfold Footprint.Run
      simp only [addRegTcg, Footprint.vars, addRegFields, List.foldl, List.lookup,
        String.reduceBEq, Option.getD]
      by_cases hn : n.val = 31 <;> by_cases hm : m.val = 31 <;> by_cases hd : d.val = 31
      all_goals
        isla_bwd [s.pc.toNat] using omega with [hσ, hn, hm, hd]
        try isla_gprs s using omega with [hσ, hn, hm, hd]
      all_goals first
        | exact toNat_lt _
        | gpr_end
        | (simp only [sint]; omega)
        | omega

/-- The trace of `ADD Xd, Xn, Xm` under `kvm` agrees with `exec` for every register number and
every state. -/
theorem addReg_kvm (P : Platform) (u : Unknown) (d n m : Fin 32) (s : State) :
    Agrees P (kvm.sys .tcr u) ["SEE", "__BranchTaken"] addRegKvm (addRegFields d n m)
      (.addReg d n m) s := by
  rw [show addRegKvm = addRegTcg from rfl]
  exact (addReg_tcg P u d n m s).of_reads
    (by isla_reads [addRegTcg, Profile.sys_get, Profile.sys])

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.addReg_tcg
#print axioms TestSupport.A64.Isla.addReg_kvm
