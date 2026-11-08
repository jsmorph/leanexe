import LeanExe.A64.Isla.Float

/-!
Theorems of `AgreesAll` for `FCVTZU Xd, Dn` of `LeanExe/A64/Machine.lean`, the conversion of a
double to an unsigned 64-bit integer, from the traces of `tests/isla/tcg`, `tests/isla/kvm`, and
`tests/isla/sme` under the profiles `tcg`, `kvm`, and `sme` with the arguments `fp` of
`tests/isla/traces.sh`.  Each theorem holds for every value of every register field, register 31
included, and every state.  The trace calls the abstract wrapper `FPToFixed64`, and the theorem
takes its equation `FPToFixedEq` of `LeanExe/A64/Isla/Float.lean` as a hypothesis on the meanings
`A`.  The form writes a general register, so each trace has one outcome, but its abstract call
needs the meanings, so the theorem states `AgreesAll`, with FPSR among the changed registers:
Arm's `FPToFixed` sets FPSR's cumulative exception bits, which the abstract call leaves out of
the trace.  The trace of `sme` branches on `PSTATE.SM` and, in Streaming SVE mode, on the FA64
bits of `SMCR_EL1` and `SMCR_EL2`, as that of `FMOV Xd, Dn` does, and every branch ends in
`exec`'s state.

The proofs walk the traces with the tactics of `LeanExe/A64/Isla/Walk.lean` and
`LeanExe/A64/Isla/Float.lean`.  The forward lemma takes every path to `exec`'s state, and the
backward lemma builds one, after a case split on the destination register 31, the zero register,
and under `sme` on those bits.  `tests/isla/theorems.sh` elaborates the module and prints the
axioms of its theorems.
-/

namespace TestSupport.A64.Isla

open LeanExe.A64 LeanExe.A64.Isla

/- The lemmas elaborate one after another, so that the peak of memory is that of one lemma's walk.
The traces compute masks of 2048 bits, whose powers of 2 `simp` evaluates only below the
threshold. -/
set_option Elab.async false
set_option exponentiation.threshold 4096

attribute [local congr] run_congr runSome_congr

set_option maxRecDepth 100000 in
/-- The footprint of `FCVTZU Xd, Dn` under the profile `tcg`. -/
def fcvtzuTcg : Footprint := isla_trace% "tests/isla/tcg/fcvtzu"

isla_nodes fcvtzuTcg

set_option maxRecDepth 100000 in
theorem fcvtzuTcg_n0 : fcvtzuTcg.trace = fcvtzuTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fcvtzuTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fcvtzuTcg` ends in `exec`'s state. -/
theorem fcvtzuTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPToFixedEq A) (hσ : fcvtzuTcg.ctx σ u)
    (h : fcvtzuTcg.Run P (fpFields2 d n) s σ o A) :
    o = .done { s.setX d (Wasm.i64TruncSatF64U (s.dregs n)) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 293)) := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixedEq at hA
    unfold Footprint.Run at h
    rw [fcvtzuTcg_n0, show fcvtzuTcg.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals xreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fcvtzuTcg` has a path to `exec`'s state. -/
theorem fcvtzuTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPToFixedEq A) (hσ : fcvtzuTcg.ctx σ u) :
    fcvtzuTcg.Run P (fpFields2 d n) s σ
      (.done { s.setX d (Wasm.i64TruncSatF64U (s.dregs n)) with pc := s.pc + 4 }
        ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 293))) A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixedEq at hA
    by_cases h0 : d.val = 31
    rotate_left
    rotate_left
    all_goals
      unfold Footprint.Run
      rw [fcvtzuTcg_n0, show fcvtzuTcg.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | (apply Eq.symm; xreg_end; done)
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FCVTZU Xd, Dn` under `tcg` agrees with `exec` for every register number and
every state, where `A` satisfies `FPToFixedEq`. -/
theorem fcvtzu_tcg (P : Platform) (A : Abstract) (hA : FPToFixedEq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "FPSR"] fcvtzuTcg
      (fpFields2 d n) (.fcvtzu d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fcvtzuTcg, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fcvtzuTcg.ctx_of σ u hσ
      exact ⟨⟨_, fcvtzuTcg_bwd hA hc⟩, fun o h => ⟨_, fcvtzuTcg_fwd hA hc h, by frame_end⟩⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FCVTZU Xd, Dn` under the profile `kvm`. -/
def fcvtzuKvm : Footprint := isla_trace% "tests/isla/kvm/fcvtzu"

isla_nodes fcvtzuKvm

set_option maxRecDepth 100000 in
theorem fcvtzuKvm_n0 : fcvtzuKvm.trace = fcvtzuKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fcvtzuKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fcvtzuKvm` ends in `exec`'s state. -/
theorem fcvtzuKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPToFixedEq A) (hσ : fcvtzuKvm.ctx σ u)
    (h : fcvtzuKvm.Run P (fpFields2 d n) s σ o A) :
    o = .done { s.setX d (Wasm.i64TruncSatF64U (s.dregs n)) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 293)) := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixedEq at hA
    unfold Footprint.Run at h
    rw [fcvtzuKvm_n0, show fcvtzuKvm.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals xreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fcvtzuKvm` has a path to `exec`'s state. -/
theorem fcvtzuKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPToFixedEq A) (hσ : fcvtzuKvm.ctx σ u) :
    fcvtzuKvm.Run P (fpFields2 d n) s σ
      (.done { s.setX d (Wasm.i64TruncSatF64U (s.dregs n)) with pc := s.pc + 4 }
        ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 293))) A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixedEq at hA
    by_cases h0 : d.val = 31
    rotate_left
    rotate_left
    all_goals
      unfold Footprint.Run
      rw [fcvtzuKvm_n0, show fcvtzuKvm.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | (apply Eq.symm; xreg_end; done)
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FCVTZU Xd, Dn` under `kvm` agrees with `exec` for every register number and
every state, where `A` satisfies `FPToFixedEq`. -/
theorem fcvtzu_kvm (P : Platform) (A : Abstract) (hA : FPToFixedEq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "FPSR"] fcvtzuKvm
      (fpFields2 d n) (.fcvtzu d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fcvtzuKvm, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fcvtzuKvm.ctx_of σ u hσ
      exact ⟨⟨_, fcvtzuKvm_bwd hA hc⟩, fun o h => ⟨_, fcvtzuKvm_fwd hA hc h, by frame_end⟩⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FCVTZU Xd, Dn` under the profile `sme`. -/
def fcvtzuSme : Footprint := isla_trace% "tests/isla/sme/fcvtzu"

isla_nodes fcvtzuSme

set_option maxRecDepth 100000 in
theorem fcvtzuSme_n0 : fcvtzuSme.trace = fcvtzuSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fcvtzuSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fcvtzuSme` ends in `exec`'s state. -/
theorem fcvtzuSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPToFixedEq A) (hσ : fcvtzuSme.ctx σ u)
    (h : fcvtzuSme.Run P (fpFields2 d n) s σ o A) :
    o = .done { s.setX d (Wasm.i64TruncSatF64U (s.dregs n)) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 293)) := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixedEq at hA
    unfold Footprint.Run at h
    rw [fcvtzuSme_n0, show fcvtzuSme.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals xreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fcvtzuSme` has a path to `exec`'s state. -/
theorem fcvtzuSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPToFixedEq A) (hσ : fcvtzuSme.ctx σ u) :
    fcvtzuSme.Run P (fpFields2 d n) s σ
      (.done { s.setX d (Wasm.i64TruncSatF64U (s.dregs n)) with pc := s.pc + 4 }
        ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 293))) A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixedEq at hA
    by_cases h0 : d.val = 31
    by_cases h1 : u.sm.toNat = 1
    by_cases h2 : u.smcr1.toNat / 2147483648 % 2 = 0
    rotate_left
    by_cases h3 : u.smcr2.toNat / 2147483648 % 2 = 0
    rotate_left
    rotate_left
    rotate_left
    by_cases h4 : u.sm.toNat = 1
    by_cases h5 : u.smcr1.toNat / 2147483648 % 2 = 0
    rotate_left
    by_cases h6 : u.smcr2.toNat / 2147483648 % 2 = 0
    rotate_left
    rotate_left
    rotate_left
    all_goals
      unfold Footprint.Run
      rw [fcvtzuSme_n0, show fcvtzuSme.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | (apply Eq.symm; xreg_end; done)
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FCVTZU Xd, Dn` under `sme` agrees with `exec` for every register number and
every state, where `A` satisfies `FPToFixedEq`. -/
theorem fcvtzu_sme (P : Platform) (A : Abstract) (hA : FPToFixedEq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "FPSR"] fcvtzuSme
      (fpFields2 d n) (.fcvtzu d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fcvtzuSme, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fcvtzuSme.ctx_of σ u hσ
      exact ⟨⟨_, fcvtzuSme_bwd hA hc⟩, fun o h => ⟨_, fcvtzuSme_fwd hA hc h, by frame_end⟩⟩

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.fcvtzu_tcg
#print axioms TestSupport.A64.Isla.fcvtzu_kvm
#print axioms TestSupport.A64.Isla.fcvtzu_sme
