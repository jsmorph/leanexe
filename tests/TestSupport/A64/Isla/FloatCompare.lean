import LeanExe.A64.Isla.Float

/-!
Theorems of `AgreesAll` for `FCMP Dn, Dm` of `LeanExe/A64/Machine.lean`, the comparison of two
doubles that sets the flags, from the traces of `tests/isla/tcg`, `tests/isla/kvm`, and
`tests/isla/sme` under the profiles `tcg`, `kvm`, and `sme` with the arguments `fp` of
`tests/isla/traces.sh`.  Each theorem holds for every value of every register field, register 31
included, and every state.  The trace calls `FPCompare`, which `traces.sh` leaves abstract, and
writes the four bits of its result to PSTATE's N, Z, C, and V, and the theorem takes the equation
`FPCompareEq` of `LeanExe/A64/Isla/Float.lean` as a hypothesis on the meanings `A`.  Each trace has
one path, in the profile `sme` as well, since `FCMP` neither writes a D register nor tests
`IsMerging`, but its abstract call needs the meanings, so the theorem states `AgreesAll`, with
FPSR among the changed registers: Arm's `FPCompare` sets FPSR's IOC for a signaling NaN, which the
abstract call leaves out of the trace.

The proofs walk the traces with the tactics of `LeanExe/A64/Isla/Walk.lean` and
`LeanExe/A64/Isla/Float.lean`.  The forward lemma takes the path to `exec`'s state, and the backward
lemma builds it, with the decoder's tests of `Rm`, which hold for every value of the field.
`tests/isla/theorems.sh` elaborates the module and prints the axioms of its theorems.
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
/-- The footprint of `FCMP Dn, Dm` under the profile `tcg`. -/
def fcmpTcg : Footprint := isla_trace% "tests/isla/tcg/fcmp"

isla_nodes fcmpTcg

set_option maxRecDepth 100000 in
theorem fcmpTcg_n0 : fcmpTcg.trace = fcmpTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fcmpTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fcmpTcg` ends in `exec`'s state. -/
theorem fcmpTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPCompareEq A) (hσ : fcmpTcg.ctx σ u)
    (h : fcmpTcg.Run P (fcmpFields n m) s σ o A) :
    o = .done { s.fcmp (s.dregs n) (s.dregs m) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 272)) := by
  without_info
    have := n.isLt
    have := m.isLt
    unfold FPCompareEq at hA
    unfold Footprint.Run at h
    rw [fcmpTcg_n0, show fcmpTcg.vars (fcmpFields n m) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals flags_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fcmpTcg` has a path to `exec`'s state. -/
theorem fcmpTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPCompareEq A) (hσ : fcmpTcg.ctx σ u) :
    fcmpTcg.Run P (fcmpFields n m) s σ
      (.done { s.fcmp (s.dregs n) (s.dregs m) with pc := s.pc + 4 }
        ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 272))) A := by
  without_info
    have := n.isLt
    have := m.isLt
    unfold FPCompareEq at hA
    unfold Footprint.Run
    rw [fcmpTcg_n0, show fcmpTcg.vars (fcmpFields n m) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val) from rfl]
    fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | (apply Eq.symm; flags_end; done)
      | fp_side hσ [hA, fcmpNZCV_lt]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FCMP Dn, Dm` under `tcg` agrees with `exec` for every register number and every
state, where `A` satisfies `FPCompareEq`. -/
theorem fcmp_tcg (P : Platform) (A : Abstract) (hA : FPCompareEq A)
    (u : Unknown) (n m : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "FPSR"] fcmpTcg
      (fcmpFields n m) (.fcmp n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fcmpTcg, fcmpFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fcmpTcg.ctx_of σ u hσ
      exact ⟨⟨_, fcmpTcg_bwd hA hc⟩, fun o h => ⟨_, fcmpTcg_fwd hA hc h, by frame_end⟩⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FCMP Dn, Dm` under the profile `kvm`. -/
def fcmpKvm : Footprint := isla_trace% "tests/isla/kvm/fcmp"

isla_nodes fcmpKvm

set_option maxRecDepth 100000 in
theorem fcmpKvm_n0 : fcmpKvm.trace = fcmpKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fcmpKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fcmpKvm` ends in `exec`'s state. -/
theorem fcmpKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPCompareEq A) (hσ : fcmpKvm.ctx σ u)
    (h : fcmpKvm.Run P (fcmpFields n m) s σ o A) :
    o = .done { s.fcmp (s.dregs n) (s.dregs m) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 272)) := by
  without_info
    have := n.isLt
    have := m.isLt
    unfold FPCompareEq at hA
    unfold Footprint.Run at h
    rw [fcmpKvm_n0, show fcmpKvm.vars (fcmpFields n m) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals flags_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fcmpKvm` has a path to `exec`'s state. -/
theorem fcmpKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPCompareEq A) (hσ : fcmpKvm.ctx σ u) :
    fcmpKvm.Run P (fcmpFields n m) s σ
      (.done { s.fcmp (s.dregs n) (s.dregs m) with pc := s.pc + 4 }
        ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 272))) A := by
  without_info
    have := n.isLt
    have := m.isLt
    unfold FPCompareEq at hA
    unfold Footprint.Run
    rw [fcmpKvm_n0, show fcmpKvm.vars (fcmpFields n m) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val) from rfl]
    fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | (apply Eq.symm; flags_end; done)
      | fp_side hσ [hA, fcmpNZCV_lt]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FCMP Dn, Dm` under `kvm` agrees with `exec` for every register number and every
state, where `A` satisfies `FPCompareEq`. -/
theorem fcmp_kvm (P : Platform) (A : Abstract) (hA : FPCompareEq A)
    (u : Unknown) (n m : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "FPSR"] fcmpKvm
      (fcmpFields n m) (.fcmp n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fcmpKvm, fcmpFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fcmpKvm.ctx_of σ u hσ
      exact ⟨⟨_, fcmpKvm_bwd hA hc⟩, fun o h => ⟨_, fcmpKvm_fwd hA hc h, by frame_end⟩⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FCMP Dn, Dm` under the profile `sme`. -/
def fcmpSme : Footprint := isla_trace% "tests/isla/sme/fcmp"

isla_nodes fcmpSme

set_option maxRecDepth 100000 in
theorem fcmpSme_n0 : fcmpSme.trace = fcmpSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fcmpSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fcmpSme` ends in `exec`'s state. -/
theorem fcmpSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPCompareEq A) (hσ : fcmpSme.ctx σ u)
    (h : fcmpSme.Run P (fcmpFields n m) s σ o A) :
    o = .done { s.fcmp (s.dregs n) (s.dregs m) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 272)) := by
  without_info
    have := n.isLt
    have := m.isLt
    unfold FPCompareEq at hA
    unfold Footprint.Run at h
    rw [fcmpSme_n0, show fcmpSme.vars (fcmpFields n m) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals flags_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fcmpSme` has a path to `exec`'s state. -/
theorem fcmpSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPCompareEq A) (hσ : fcmpSme.ctx σ u) :
    fcmpSme.Run P (fcmpFields n m) s σ
      (.done { s.fcmp (s.dregs n) (s.dregs m) with pc := s.pc + 4 }
        ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 272))) A := by
  without_info
    have := n.isLt
    have := m.isLt
    unfold FPCompareEq at hA
    unfold Footprint.Run
    rw [fcmpSme_n0, show fcmpSme.vars (fcmpFields n m) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val) from rfl]
    fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | (apply Eq.symm; flags_end; done)
      | fp_side hσ [hA, fcmpNZCV_lt]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FCMP Dn, Dm` under `sme` agrees with `exec` for every register number and every
state, where `A` satisfies `FPCompareEq`. -/
theorem fcmp_sme (P : Platform) (A : Abstract) (hA : FPCompareEq A)
    (u : Unknown) (n m : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "FPSR"] fcmpSme
      (fcmpFields n m) (.fcmp n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fcmpSme, fcmpFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fcmpSme.ctx_of σ u hσ
      exact ⟨⟨_, fcmpSme_bwd hA hc⟩, fun o h => ⟨_, fcmpSme_fwd hA hc h, by frame_end⟩⟩

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.fcmp_tcg
#print axioms TestSupport.A64.Isla.fcmp_kvm
#print axioms TestSupport.A64.Isla.fcmp_sme
