import LeanExe.A64.Isla.Float

/-!
Theorems of `Agrees` and `AgreesAll` for the floating-point forms of `LeanExe/A64/Machine.lean`:
`FMOV Xd, Dn`, `FMOV Dd, Xn`, FADD, FSUB, FMUL, FDIV, FSQRT, and `UCVTF Dd, Xn`, from the traces
of `tests/isla/tcg` and `tests/isla/kvm` under the profiles `tcg` and `kvm` with the arguments `fp`
of `tests/isla/traces.sh`.  Each theorem holds for every value of every register field, register
31 included, and every state.  The two traces of a form differ in their reads of `FeatureImpl`,
`HCR_EL2`, `PSTATE.nRW`, `CPTR_EL2`, and `CPTR_EL3`, so each profile has its own proof.
`tests/isla/theorems.sh` elaborates the module and prints the axioms of its theorems.

`FMOV Xd, Dn` writes a general register and has one outcome, and its theorem states `Agrees`.
Every other form writes a D register through `V_set`, whose CONSTRAINED UNPREDICTABLE choice to
zero or keep the bits of the register's element of `_Z` above bit 127 gives two outcomes that
differ in those bits, so its theorem states `AgreesAll` with `_Z` among the changed registers.
The arithmetic forms and UCVTF call the abstract wrapper of an Arm function, and the theorem
takes the wrapper's equation of `LeanExe/A64/Isla/Float.lean` as a hypothesis on the meanings
`A`.  Such a theorem lists FPSR among the changed registers: Arm's function sets FPSR's
cumulative exception bits, which the abstract call leaves out of the trace.

The proofs walk the traces with the tactics of `LeanExe/A64/Isla/Walk.lean` and
`LeanExe/A64/Isla/Float.lean`.  The forward lemma of a form takes every path to `exec`'s state,
and the backward lemma builds one path, after a case split on each condition on the fields that
the trace tests: register 31 as the zero register, the source of `FMOV Dd, Xn` and UCVTF and the
destination of `FMOV Xd, Dn`, and the bits of `Rm` that the decoder tests on its way to FMUL and
FDIV.  The theorem joins them: the backward lemma gives an outcome, and the forward lemma states
that it and every other outcome are `exec`'s state.
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
/-- The footprint of `FMOV Xd, Dn` under the profile `tcg`. -/
def fmovXdTcg : Footprint := isla_trace% "tests/isla/tcg/fmov-xd"

isla_nodes fmovXdTcg

set_option maxRecDepth 100000 in
theorem fmovXdTcg_n0 : fmovXdTcg.trace = fmovXdTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmovXdTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmovXdTcg` ends in `exec`'s state. -/
theorem fmovXdTcg_fwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hσ : fmovXdTcg.ctx σ u)
    (h : fmovXdTcg.Run P (fpFields2 d n) s σ o) :
    o = .done { s.setX d (s.dregs n) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 295)) := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold Footprint.Run at h
    rw [fmovXdTcg_n0, show fmovXdTcg.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ]
    all_goals xreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmovXdTcg` has a path to an outcome. -/
theorem fmovXdTcg_bwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hσ : fmovXdTcg.ctx σ u) :
    fmovXdTcg.Run P (fpFields2 d n) s σ (.done { s.setX d (s.dregs n) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 295))) := by
  without_info
    have := d.isLt
    have := n.isLt
    by_cases h0 : d.val = 31
    rotate_left
    rotate_left
    all_goals
      unfold Footprint.Run
      rw [fmovXdTcg_n0, show fmovXdTcg.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ]
    all_goals first
      | (apply Eq.symm; xreg_end; done)
      | fp_side hσ []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMOV Xd, Dn` under `tcg` agrees with `exec` for every register number and
every state. -/
theorem fmovXd_tcg (P : Platform) 
    (u : Unknown) (d n : Fin 32) (s : State) :
    Agrees P (tcg.sys .fp u) ["SEE", "__BranchTaken"] fmovXdTcg
      (fpFields2 d n) (.fmovXD d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmovXdTcg, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmovXdTcg.ctx_of σ u hσ
      exact ⟨_, fun o => ⟨fun h => fmovXdTcg_fwd hc h, fun h => h ▸ fmovXdTcg_bwd hc⟩,
        by frame_end⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FMOV Xd, Dn` under the profile `kvm`. -/
def fmovXdKvm : Footprint := isla_trace% "tests/isla/kvm/fmov-xd"

isla_nodes fmovXdKvm

set_option maxRecDepth 100000 in
theorem fmovXdKvm_n0 : fmovXdKvm.trace = fmovXdKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmovXdKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmovXdKvm` ends in `exec`'s state. -/
theorem fmovXdKvm_fwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hσ : fmovXdKvm.ctx σ u)
    (h : fmovXdKvm.Run P (fpFields2 d n) s σ o) :
    o = .done { s.setX d (s.dregs n) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 295)) := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold Footprint.Run at h
    rw [fmovXdKvm_n0, show fmovXdKvm.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ]
    all_goals xreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmovXdKvm` has a path to an outcome. -/
theorem fmovXdKvm_bwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hσ : fmovXdKvm.ctx σ u) :
    fmovXdKvm.Run P (fpFields2 d n) s σ (.done { s.setX d (s.dregs n) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 295))) := by
  without_info
    have := d.isLt
    have := n.isLt
    by_cases h0 : d.val = 31
    rotate_left
    rotate_left
    all_goals
      unfold Footprint.Run
      rw [fmovXdKvm_n0, show fmovXdKvm.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ]
    all_goals first
      | (apply Eq.symm; xreg_end; done)
      | fp_side hσ []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMOV Xd, Dn` under `kvm` agrees with `exec` for every register number and
every state. -/
theorem fmovXd_kvm (P : Platform) 
    (u : Unknown) (d n : Fin 32) (s : State) :
    Agrees P (kvm.sys .fp u) ["SEE", "__BranchTaken"] fmovXdKvm
      (fpFields2 d n) (.fmovXD d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmovXdKvm, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmovXdKvm.ctx_of σ u hσ
      exact ⟨_, fun o => ⟨fun h => fmovXdKvm_fwd hc h, fun h => h ▸ fmovXdKvm_bwd hc⟩,
        by frame_end⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FMOV Dd, Xn` under the profile `tcg`. -/
def fmovDxTcg : Footprint := isla_trace% "tests/isla/tcg/fmov-dx"

isla_nodes fmovDxTcg

set_option maxRecDepth 100000 in
theorem fmovDxTcg_n0 : fmovDxTcg.trace = fmovDxTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmovDxTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmovDxTcg` ends in `exec`'s state. -/
theorem fmovDxTcg_fwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hσ : fmovDxTcg.ctx σ u)
    (h : fmovDxTcg.Run P (fpFields2 d n) s σ o) :
    ∃ σ', o = .done
      { s.setD d (s.x n) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold Footprint.Run at h
    rw [fmovDxTcg_n0, show fmovDxTcg.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmovDxTcg` has a path to an outcome. -/
theorem fmovDxTcg_bwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hσ : fmovDxTcg.ctx σ u) :
    ∃ o, fmovDxTcg.Run P (fpFields2 d n) s σ o := by
  without_info
    have := d.isLt
    have := n.isLt
    by_cases h0 : n.val = 31
    rotate_left
    rotate_left
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fmovDxTcg_n0, show fmovDxTcg.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ]
    all_goals first
      | rfl
      | fp_side hσ []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMOV Dd, Xn` under `tcg` agrees with `exec` for every register number and
every state. -/
theorem fmovDx_tcg (P : Platform) 
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P noAbstract (tcg.sys .fp u) ["SEE", "__BranchTaken", "_Z"] fmovDxTcg
      (fpFields2 d n) (.fmovDX d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmovDxTcg, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmovDxTcg.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fmovDxTcg_bwd (P := P) (d := d) (n := n) (s := s) hc
      obtain ⟨σ', rfl, -⟩ := fmovDxTcg_fwd hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fmovDxTcg_fwd hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FMOV Dd, Xn` under the profile `kvm`. -/
def fmovDxKvm : Footprint := isla_trace% "tests/isla/kvm/fmov-dx"

isla_nodes fmovDxKvm

set_option maxRecDepth 100000 in
theorem fmovDxKvm_n0 : fmovDxKvm.trace = fmovDxKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmovDxKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmovDxKvm` ends in `exec`'s state. -/
theorem fmovDxKvm_fwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hσ : fmovDxKvm.ctx σ u)
    (h : fmovDxKvm.Run P (fpFields2 d n) s σ o) :
    ∃ σ', o = .done
      { s.setD d (s.x n) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold Footprint.Run at h
    rw [fmovDxKvm_n0, show fmovDxKvm.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmovDxKvm` has a path to an outcome. -/
theorem fmovDxKvm_bwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hσ : fmovDxKvm.ctx σ u) :
    ∃ o, fmovDxKvm.Run P (fpFields2 d n) s σ o := by
  without_info
    have := d.isLt
    have := n.isLt
    by_cases h0 : n.val = 31
    rotate_left
    rotate_left
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fmovDxKvm_n0, show fmovDxKvm.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ]
    all_goals first
      | rfl
      | fp_side hσ []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMOV Dd, Xn` under `kvm` agrees with `exec` for every register number and
every state. -/
theorem fmovDx_kvm (P : Platform) 
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P noAbstract (kvm.sys .fp u) ["SEE", "__BranchTaken", "_Z"] fmovDxKvm
      (fpFields2 d n) (.fmovDX d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmovDxKvm, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmovDxKvm.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fmovDxKvm_bwd (P := P) (d := d) (n := n) (s := s) hc
      obtain ⟨σ', rfl, -⟩ := fmovDxKvm_fwd hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fmovDxKvm_fwd hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FADD Dd, Dn, Dm` under the profile `tcg`. -/
def faddTcg : Footprint := isla_trace% "tests/isla/tcg/fadd"

isla_nodes faddTcg

set_option maxRecDepth 100000 in
theorem faddTcg_n0 : faddTcg.trace = faddTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx faddTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `faddTcg` ends in `exec`'s state. -/
theorem faddTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPAddEq A) (hσ : faddTcg.ctx σ u)
    (h : faddTcg.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f64Add (s.dregs n) (s.dregs m)) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPAddEq at hA
    unfold Footprint.Run at h
    rw [faddTcg_n0, show faddTcg.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `faddTcg` has a path to an outcome. -/
theorem faddTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPAddEq A) (hσ : faddTcg.ctx σ u) :
    ∃ o, faddTcg.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPAddEq at hA
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [faddTcg_n0, show faddTcg.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | rfl
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FADD Dd, Dn, Dm` under `tcg` agrees with `exec` for every register number and
every state, where `A` satisfies `FPAddEq`. -/
theorem fadd_tcg (P : Platform) (A : Abstract) (hA : FPAddEq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] faddTcg
      (fpFields3 d n m) (.fadd d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, faddTcg, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := faddTcg.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := faddTcg_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := faddTcg_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => faddTcg_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FADD Dd, Dn, Dm` under the profile `kvm`. -/
def faddKvm : Footprint := isla_trace% "tests/isla/kvm/fadd"

isla_nodes faddKvm

set_option maxRecDepth 100000 in
theorem faddKvm_n0 : faddKvm.trace = faddKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx faddKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `faddKvm` ends in `exec`'s state. -/
theorem faddKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPAddEq A) (hσ : faddKvm.ctx σ u)
    (h : faddKvm.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f64Add (s.dregs n) (s.dregs m)) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPAddEq at hA
    unfold Footprint.Run at h
    rw [faddKvm_n0, show faddKvm.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `faddKvm` has a path to an outcome. -/
theorem faddKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPAddEq A) (hσ : faddKvm.ctx σ u) :
    ∃ o, faddKvm.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPAddEq at hA
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [faddKvm_n0, show faddKvm.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | rfl
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FADD Dd, Dn, Dm` under `kvm` agrees with `exec` for every register number and
every state, where `A` satisfies `FPAddEq`. -/
theorem fadd_kvm (P : Platform) (A : Abstract) (hA : FPAddEq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] faddKvm
      (fpFields3 d n m) (.fadd d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, faddKvm, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := faddKvm.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := faddKvm_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := faddKvm_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => faddKvm_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FSUB Dd, Dn, Dm` under the profile `tcg`. -/
def fsubTcg : Footprint := isla_trace% "tests/isla/tcg/fsub"

isla_nodes fsubTcg

set_option maxRecDepth 100000 in
theorem fsubTcg_n0 : fsubTcg.trace = fsubTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fsubTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fsubTcg` ends in `exec`'s state. -/
theorem fsubTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPSubEq A) (hσ : fsubTcg.ctx σ u)
    (h : fsubTcg.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f64Sub (s.dregs n) (s.dregs m)) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPSubEq at hA
    unfold Footprint.Run at h
    rw [fsubTcg_n0, show fsubTcg.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fsubTcg` has a path to an outcome. -/
theorem fsubTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPSubEq A) (hσ : fsubTcg.ctx σ u) :
    ∃ o, fsubTcg.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPSubEq at hA
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fsubTcg_n0, show fsubTcg.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | rfl
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FSUB Dd, Dn, Dm` under `tcg` agrees with `exec` for every register number and
every state, where `A` satisfies `FPSubEq`. -/
theorem fsub_tcg (P : Platform) (A : Abstract) (hA : FPSubEq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fsubTcg
      (fpFields3 d n m) (.fsub d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fsubTcg, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fsubTcg.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fsubTcg_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fsubTcg_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fsubTcg_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FSUB Dd, Dn, Dm` under the profile `kvm`. -/
def fsubKvm : Footprint := isla_trace% "tests/isla/kvm/fsub"

isla_nodes fsubKvm

set_option maxRecDepth 100000 in
theorem fsubKvm_n0 : fsubKvm.trace = fsubKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fsubKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fsubKvm` ends in `exec`'s state. -/
theorem fsubKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPSubEq A) (hσ : fsubKvm.ctx σ u)
    (h : fsubKvm.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f64Sub (s.dregs n) (s.dregs m)) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPSubEq at hA
    unfold Footprint.Run at h
    rw [fsubKvm_n0, show fsubKvm.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fsubKvm` has a path to an outcome. -/
theorem fsubKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPSubEq A) (hσ : fsubKvm.ctx σ u) :
    ∃ o, fsubKvm.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPSubEq at hA
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fsubKvm_n0, show fsubKvm.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | rfl
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FSUB Dd, Dn, Dm` under `kvm` agrees with `exec` for every register number and
every state, where `A` satisfies `FPSubEq`. -/
theorem fsub_kvm (P : Platform) (A : Abstract) (hA : FPSubEq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fsubKvm
      (fpFields3 d n m) (.fsub d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fsubKvm, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fsubKvm.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fsubKvm_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fsubKvm_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fsubKvm_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FMUL Dd, Dn, Dm` under the profile `tcg`. -/
def fmulTcg : Footprint := isla_trace% "tests/isla/tcg/fmul"

isla_nodes fmulTcg

set_option maxRecDepth 100000 in
theorem fmulTcg_n0 : fmulTcg.trace = fmulTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmulTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmulTcg` ends in `exec`'s state. -/
theorem fmulTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPMulEq A) (hσ : fmulTcg.ctx σ u)
    (h : fmulTcg.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f64Mul (s.dregs n) (s.dregs m)) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPMulEq at hA
    unfold Footprint.Run at h
    rw [fmulTcg_n0, show fmulTcg.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmulTcg` has a path to an outcome. -/
theorem fmulTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPMulEq A) (hσ : fmulTcg.ctx σ u) :
    ∃ o, fmulTcg.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPMulEq at hA
    by_cases h0 : m.val / 2 % 16 = 1
    rotate_left
    by_cases h1 : m.val / 16 % 2 = 0
    by_cases h2 : m.val / 2 % 4 = 3
    rotate_left
    rotate_left
    rotate_left
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fmulTcg_n0, show fmulTcg.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | rfl
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMUL Dd, Dn, Dm` under `tcg` agrees with `exec` for every register number and
every state, where `A` satisfies `FPMulEq`. -/
theorem fmul_tcg (P : Platform) (A : Abstract) (hA : FPMulEq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fmulTcg
      (fpFields3 d n m) (.fmul d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmulTcg, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmulTcg.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fmulTcg_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fmulTcg_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fmulTcg_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FMUL Dd, Dn, Dm` under the profile `kvm`. -/
def fmulKvm : Footprint := isla_trace% "tests/isla/kvm/fmul"

isla_nodes fmulKvm

set_option maxRecDepth 100000 in
theorem fmulKvm_n0 : fmulKvm.trace = fmulKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmulKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmulKvm` ends in `exec`'s state. -/
theorem fmulKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPMulEq A) (hσ : fmulKvm.ctx σ u)
    (h : fmulKvm.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f64Mul (s.dregs n) (s.dregs m)) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPMulEq at hA
    unfold Footprint.Run at h
    rw [fmulKvm_n0, show fmulKvm.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmulKvm` has a path to an outcome. -/
theorem fmulKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPMulEq A) (hσ : fmulKvm.ctx σ u) :
    ∃ o, fmulKvm.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPMulEq at hA
    by_cases h0 : m.val / 2 % 16 = 1
    rotate_left
    by_cases h1 : m.val / 16 % 2 = 0
    by_cases h2 : m.val / 2 % 4 = 3
    rotate_left
    rotate_left
    rotate_left
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fmulKvm_n0, show fmulKvm.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | rfl
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMUL Dd, Dn, Dm` under `kvm` agrees with `exec` for every register number and
every state, where `A` satisfies `FPMulEq`. -/
theorem fmul_kvm (P : Platform) (A : Abstract) (hA : FPMulEq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fmulKvm
      (fpFields3 d n m) (.fmul d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmulKvm, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmulKvm.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fmulKvm_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fmulKvm_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fmulKvm_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FDIV Dd, Dn, Dm` under the profile `tcg`. -/
def fdivTcg : Footprint := isla_trace% "tests/isla/tcg/fdiv"

isla_nodes fdivTcg

set_option maxRecDepth 100000 in
theorem fdivTcg_n0 : fdivTcg.trace = fdivTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fdivTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fdivTcg` ends in `exec`'s state. -/
theorem fdivTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPDivEq A) (hσ : fdivTcg.ctx σ u)
    (h : fdivTcg.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f64Div (s.dregs n) (s.dregs m)) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPDivEq at hA
    unfold Footprint.Run at h
    rw [fdivTcg_n0, show fdivTcg.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fdivTcg` has a path to an outcome. -/
theorem fdivTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPDivEq A) (hσ : fdivTcg.ctx σ u) :
    ∃ o, fdivTcg.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPDivEq at hA
    by_cases h0 : m.val / 2 % 16 = 1
    rotate_left
    by_cases h1 : m.val / 16 % 2 = 0
    by_cases h2 : m.val / 2 % 4 = 3
    rotate_left
    rotate_left
    rotate_left
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fdivTcg_n0, show fdivTcg.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | rfl
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FDIV Dd, Dn, Dm` under `tcg` agrees with `exec` for every register number and
every state, where `A` satisfies `FPDivEq`. -/
theorem fdiv_tcg (P : Platform) (A : Abstract) (hA : FPDivEq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fdivTcg
      (fpFields3 d n m) (.fdiv d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fdivTcg, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fdivTcg.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fdivTcg_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fdivTcg_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fdivTcg_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FDIV Dd, Dn, Dm` under the profile `kvm`. -/
def fdivKvm : Footprint := isla_trace% "tests/isla/kvm/fdiv"

isla_nodes fdivKvm

set_option maxRecDepth 100000 in
theorem fdivKvm_n0 : fdivKvm.trace = fdivKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fdivKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fdivKvm` ends in `exec`'s state. -/
theorem fdivKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPDivEq A) (hσ : fdivKvm.ctx σ u)
    (h : fdivKvm.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f64Div (s.dregs n) (s.dregs m)) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPDivEq at hA
    unfold Footprint.Run at h
    rw [fdivKvm_n0, show fdivKvm.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fdivKvm` has a path to an outcome. -/
theorem fdivKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPDivEq A) (hσ : fdivKvm.ctx σ u) :
    ∃ o, fdivKvm.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPDivEq at hA
    by_cases h0 : m.val / 2 % 16 = 1
    rotate_left
    by_cases h1 : m.val / 16 % 2 = 0
    by_cases h2 : m.val / 2 % 4 = 3
    rotate_left
    rotate_left
    rotate_left
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fdivKvm_n0, show fdivKvm.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | rfl
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FDIV Dd, Dn, Dm` under `kvm` agrees with `exec` for every register number and
every state, where `A` satisfies `FPDivEq`. -/
theorem fdiv_kvm (P : Platform) (A : Abstract) (hA : FPDivEq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fdivKvm
      (fpFields3 d n m) (.fdiv d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fdivKvm, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fdivKvm.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fdivKvm_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fdivKvm_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fdivKvm_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FSQRT Dd, Dn` under the profile `tcg`. -/
def fsqrtTcg : Footprint := isla_trace% "tests/isla/tcg/fsqrt"

isla_nodes fsqrtTcg

set_option maxRecDepth 100000 in
theorem fsqrtTcg_n0 : fsqrtTcg.trace = fsqrtTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fsqrtTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fsqrtTcg` ends in `exec`'s state. -/
theorem fsqrtTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPSqrtEq A) (hσ : fsqrtTcg.ctx σ u)
    (h : fsqrtTcg.Run P (fpFields2 d n) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f64Sqrt (s.dregs n)) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPSqrtEq at hA
    unfold Footprint.Run at h
    rw [fsqrtTcg_n0, show fsqrtTcg.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fsqrtTcg` has a path to an outcome. -/
theorem fsqrtTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPSqrtEq A) (hσ : fsqrtTcg.ctx σ u) :
    ∃ o, fsqrtTcg.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPSqrtEq at hA
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fsqrtTcg_n0, show fsqrtTcg.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | rfl
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FSQRT Dd, Dn` under `tcg` agrees with `exec` for every register number and
every state, where `A` satisfies `FPSqrtEq`. -/
theorem fsqrt_tcg (P : Platform) (A : Abstract) (hA : FPSqrtEq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fsqrtTcg
      (fpFields2 d n) (.fsqrt d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fsqrtTcg, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fsqrtTcg.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fsqrtTcg_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fsqrtTcg_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fsqrtTcg_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FSQRT Dd, Dn` under the profile `kvm`. -/
def fsqrtKvm : Footprint := isla_trace% "tests/isla/kvm/fsqrt"

isla_nodes fsqrtKvm

set_option maxRecDepth 100000 in
theorem fsqrtKvm_n0 : fsqrtKvm.trace = fsqrtKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fsqrtKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fsqrtKvm` ends in `exec`'s state. -/
theorem fsqrtKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPSqrtEq A) (hσ : fsqrtKvm.ctx σ u)
    (h : fsqrtKvm.Run P (fpFields2 d n) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f64Sqrt (s.dregs n)) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPSqrtEq at hA
    unfold Footprint.Run at h
    rw [fsqrtKvm_n0, show fsqrtKvm.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fsqrtKvm` has a path to an outcome. -/
theorem fsqrtKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPSqrtEq A) (hσ : fsqrtKvm.ctx σ u) :
    ∃ o, fsqrtKvm.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPSqrtEq at hA
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fsqrtKvm_n0, show fsqrtKvm.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | rfl
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FSQRT Dd, Dn` under `kvm` agrees with `exec` for every register number and
every state, where `A` satisfies `FPSqrtEq`. -/
theorem fsqrt_kvm (P : Platform) (A : Abstract) (hA : FPSqrtEq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fsqrtKvm
      (fpFields2 d n) (.fsqrt d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fsqrtKvm, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fsqrtKvm.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fsqrtKvm_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fsqrtKvm_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fsqrtKvm_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `UCVTF Dd, Xn` under the profile `tcg`. -/
def ucvtfTcg : Footprint := isla_trace% "tests/isla/tcg/ucvtf"

isla_nodes ucvtfTcg

set_option maxRecDepth 100000 in
theorem ucvtfTcg_n0 : ucvtfTcg.trace = ucvtfTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx ucvtfTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `ucvtfTcg` ends in `exec`'s state. -/
theorem ucvtfTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FixedToFPEq A) (hσ : ucvtfTcg.ctx σ u)
    (h : ucvtfTcg.Run P (fpFields2 d n) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f64ConvertI64U (s.x n)) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FixedToFPEq at hA
    have hA0 := hA 0
    simp only [UInt64.toNat_zero] at hA0
    unfold Footprint.Run at h
    rw [ucvtfTcg_n0, show ucvtfTcg.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hA0]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ucvtfTcg` has a path to an outcome. -/
theorem ucvtfTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FixedToFPEq A) (hσ : ucvtfTcg.ctx σ u) :
    ∃ o, ucvtfTcg.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FixedToFPEq at hA
    have hA0 := hA 0
    simp only [UInt64.toNat_zero] at hA0
    by_cases h0 : n.val = 31
    rotate_left
    rotate_left
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [ucvtfTcg_n0, show ucvtfTcg.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hA0]
    all_goals first
      | rfl
      | fp_side hσ [hA, hA0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `UCVTF Dd, Xn` under `tcg` agrees with `exec` for every register number and
every state, where `A` satisfies `FixedToFPEq`. -/
theorem ucvtf_tcg (P : Platform) (A : Abstract) (hA : FixedToFPEq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] ucvtfTcg
      (fpFields2 d n) (.ucvtf d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, ucvtfTcg, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := ucvtfTcg.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := ucvtfTcg_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := ucvtfTcg_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => ucvtfTcg_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `UCVTF Dd, Xn` under the profile `kvm`. -/
def ucvtfKvm : Footprint := isla_trace% "tests/isla/kvm/ucvtf"

isla_nodes ucvtfKvm

set_option maxRecDepth 100000 in
theorem ucvtfKvm_n0 : ucvtfKvm.trace = ucvtfKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx ucvtfKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `ucvtfKvm` ends in `exec`'s state. -/
theorem ucvtfKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FixedToFPEq A) (hσ : ucvtfKvm.ctx σ u)
    (h : ucvtfKvm.Run P (fpFields2 d n) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f64ConvertI64U (s.x n)) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FixedToFPEq at hA
    have hA0 := hA 0
    simp only [UInt64.toNat_zero] at hA0
    unfold Footprint.Run at h
    rw [ucvtfKvm_n0, show ucvtfKvm.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hA0]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ucvtfKvm` has a path to an outcome. -/
theorem ucvtfKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FixedToFPEq A) (hσ : ucvtfKvm.ctx σ u) :
    ∃ o, ucvtfKvm.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FixedToFPEq at hA
    have hA0 := hA 0
    simp only [UInt64.toNat_zero] at hA0
    by_cases h0 : n.val = 31
    rotate_left
    rotate_left
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [ucvtfKvm_n0, show ucvtfKvm.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hA0]
    all_goals first
      | rfl
      | fp_side hσ [hA, hA0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `UCVTF Dd, Xn` under `kvm` agrees with `exec` for every register number and
every state, where `A` satisfies `FixedToFPEq`. -/
theorem ucvtf_kvm (P : Platform) (A : Abstract) (hA : FixedToFPEq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] ucvtfKvm
      (fpFields2 d n) (.ucvtf d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, ucvtfKvm, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := ucvtfKvm.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := ucvtfKvm_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := ucvtfKvm_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => ucvtfKvm_fwd hA hc h⟩

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.fmovXd_tcg
#print axioms TestSupport.A64.Isla.fmovXd_kvm
#print axioms TestSupport.A64.Isla.fmovDx_tcg
#print axioms TestSupport.A64.Isla.fmovDx_kvm
#print axioms TestSupport.A64.Isla.fadd_tcg
#print axioms TestSupport.A64.Isla.fadd_kvm
#print axioms TestSupport.A64.Isla.fsub_tcg
#print axioms TestSupport.A64.Isla.fsub_kvm
#print axioms TestSupport.A64.Isla.fmul_tcg
#print axioms TestSupport.A64.Isla.fmul_kvm
#print axioms TestSupport.A64.Isla.fdiv_tcg
#print axioms TestSupport.A64.Isla.fdiv_kvm
#print axioms TestSupport.A64.Isla.fsqrt_tcg
#print axioms TestSupport.A64.Isla.fsqrt_kvm
#print axioms TestSupport.A64.Isla.ucvtf_tcg
#print axioms TestSupport.A64.Isla.ucvtf_kvm
