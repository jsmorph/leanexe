import LeanExe.A64.Isla.Float

/-!
The theorems of `tests/TestSupport/A64/Isla/Float.lean` under the profile `sme`, from the traces of
`tests/isla/sme`: the forms of `kvm` on a processor that implements FEAT_SME and FEAT_SME_FA64,
with `PSTATE.SM`, `SMCR_EL1`, and `SMCR_EL2` unknown and the settings that Linux's boot protocol
requires of such a processor.  Each trace branches on `PSTATE.SM` in `IsMerging` and in the vector
length of `V_set`, and, in Streaming SVE mode, on the FA64 bits of `SMCR_EL1` and `SMCR_EL2` in
`IsFullA64Enabled`.  Each theorem states that every branch ends in `exec`'s state, so the model's
meaning of the form holds for either value of `PSTATE.SM` and of those bits.  The backward lemma
splits on them besides the fields.  `tests/isla/theorems.sh` elaborates the module and prints the
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
/-- The footprint of `FMOV Xd, Dn` under the profile `sme`. -/
def fmovXdSme : Footprint := isla_trace% "tests/isla/sme/fmov-xd"

isla_nodes fmovXdSme

set_option maxRecDepth 100000 in
theorem fmovXdSme_n0 : fmovXdSme.trace = fmovXdSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmovXdSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmovXdSme` ends in `exec`'s state. -/
theorem fmovXdSme_fwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hσ : fmovXdSme.ctx σ u)
    (h : fmovXdSme.Run P (fpFields2 d n) s σ o) :
    o = .done { s.setX d (s.dregs n) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 295)) := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold Footprint.Run at h
    rw [fmovXdSme_n0, show fmovXdSme.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ]
    all_goals xreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmovXdSme` has a path to an outcome. -/
theorem fmovXdSme_bwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hσ : fmovXdSme.ctx σ u) :
    fmovXdSme.Run P (fpFields2 d n) s σ (.done { s.setX d (s.dregs n) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 295))) := by
  without_info
    have := d.isLt
    have := n.isLt
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
      rw [fmovXdSme_n0, show fmovXdSme.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ]
    all_goals first
      | (apply Eq.symm; xreg_end; done)
      | fp_side hσ []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMOV Xd, Dn` under `sme` agrees with `exec` for every register number and
every state. -/
theorem fmovXd_sme (P : Platform) 
    (u : Unknown) (d n : Fin 32) (s : State) :
    Agrees P (sme.sys .fp u) ["SEE", "__BranchTaken"] fmovXdSme
      (fpFields2 d n) (.fmovXD d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmovXdSme, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmovXdSme.ctx_of σ u hσ
      exact ⟨_, fun o => ⟨fun h => fmovXdSme_fwd hc h, fun h => h ▸ fmovXdSme_bwd hc⟩,
        by frame_end⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FMOV Dd, Xn` under the profile `sme`. -/
def fmovDxSme : Footprint := isla_trace% "tests/isla/sme/fmov-dx"

isla_nodes fmovDxSme

set_option maxRecDepth 100000 in
theorem fmovDxSme_n0 : fmovDxSme.trace = fmovDxSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmovDxSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmovDxSme` ends in `exec`'s state. -/
theorem fmovDxSme_fwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hσ : fmovDxSme.ctx σ u)
    (h : fmovDxSme.Run P (fpFields2 d n) s σ o) :
    ∃ σ', o = .done
      { s.setD d (s.x n) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold Footprint.Run at h
    rw [fmovDxSme_n0, show fmovDxSme.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmovDxSme` has a path to an outcome. -/
theorem fmovDxSme_bwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hσ : fmovDxSme.ctx σ u) :
    ∃ o, fmovDxSme.Run P (fpFields2 d n) s σ o := by
  without_info
    have := d.isLt
    have := n.isLt
    by_cases h0 : n.val = 31
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
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fmovDxSme_n0, show fmovDxSme.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ]
    all_goals first
      | rfl
      | fp_side hσ []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMOV Dd, Xn` under `sme` agrees with `exec` for every register number and
every state. -/
theorem fmovDx_sme (P : Platform) 
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P noAbstract (sme.sys .fp u) ["SEE", "__BranchTaken", "_Z"] fmovDxSme
      (fpFields2 d n) (.fmovDX d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmovDxSme, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmovDxSme.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fmovDxSme_bwd (P := P) (d := d) (n := n) (s := s) hc
      obtain ⟨σ', rfl, -⟩ := fmovDxSme_fwd hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fmovDxSme_fwd hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FADD Dd, Dn, Dm` under the profile `sme`. -/
def faddSme : Footprint := isla_trace% "tests/isla/sme/fadd"

isla_nodes faddSme

set_option maxRecDepth 100000 in
theorem faddSme_n0 : faddSme.trace = faddSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx faddSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `faddSme` ends in `exec`'s state. -/
theorem faddSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPAddEq A) (hσ : faddSme.ctx σ u)
    (h : faddSme.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f64Add (s.dregs n) (s.dregs m)) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPAddEq at hA
    unfold Footprint.Run at h
    rw [faddSme_n0, show faddSme.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `faddSme` has a path to an outcome. -/
theorem faddSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPAddEq A) (hσ : faddSme.ctx σ u) :
    ∃ o, faddSme.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPAddEq at hA
    by_cases h0 : u.sm.toNat = 1
    by_cases h1 : u.smcr1.toNat / 2147483648 % 2 = 0
    rotate_left
    by_cases h2 : u.smcr2.toNat / 2147483648 % 2 = 0
    rotate_left
    rotate_left
    rotate_left
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [faddSme_n0, show faddSme.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | rfl
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FADD Dd, Dn, Dm` under `sme` agrees with `exec` for every register number and
every state, where `A` satisfies `FPAddEq`. -/
theorem fadd_sme (P : Platform) (A : Abstract) (hA : FPAddEq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] faddSme
      (fpFields3 d n m) (.fadd d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, faddSme, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := faddSme.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := faddSme_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := faddSme_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => faddSme_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FSUB Dd, Dn, Dm` under the profile `sme`. -/
def fsubSme : Footprint := isla_trace% "tests/isla/sme/fsub"

isla_nodes fsubSme

set_option maxRecDepth 100000 in
theorem fsubSme_n0 : fsubSme.trace = fsubSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fsubSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fsubSme` ends in `exec`'s state. -/
theorem fsubSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPSubEq A) (hσ : fsubSme.ctx σ u)
    (h : fsubSme.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f64Sub (s.dregs n) (s.dregs m)) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPSubEq at hA
    unfold Footprint.Run at h
    rw [fsubSme_n0, show fsubSme.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fsubSme` has a path to an outcome. -/
theorem fsubSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPSubEq A) (hσ : fsubSme.ctx σ u) :
    ∃ o, fsubSme.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPSubEq at hA
    by_cases h0 : u.sm.toNat = 1
    by_cases h1 : u.smcr1.toNat / 2147483648 % 2 = 0
    rotate_left
    by_cases h2 : u.smcr2.toNat / 2147483648 % 2 = 0
    rotate_left
    rotate_left
    rotate_left
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fsubSme_n0, show fsubSme.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | rfl
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FSUB Dd, Dn, Dm` under `sme` agrees with `exec` for every register number and
every state, where `A` satisfies `FPSubEq`. -/
theorem fsub_sme (P : Platform) (A : Abstract) (hA : FPSubEq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fsubSme
      (fpFields3 d n m) (.fsub d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fsubSme, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fsubSme.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fsubSme_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fsubSme_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fsubSme_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FMUL Dd, Dn, Dm` under the profile `sme`. -/
def fmulSme : Footprint := isla_trace% "tests/isla/sme/fmul"

isla_nodes fmulSme

set_option maxRecDepth 100000 in
theorem fmulSme_n0 : fmulSme.trace = fmulSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmulSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmulSme` ends in `exec`'s state. -/
theorem fmulSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPMulEq A) (hσ : fmulSme.ctx σ u)
    (h : fmulSme.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f64Mul (s.dregs n) (s.dregs m)) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPMulEq at hA
    unfold Footprint.Run at h
    rw [fmulSme_n0, show fmulSme.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmulSme` has a path to an outcome. -/
theorem fmulSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPMulEq A) (hσ : fmulSme.ctx σ u) :
    ∃ o, fmulSme.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPMulEq at hA
    by_cases h0 : m.val / 2 % 16 = 1
    by_cases h1 : u.sm.toNat = 1
    by_cases h2 : u.smcr1.toNat / 2147483648 % 2 = 0
    rotate_left
    by_cases h3 : u.smcr2.toNat / 2147483648 % 2 = 0
    rotate_left
    rotate_left
    rotate_left
    by_cases h4 : m.val / 16 % 2 = 0
    by_cases h5 : m.val / 2 % 4 = 3
    by_cases h6 : u.sm.toNat = 1
    by_cases h7 : u.smcr1.toNat / 2147483648 % 2 = 0
    rotate_left
    by_cases h8 : u.smcr2.toNat / 2147483648 % 2 = 0
    rotate_left
    rotate_left
    rotate_left
    by_cases h9 : u.sm.toNat = 1
    by_cases h10 : u.smcr1.toNat / 2147483648 % 2 = 0
    rotate_left
    by_cases h11 : u.smcr2.toNat / 2147483648 % 2 = 0
    rotate_left
    rotate_left
    rotate_left
    by_cases h12 : u.sm.toNat = 1
    by_cases h13 : u.smcr1.toNat / 2147483648 % 2 = 0
    rotate_left
    by_cases h14 : u.smcr2.toNat / 2147483648 % 2 = 0
    rotate_left
    rotate_left
    rotate_left
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fmulSme_n0, show fmulSme.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | rfl
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMUL Dd, Dn, Dm` under `sme` agrees with `exec` for every register number and
every state, where `A` satisfies `FPMulEq`. -/
theorem fmul_sme (P : Platform) (A : Abstract) (hA : FPMulEq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fmulSme
      (fpFields3 d n m) (.fmul d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmulSme, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmulSme.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fmulSme_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fmulSme_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fmulSme_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FDIV Dd, Dn, Dm` under the profile `sme`. -/
def fdivSme : Footprint := isla_trace% "tests/isla/sme/fdiv"

isla_nodes fdivSme

set_option maxRecDepth 100000 in
theorem fdivSme_n0 : fdivSme.trace = fdivSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fdivSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fdivSme` ends in `exec`'s state. -/
theorem fdivSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPDivEq A) (hσ : fdivSme.ctx σ u)
    (h : fdivSme.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f64Div (s.dregs n) (s.dregs m)) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPDivEq at hA
    unfold Footprint.Run at h
    rw [fdivSme_n0, show fdivSme.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fdivSme` has a path to an outcome. -/
theorem fdivSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPDivEq A) (hσ : fdivSme.ctx σ u) :
    ∃ o, fdivSme.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPDivEq at hA
    by_cases h0 : m.val / 2 % 16 = 1
    by_cases h1 : u.sm.toNat = 1
    by_cases h2 : u.smcr1.toNat / 2147483648 % 2 = 0
    rotate_left
    by_cases h3 : u.smcr2.toNat / 2147483648 % 2 = 0
    rotate_left
    rotate_left
    rotate_left
    by_cases h4 : m.val / 16 % 2 = 0
    by_cases h5 : m.val / 2 % 4 = 3
    by_cases h6 : u.sm.toNat = 1
    by_cases h7 : u.smcr1.toNat / 2147483648 % 2 = 0
    rotate_left
    by_cases h8 : u.smcr2.toNat / 2147483648 % 2 = 0
    rotate_left
    rotate_left
    rotate_left
    by_cases h9 : u.sm.toNat = 1
    by_cases h10 : u.smcr1.toNat / 2147483648 % 2 = 0
    rotate_left
    by_cases h11 : u.smcr2.toNat / 2147483648 % 2 = 0
    rotate_left
    rotate_left
    rotate_left
    by_cases h12 : u.sm.toNat = 1
    by_cases h13 : u.smcr1.toNat / 2147483648 % 2 = 0
    rotate_left
    by_cases h14 : u.smcr2.toNat / 2147483648 % 2 = 0
    rotate_left
    rotate_left
    rotate_left
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fdivSme_n0, show fdivSme.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | rfl
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FDIV Dd, Dn, Dm` under `sme` agrees with `exec` for every register number and
every state, where `A` satisfies `FPDivEq`. -/
theorem fdiv_sme (P : Platform) (A : Abstract) (hA : FPDivEq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fdivSme
      (fpFields3 d n m) (.fdiv d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fdivSme, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fdivSme.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fdivSme_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fdivSme_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fdivSme_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FSQRT Dd, Dn` under the profile `sme`. -/
def fsqrtSme : Footprint := isla_trace% "tests/isla/sme/fsqrt"

isla_nodes fsqrtSme

set_option maxRecDepth 100000 in
theorem fsqrtSme_n0 : fsqrtSme.trace = fsqrtSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fsqrtSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fsqrtSme` ends in `exec`'s state. -/
theorem fsqrtSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPSqrtEq A) (hσ : fsqrtSme.ctx σ u)
    (h : fsqrtSme.Run P (fpFields2 d n) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f64Sqrt (s.dregs n)) with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPSqrtEq at hA
    unfold Footprint.Run at h
    rw [fsqrtSme_n0, show fsqrtSme.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fsqrtSme` has a path to an outcome. -/
theorem fsqrtSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPSqrtEq A) (hσ : fsqrtSme.ctx σ u) :
    ∃ o, fsqrtSme.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPSqrtEq at hA
    by_cases h0 : u.sm.toNat = 1
    by_cases h1 : u.smcr1.toNat / 2147483648 % 2 = 0
    rotate_left
    by_cases h2 : u.smcr2.toNat / 2147483648 % 2 = 0
    rotate_left
    rotate_left
    rotate_left
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fsqrtSme_n0, show fsqrtSme.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA]
    all_goals first
      | rfl
      | fp_side hσ [hA]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FSQRT Dd, Dn` under `sme` agrees with `exec` for every register number and
every state, where `A` satisfies `FPSqrtEq`. -/
theorem fsqrt_sme (P : Platform) (A : Abstract) (hA : FPSqrtEq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fsqrtSme
      (fpFields2 d n) (.fsqrt d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fsqrtSme, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fsqrtSme.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fsqrtSme_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fsqrtSme_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fsqrtSme_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `UCVTF Dd, Xn` under the profile `sme`. -/
def ucvtfSme : Footprint := isla_trace% "tests/isla/sme/ucvtf"

isla_nodes ucvtfSme

set_option maxRecDepth 100000 in
theorem ucvtfSme_n0 : ucvtfSme.trace = ucvtfSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx ucvtfSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `ucvtfSme` ends in `exec`'s state. -/
theorem ucvtfSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FixedToFPEq A) (hσ : ucvtfSme.ctx σ u)
    (h : ucvtfSme.Run P (fpFields2 d n) s σ o A) :
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
    rw [ucvtfSme_n0, show ucvtfSme.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hA0]
    all_goals dreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ucvtfSme` has a path to an outcome. -/
theorem ucvtfSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FixedToFPEq A) (hσ : ucvtfSme.ctx σ u) :
    ∃ o, ucvtfSme.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FixedToFPEq at hA
    have hA0 := hA 0
    simp only [UInt64.toNat_zero] at hA0
    by_cases h0 : n.val = 31
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
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [ucvtfSme_n0, show ucvtfSme.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hA0]
    all_goals first
      | rfl
      | fp_side hσ [hA, hA0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `UCVTF Dd, Xn` under `sme` agrees with `exec` for every register number and
every state, where `A` satisfies `FixedToFPEq`. -/
theorem ucvtf_sme (P : Platform) (A : Abstract) (hA : FixedToFPEq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] ucvtfSme
      (fpFields2 d n) (.ucvtf d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, ucvtfSme, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := ucvtfSme.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := ucvtfSme_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := ucvtfSme_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => ucvtfSme_fwd hA hc h⟩

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.fmovXd_sme
#print axioms TestSupport.A64.Isla.fmovDx_sme
#print axioms TestSupport.A64.Isla.fadd_sme
#print axioms TestSupport.A64.Isla.fsub_sme
#print axioms TestSupport.A64.Isla.fmul_sme
#print axioms TestSupport.A64.Isla.fdiv_sme
#print axioms TestSupport.A64.Isla.fsqrt_sme
#print axioms TestSupport.A64.Isla.ucvtf_sme
