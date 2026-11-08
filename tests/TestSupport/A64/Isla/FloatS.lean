import LeanExe.A64.Isla.Float

/-!
Theorems of `AgreesAll`, or of `Agrees` for `FMOV Wd, Sn`, for the single-precision forms of
`LeanExe/A64/Machine.lean`, from the traces of `tests/isla/tcg` and `tests/isla/kvm` under the profiles
`tcg` and `kvm` with the arguments `fp` of `tests/isla/traces.sh`.  Each theorem holds for every value
of every register field, register 31 included, and every state.  A form reads the low 32 bits of
its D registers, which the traces extract from the elements of `_Z`, and writes its result
zero-extended, so the walks add `low32_eq` and `ofNat_u32` to the rules of
`LeanExe/A64/Isla/Float.lean`.  `FMOV Sd, Wn`, `UCVTF Sd, Xn`, and `SCVTF Sd, Wn` write the D
register with a width of 32 bits, and their walks add `rwchain_eq`, `ofNat_and32_or`, and
`ofNat_and32`.  The arithmetic forms, `FRINTN`, the conversions, and `FCMP` call an
abstract 32-bit wrapper of Arm's function, or `FPCompare` itself, and their theorems take its
equation as a hypothesis on the meanings `A` and list FPSR among the changed registers.  The forms
that write a D register leave `V_set`'s choice above bit 127, so their theorems list `_Z`, and
`FMOV Wd`, `FCVTZU`, `FCVTZS`, and `FCMP` have one outcome.  The case splits of each backward
lemma follow the conditions on the fields that the trace tests, which are those of the
double-precision form of the same shape.  `tests/isla/theorems.sh` elaborates the module and
prints the axioms of its theorems.
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
/-- The footprint of `FMOV Sd, Wn` under the profile `tcg`. -/
def fmovSwTcg : Footprint := isla_trace% "tests/isla/tcg/fmov-sw"

isla_nodes fmovSwTcg

set_option maxRecDepth 100000 in
theorem fmovSwTcg_n0 : fmovSwTcg.trace = fmovSwTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmovSwTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmovSwTcg` ends in `exec`'s state. -/
theorem fmovSwTcg_fwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hσ : fmovSwTcg.ctx σ u)
    (h : fmovSwTcg.Run P (fpFields2 d n) s σ o) :
    ∃ σ', o = .done
      { s.setD d (s.x n).toUInt32.toUInt64 with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold Footprint.Run at h
    rw [fmovSwTcg_n0, show fmovSwTcg.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmovSwTcg` has a path to an outcome. -/
theorem fmovSwTcg_bwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hσ : fmovSwTcg.ctx σ u) :
    ∃ o, fmovSwTcg.Run P (fpFields2 d n) s σ o := by
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
      rw [fmovSwTcg_n0, show fmovSwTcg.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals first
      | rfl
      | fp_side hσ [hi_lo_mod32, low32_eq, u32_mod, schain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMOV Sd, Wn` under `tcg` agrees with `exec` for every register number and every
state. -/
theorem fmovSw_tcg (P : Platform)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P noAbstract (tcg.sys .fp u) ["SEE", "__BranchTaken", "_Z"] fmovSwTcg
      (fpFields2 d n) (.fmovSW d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmovSwTcg, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmovSwTcg.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fmovSwTcg_bwd (P := P) (d := d) (n := n) (s := s) hc
      obtain ⟨σ', rfl, -⟩ := fmovSwTcg_fwd hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fmovSwTcg_fwd hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FMOV Sd, Wn` under the profile `kvm`. -/
def fmovSwKvm : Footprint := isla_trace% "tests/isla/kvm/fmov-sw"

isla_nodes fmovSwKvm

set_option maxRecDepth 100000 in
theorem fmovSwKvm_n0 : fmovSwKvm.trace = fmovSwKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmovSwKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmovSwKvm` ends in `exec`'s state. -/
theorem fmovSwKvm_fwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hσ : fmovSwKvm.ctx σ u)
    (h : fmovSwKvm.Run P (fpFields2 d n) s σ o) :
    ∃ σ', o = .done
      { s.setD d (s.x n).toUInt32.toUInt64 with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold Footprint.Run at h
    rw [fmovSwKvm_n0, show fmovSwKvm.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmovSwKvm` has a path to an outcome. -/
theorem fmovSwKvm_bwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hσ : fmovSwKvm.ctx σ u) :
    ∃ o, fmovSwKvm.Run P (fpFields2 d n) s σ o := by
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
      rw [fmovSwKvm_n0, show fmovSwKvm.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals first
      | rfl
      | fp_side hσ [hi_lo_mod32, low32_eq, u32_mod, schain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMOV Sd, Wn` under `kvm` agrees with `exec` for every register number and every
state. -/
theorem fmovSw_kvm (P : Platform)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P noAbstract (kvm.sys .fp u) ["SEE", "__BranchTaken", "_Z"] fmovSwKvm
      (fpFields2 d n) (.fmovSW d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmovSwKvm, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmovSwKvm.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fmovSwKvm_bwd (P := P) (d := d) (n := n) (s := s) hc
      obtain ⟨σ', rfl, -⟩ := fmovSwKvm_fwd hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fmovSwKvm_fwd hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FMOV Wd, Sn` under the profile `tcg`. -/
def fmovWsTcg : Footprint := isla_trace% "tests/isla/tcg/fmov-ws"

isla_nodes fmovWsTcg

set_option maxRecDepth 100000 in
theorem fmovWsTcg_n0 : fmovWsTcg.trace = fmovWsTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmovWsTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmovWsTcg` ends in `exec`'s state. -/
theorem fmovWsTcg_fwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hσ : fmovWsTcg.ctx σ u)
    (h : fmovWsTcg.Run P (fpFields2 d n) s σ o) :
    o = .done { s.setX d (s.dregs n).toUInt32.toUInt64 with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 295)) := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold Footprint.Run at h
    rw [fmovWsTcg_n0, show fmovWsTcg.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals wreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmovWsTcg` has a path to `exec`'s state. -/
theorem fmovWsTcg_bwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hσ : fmovWsTcg.ctx σ u) :
    fmovWsTcg.Run P (fpFields2 d n) s σ
      (.done { s.setX d (s.dregs n).toUInt32.toUInt64 with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 295))) := by
  without_info
    have := d.isLt
    have := n.isLt
    by_cases h0 : d.val = 31
    rotate_left
    rotate_left
    all_goals
      unfold Footprint.Run
      rw [fmovWsTcg_n0, show fmovWsTcg.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | (apply Eq.symm; wreg_end; done)
      | fp_side hσ [hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMOV Wd, Sn` under `tcg` agrees with `exec` for every register number and every
state. -/
theorem fmovWs_tcg (P : Platform) (u : Unknown) (d n : Fin 32) (s : State) :
    Agrees P (tcg.sys .fp u) ["SEE", "__BranchTaken"] fmovWsTcg (fpFields2 d n) (.fmovWS d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmovWsTcg, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmovWsTcg.ctx_of σ u hσ
      exact ⟨_, fun o => ⟨fun h => fmovWsTcg_fwd hc h, fun h => h ▸ fmovWsTcg_bwd hc⟩, by frame_end⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FMOV Wd, Sn` under the profile `kvm`. -/
def fmovWsKvm : Footprint := isla_trace% "tests/isla/kvm/fmov-ws"

isla_nodes fmovWsKvm

set_option maxRecDepth 100000 in
theorem fmovWsKvm_n0 : fmovWsKvm.trace = fmovWsKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmovWsKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmovWsKvm` ends in `exec`'s state. -/
theorem fmovWsKvm_fwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hσ : fmovWsKvm.ctx σ u)
    (h : fmovWsKvm.Run P (fpFields2 d n) s σ o) :
    o = .done { s.setX d (s.dregs n).toUInt32.toUInt64 with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 295)) := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold Footprint.Run at h
    rw [fmovWsKvm_n0, show fmovWsKvm.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals wreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmovWsKvm` has a path to `exec`'s state. -/
theorem fmovWsKvm_bwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hσ : fmovWsKvm.ctx σ u) :
    fmovWsKvm.Run P (fpFields2 d n) s σ
      (.done { s.setX d (s.dregs n).toUInt32.toUInt64 with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 295))) := by
  without_info
    have := d.isLt
    have := n.isLt
    by_cases h0 : d.val = 31
    rotate_left
    rotate_left
    all_goals
      unfold Footprint.Run
      rw [fmovWsKvm_n0, show fmovWsKvm.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | (apply Eq.symm; wreg_end; done)
      | fp_side hσ [hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMOV Wd, Sn` under `kvm` agrees with `exec` for every register number and every
state. -/
theorem fmovWs_kvm (P : Platform) (u : Unknown) (d n : Fin 32) (s : State) :
    Agrees P (kvm.sys .fp u) ["SEE", "__BranchTaken"] fmovWsKvm (fpFields2 d n) (.fmovWS d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmovWsKvm, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmovWsKvm.ctx_of σ u hσ
      exact ⟨_, fun o => ⟨fun h => fmovWsKvm_fwd hc h, fun h => h ▸ fmovWsKvm_bwd hc⟩, by frame_end⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FADD Sd, Sn, Sm` under the profile `tcg`. -/
def faddSTcg : Footprint := isla_trace% "tests/isla/tcg/fadd-s"

isla_nodes faddSTcg

set_option maxRecDepth 100000 in
theorem faddSTcg_n0 : faddSTcg.trace = faddSTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx faddSTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `faddSTcg` ends in `exec`'s state. -/
theorem faddSTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPAdd32Eq A) (hσ : faddSTcg.ctx σ u)
    (h : faddSTcg.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32Add (s.dregs n).toUInt32 (s.dregs m).toUInt32).toUInt64 with
        pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPAdd32Eq at hA
    unfold Footprint.Run at h
    rw [faddSTcg_n0, show faddSTcg.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `faddSTcg` has a path to an outcome. -/
theorem faddSTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPAdd32Eq A) (hσ : faddSTcg.ctx σ u) :
    ∃ o, faddSTcg.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPAdd32Eq at hA
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [faddSTcg_n0, show faddSTcg.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FADD Sd, Sn, Sm` under `tcg` agrees with `exec` for every register number and every
state, where `A` satisfies `FPAdd32Eq`. -/
theorem faddS_tcg (P : Platform) (A : Abstract) (hA : FPAdd32Eq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] faddSTcg
      (fpFields3 d n m) (.faddS d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, faddSTcg, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := faddSTcg.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := faddSTcg_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := faddSTcg_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => faddSTcg_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FADD Sd, Sn, Sm` under the profile `kvm`. -/
def faddSKvm : Footprint := isla_trace% "tests/isla/kvm/fadd-s"

isla_nodes faddSKvm

set_option maxRecDepth 100000 in
theorem faddSKvm_n0 : faddSKvm.trace = faddSKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx faddSKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `faddSKvm` ends in `exec`'s state. -/
theorem faddSKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPAdd32Eq A) (hσ : faddSKvm.ctx σ u)
    (h : faddSKvm.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32Add (s.dregs n).toUInt32 (s.dregs m).toUInt32).toUInt64 with
        pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPAdd32Eq at hA
    unfold Footprint.Run at h
    rw [faddSKvm_n0, show faddSKvm.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `faddSKvm` has a path to an outcome. -/
theorem faddSKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPAdd32Eq A) (hσ : faddSKvm.ctx σ u) :
    ∃ o, faddSKvm.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPAdd32Eq at hA
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [faddSKvm_n0, show faddSKvm.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FADD Sd, Sn, Sm` under `kvm` agrees with `exec` for every register number and every
state, where `A` satisfies `FPAdd32Eq`. -/
theorem faddS_kvm (P : Platform) (A : Abstract) (hA : FPAdd32Eq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] faddSKvm
      (fpFields3 d n m) (.faddS d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, faddSKvm, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := faddSKvm.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := faddSKvm_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := faddSKvm_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => faddSKvm_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FSUB Sd, Sn, Sm` under the profile `tcg`. -/
def fsubSTcg : Footprint := isla_trace% "tests/isla/tcg/fsub-s"

isla_nodes fsubSTcg

set_option maxRecDepth 100000 in
theorem fsubSTcg_n0 : fsubSTcg.trace = fsubSTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fsubSTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fsubSTcg` ends in `exec`'s state. -/
theorem fsubSTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPSub32Eq A) (hσ : fsubSTcg.ctx σ u)
    (h : fsubSTcg.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32Sub (s.dregs n).toUInt32 (s.dregs m).toUInt32).toUInt64 with
        pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPSub32Eq at hA
    unfold Footprint.Run at h
    rw [fsubSTcg_n0, show fsubSTcg.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fsubSTcg` has a path to an outcome. -/
theorem fsubSTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPSub32Eq A) (hσ : fsubSTcg.ctx σ u) :
    ∃ o, fsubSTcg.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPSub32Eq at hA
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fsubSTcg_n0, show fsubSTcg.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FSUB Sd, Sn, Sm` under `tcg` agrees with `exec` for every register number and every
state, where `A` satisfies `FPSub32Eq`. -/
theorem fsubS_tcg (P : Platform) (A : Abstract) (hA : FPSub32Eq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fsubSTcg
      (fpFields3 d n m) (.fsubS d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fsubSTcg, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fsubSTcg.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fsubSTcg_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fsubSTcg_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fsubSTcg_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FSUB Sd, Sn, Sm` under the profile `kvm`. -/
def fsubSKvm : Footprint := isla_trace% "tests/isla/kvm/fsub-s"

isla_nodes fsubSKvm

set_option maxRecDepth 100000 in
theorem fsubSKvm_n0 : fsubSKvm.trace = fsubSKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fsubSKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fsubSKvm` ends in `exec`'s state. -/
theorem fsubSKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPSub32Eq A) (hσ : fsubSKvm.ctx σ u)
    (h : fsubSKvm.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32Sub (s.dregs n).toUInt32 (s.dregs m).toUInt32).toUInt64 with
        pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPSub32Eq at hA
    unfold Footprint.Run at h
    rw [fsubSKvm_n0, show fsubSKvm.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fsubSKvm` has a path to an outcome. -/
theorem fsubSKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPSub32Eq A) (hσ : fsubSKvm.ctx σ u) :
    ∃ o, fsubSKvm.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPSub32Eq at hA
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fsubSKvm_n0, show fsubSKvm.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FSUB Sd, Sn, Sm` under `kvm` agrees with `exec` for every register number and every
state, where `A` satisfies `FPSub32Eq`. -/
theorem fsubS_kvm (P : Platform) (A : Abstract) (hA : FPSub32Eq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fsubSKvm
      (fpFields3 d n m) (.fsubS d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fsubSKvm, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fsubSKvm.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fsubSKvm_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fsubSKvm_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fsubSKvm_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FMUL Sd, Sn, Sm` under the profile `tcg`. -/
def fmulSTcg : Footprint := isla_trace% "tests/isla/tcg/fmul-s"

isla_nodes fmulSTcg

set_option maxRecDepth 100000 in
theorem fmulSTcg_n0 : fmulSTcg.trace = fmulSTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmulSTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmulSTcg` ends in `exec`'s state. -/
theorem fmulSTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPMul32Eq A) (hσ : fmulSTcg.ctx σ u)
    (h : fmulSTcg.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32Mul (s.dregs n).toUInt32 (s.dregs m).toUInt32).toUInt64 with
        pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPMul32Eq at hA
    unfold Footprint.Run at h
    rw [fmulSTcg_n0, show fmulSTcg.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmulSTcg` has a path to an outcome. -/
theorem fmulSTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPMul32Eq A) (hσ : fmulSTcg.ctx σ u) :
    ∃ o, fmulSTcg.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPMul32Eq at hA
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
      rw [fmulSTcg_n0, show fmulSTcg.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMUL Sd, Sn, Sm` under `tcg` agrees with `exec` for every register number and every
state, where `A` satisfies `FPMul32Eq`. -/
theorem fmulS_tcg (P : Platform) (A : Abstract) (hA : FPMul32Eq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fmulSTcg
      (fpFields3 d n m) (.fmulS d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmulSTcg, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmulSTcg.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fmulSTcg_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fmulSTcg_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fmulSTcg_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FMUL Sd, Sn, Sm` under the profile `kvm`. -/
def fmulSKvm : Footprint := isla_trace% "tests/isla/kvm/fmul-s"

isla_nodes fmulSKvm

set_option maxRecDepth 100000 in
theorem fmulSKvm_n0 : fmulSKvm.trace = fmulSKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmulSKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmulSKvm` ends in `exec`'s state. -/
theorem fmulSKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPMul32Eq A) (hσ : fmulSKvm.ctx σ u)
    (h : fmulSKvm.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32Mul (s.dregs n).toUInt32 (s.dregs m).toUInt32).toUInt64 with
        pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPMul32Eq at hA
    unfold Footprint.Run at h
    rw [fmulSKvm_n0, show fmulSKvm.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmulSKvm` has a path to an outcome. -/
theorem fmulSKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPMul32Eq A) (hσ : fmulSKvm.ctx σ u) :
    ∃ o, fmulSKvm.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPMul32Eq at hA
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
      rw [fmulSKvm_n0, show fmulSKvm.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMUL Sd, Sn, Sm` under `kvm` agrees with `exec` for every register number and every
state, where `A` satisfies `FPMul32Eq`. -/
theorem fmulS_kvm (P : Platform) (A : Abstract) (hA : FPMul32Eq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fmulSKvm
      (fpFields3 d n m) (.fmulS d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmulSKvm, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmulSKvm.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fmulSKvm_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fmulSKvm_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fmulSKvm_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FDIV Sd, Sn, Sm` under the profile `tcg`. -/
def fdivSTcg : Footprint := isla_trace% "tests/isla/tcg/fdiv-s"

isla_nodes fdivSTcg

set_option maxRecDepth 100000 in
theorem fdivSTcg_n0 : fdivSTcg.trace = fdivSTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fdivSTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fdivSTcg` ends in `exec`'s state. -/
theorem fdivSTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPDiv32Eq A) (hσ : fdivSTcg.ctx σ u)
    (h : fdivSTcg.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32Div (s.dregs n).toUInt32 (s.dregs m).toUInt32).toUInt64 with
        pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPDiv32Eq at hA
    unfold Footprint.Run at h
    rw [fdivSTcg_n0, show fdivSTcg.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fdivSTcg` has a path to an outcome. -/
theorem fdivSTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPDiv32Eq A) (hσ : fdivSTcg.ctx σ u) :
    ∃ o, fdivSTcg.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPDiv32Eq at hA
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
      rw [fdivSTcg_n0, show fdivSTcg.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FDIV Sd, Sn, Sm` under `tcg` agrees with `exec` for every register number and every
state, where `A` satisfies `FPDiv32Eq`. -/
theorem fdivS_tcg (P : Platform) (A : Abstract) (hA : FPDiv32Eq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fdivSTcg
      (fpFields3 d n m) (.fdivS d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fdivSTcg, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fdivSTcg.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fdivSTcg_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fdivSTcg_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fdivSTcg_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FDIV Sd, Sn, Sm` under the profile `kvm`. -/
def fdivSKvm : Footprint := isla_trace% "tests/isla/kvm/fdiv-s"

isla_nodes fdivSKvm

set_option maxRecDepth 100000 in
theorem fdivSKvm_n0 : fdivSKvm.trace = fdivSKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fdivSKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fdivSKvm` ends in `exec`'s state. -/
theorem fdivSKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPDiv32Eq A) (hσ : fdivSKvm.ctx σ u)
    (h : fdivSKvm.Run P (fpFields3 d n m) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32Div (s.dregs n).toUInt32 (s.dregs m).toUInt32).toUInt64 with
        pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPDiv32Eq at hA
    unfold Footprint.Run at h
    rw [fdivSKvm_n0, show fdivSKvm.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fdivSKvm` has a path to an outcome. -/
theorem fdivSKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPDiv32Eq A) (hσ : fdivSKvm.ctx σ u) :
    ∃ o, fdivSKvm.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPDiv32Eq at hA
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
      rw [fdivSKvm_n0, show fdivSKvm.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FDIV Sd, Sn, Sm` under `kvm` agrees with `exec` for every register number and every
state, where `A` satisfies `FPDiv32Eq`. -/
theorem fdivS_kvm (P : Platform) (A : Abstract) (hA : FPDiv32Eq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fdivSKvm
      (fpFields3 d n m) (.fdivS d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fdivSKvm, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fdivSKvm.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fdivSKvm_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fdivSKvm_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fdivSKvm_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FSQRT Sd, Sn` under the profile `tcg`. -/
def fsqrtSTcg : Footprint := isla_trace% "tests/isla/tcg/fsqrt-s"

isla_nodes fsqrtSTcg

set_option maxRecDepth 100000 in
theorem fsqrtSTcg_n0 : fsqrtSTcg.trace = fsqrtSTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fsqrtSTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fsqrtSTcg` ends in `exec`'s state. -/
theorem fsqrtSTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPSqrt32Eq A) (hσ : fsqrtSTcg.ctx σ u)
    (h : fsqrtSTcg.Run P (fpFields2 d n) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32Sqrt (s.dregs n).toUInt32).toUInt64 with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPSqrt32Eq at hA
    unfold Footprint.Run at h
    rw [fsqrtSTcg_n0, show fsqrtSTcg.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fsqrtSTcg` has a path to an outcome. -/
theorem fsqrtSTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPSqrt32Eq A) (hσ : fsqrtSTcg.ctx σ u) :
    ∃ o, fsqrtSTcg.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPSqrt32Eq at hA
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fsqrtSTcg_n0, show fsqrtSTcg.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FSQRT Sd, Sn` under `tcg` agrees with `exec` for every register number and every
state, where `A` satisfies `FPSqrt32Eq`. -/
theorem fsqrtS_tcg (P : Platform) (A : Abstract) (hA : FPSqrt32Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fsqrtSTcg
      (fpFields2 d n) (.fsqrtS d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fsqrtSTcg, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fsqrtSTcg.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fsqrtSTcg_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fsqrtSTcg_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fsqrtSTcg_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FSQRT Sd, Sn` under the profile `kvm`. -/
def fsqrtSKvm : Footprint := isla_trace% "tests/isla/kvm/fsqrt-s"

isla_nodes fsqrtSKvm

set_option maxRecDepth 100000 in
theorem fsqrtSKvm_n0 : fsqrtSKvm.trace = fsqrtSKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fsqrtSKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fsqrtSKvm` ends in `exec`'s state. -/
theorem fsqrtSKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPSqrt32Eq A) (hσ : fsqrtSKvm.ctx σ u)
    (h : fsqrtSKvm.Run P (fpFields2 d n) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32Sqrt (s.dregs n).toUInt32).toUInt64 with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPSqrt32Eq at hA
    unfold Footprint.Run at h
    rw [fsqrtSKvm_n0, show fsqrtSKvm.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fsqrtSKvm` has a path to an outcome. -/
theorem fsqrtSKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPSqrt32Eq A) (hσ : fsqrtSKvm.ctx σ u) :
    ∃ o, fsqrtSKvm.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPSqrt32Eq at hA
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [fsqrtSKvm_n0, show fsqrtSKvm.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FSQRT Sd, Sn` under `kvm` agrees with `exec` for every register number and every
state, where `A` satisfies `FPSqrt32Eq`. -/
theorem fsqrtS_kvm (P : Platform) (A : Abstract) (hA : FPSqrt32Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fsqrtSKvm
      (fpFields2 d n) (.fsqrtS d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fsqrtSKvm, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fsqrtSKvm.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fsqrtSKvm_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fsqrtSKvm_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fsqrtSKvm_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FRINTN Sd, Sn` under the profile `tcg`. -/
def frintnSTcg : Footprint := isla_trace% "tests/isla/tcg/frintn-s"

isla_nodes frintnSTcg

set_option maxRecDepth 100000 in
theorem frintnSTcg_n0 : frintnSTcg.trace = frintnSTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx frintnSTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `frintnSTcg` ends in `exec`'s state. -/
theorem frintnSTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPRoundInt32Eq A) (hσ : frintnSTcg.ctx σ u)
    (h : frintnSTcg.Run P (fpFields2 d n) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32Nearest (s.dregs n).toUInt32).toUInt64 with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPRoundInt32Eq at hA
    unfold Footprint.Run at h
    rw [frintnSTcg_n0, show frintnSTcg.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `frintnSTcg` has a path to an outcome. -/
theorem frintnSTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPRoundInt32Eq A) (hσ : frintnSTcg.ctx σ u) :
    ∃ o, frintnSTcg.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPRoundInt32Eq at hA
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [frintnSTcg_n0, show frintnSTcg.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FRINTN Sd, Sn` under `tcg` agrees with `exec` for every register number and every
state, where `A` satisfies `FPRoundInt32Eq`. -/
theorem frintnS_tcg (P : Platform) (A : Abstract) (hA : FPRoundInt32Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] frintnSTcg
      (fpFields2 d n) (.frintnS d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, frintnSTcg, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := frintnSTcg.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := frintnSTcg_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := frintnSTcg_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => frintnSTcg_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FRINTN Sd, Sn` under the profile `kvm`. -/
def frintnSKvm : Footprint := isla_trace% "tests/isla/kvm/frintn-s"

isla_nodes frintnSKvm

set_option maxRecDepth 100000 in
theorem frintnSKvm_n0 : frintnSKvm.trace = frintnSKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx frintnSKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `frintnSKvm` ends in `exec`'s state. -/
theorem frintnSKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPRoundInt32Eq A) (hσ : frintnSKvm.ctx σ u)
    (h : frintnSKvm.Run P (fpFields2 d n) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32Nearest (s.dregs n).toUInt32).toUInt64 with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPRoundInt32Eq at hA
    unfold Footprint.Run at h
    rw [frintnSKvm_n0, show frintnSKvm.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `frintnSKvm` has a path to an outcome. -/
theorem frintnSKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPRoundInt32Eq A) (hσ : frintnSKvm.ctx σ u) :
    ∃ o, frintnSKvm.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPRoundInt32Eq at hA
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [frintnSKvm_n0, show frintnSKvm.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FRINTN Sd, Sn` under `kvm` agrees with `exec` for every register number and every
state, where `A` satisfies `FPRoundInt32Eq`. -/
theorem frintnS_kvm (P : Platform) (A : Abstract) (hA : FPRoundInt32Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] frintnSKvm
      (fpFields2 d n) (.frintnS d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, frintnSKvm, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := frintnSKvm.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := frintnSKvm_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := frintnSKvm_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => frintnSKvm_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `UCVTF Sd, Xn` under the profile `tcg`. -/
def ucvtfSxTcg : Footprint := isla_trace% "tests/isla/tcg/ucvtf-sx"

isla_nodes ucvtfSxTcg

set_option maxRecDepth 100000 in
theorem ucvtfSxTcg_n0 : ucvtfSxTcg.trace = ucvtfSxTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx ucvtfSxTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `ucvtfSxTcg` ends in `exec`'s state. -/
theorem ucvtfSxTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FixedToFP64_32Eq A) (hσ : ucvtfSxTcg.ctx σ u)
    (h : ucvtfSxTcg.Run P (fpFields2 d n) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32ConvertI64U (s.x n)).toUInt64 with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FixedToFP64_32Eq at hA
    have hA0 := hA 0
    simp only [UInt64.toNat_zero] at hA0
    unfold Footprint.Run at h
    rw [ucvtfSxTcg_n0, show ucvtfSxTcg.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hA0, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ucvtfSxTcg` has a path to an outcome. -/
theorem ucvtfSxTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FixedToFP64_32Eq A) (hσ : ucvtfSxTcg.ctx σ u) :
    ∃ o, ucvtfSxTcg.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FixedToFP64_32Eq at hA
    have hA0 := hA 0
    simp only [UInt64.toNat_zero] at hA0
    by_cases h0 : n.val = 31
    rotate_left
    rotate_left
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [ucvtfSxTcg_n0, show ucvtfSxTcg.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hA0, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals first
      | rfl
      | fp_side hσ [hA, hA0, hi_lo_mod32, low32_eq, u32_mod, schain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32, f32ConvertI64U_zero, UInt32.toNat_zero]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `UCVTF Sd, Xn` under `tcg` agrees with `exec` for every register number and every
state, where `A` satisfies `FixedToFP64_32Eq`. -/
theorem ucvtfSx_tcg (P : Platform) (A : Abstract) (hA : FixedToFP64_32Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] ucvtfSxTcg
      (fpFields2 d n) (.ucvtfSX d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, ucvtfSxTcg, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := ucvtfSxTcg.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := ucvtfSxTcg_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := ucvtfSxTcg_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => ucvtfSxTcg_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `UCVTF Sd, Xn` under the profile `kvm`. -/
def ucvtfSxKvm : Footprint := isla_trace% "tests/isla/kvm/ucvtf-sx"

isla_nodes ucvtfSxKvm

set_option maxRecDepth 100000 in
theorem ucvtfSxKvm_n0 : ucvtfSxKvm.trace = ucvtfSxKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx ucvtfSxKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `ucvtfSxKvm` ends in `exec`'s state. -/
theorem ucvtfSxKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FixedToFP64_32Eq A) (hσ : ucvtfSxKvm.ctx σ u)
    (h : ucvtfSxKvm.Run P (fpFields2 d n) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32ConvertI64U (s.x n)).toUInt64 with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FixedToFP64_32Eq at hA
    have hA0 := hA 0
    simp only [UInt64.toNat_zero] at hA0
    unfold Footprint.Run at h
    rw [ucvtfSxKvm_n0, show ucvtfSxKvm.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hA0, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ucvtfSxKvm` has a path to an outcome. -/
theorem ucvtfSxKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FixedToFP64_32Eq A) (hσ : ucvtfSxKvm.ctx σ u) :
    ∃ o, ucvtfSxKvm.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FixedToFP64_32Eq at hA
    have hA0 := hA 0
    simp only [UInt64.toNat_zero] at hA0
    by_cases h0 : n.val = 31
    rotate_left
    rotate_left
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [ucvtfSxKvm_n0, show ucvtfSxKvm.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hA0, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals first
      | rfl
      | fp_side hσ [hA, hA0, hi_lo_mod32, low32_eq, u32_mod, schain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32, f32ConvertI64U_zero, UInt32.toNat_zero]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `UCVTF Sd, Xn` under `kvm` agrees with `exec` for every register number and every
state, where `A` satisfies `FixedToFP64_32Eq`. -/
theorem ucvtfSx_kvm (P : Platform) (A : Abstract) (hA : FixedToFP64_32Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] ucvtfSxKvm
      (fpFields2 d n) (.ucvtfSX d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, ucvtfSxKvm, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := ucvtfSxKvm.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := ucvtfSxKvm_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := ucvtfSxKvm_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => ucvtfSxKvm_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `SCVTF Sd, Wn` under the profile `tcg`. -/
def scvtfSwTcg : Footprint := isla_trace% "tests/isla/tcg/scvtf-sw"

isla_nodes scvtfSwTcg

set_option maxRecDepth 100000 in
theorem scvtfSwTcg_n0 : scvtfSwTcg.trace = scvtfSwTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx scvtfSwTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `scvtfSwTcg` ends in `exec`'s state. -/
theorem scvtfSwTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FixedToFP32_32Eq A) (hσ : scvtfSwTcg.ctx σ u)
    (h : scvtfSwTcg.Run P (fpFields2 d n) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32ConvertI32S (s.x n).toUInt32).toUInt64 with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FixedToFP32_32Eq at hA
    have hA0 := hA 0
    simp only [UInt32.toNat_zero] at hA0
    unfold Footprint.Run at h
    rw [scvtfSwTcg_n0, show scvtfSwTcg.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hA0, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `scvtfSwTcg` has a path to an outcome. -/
theorem scvtfSwTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FixedToFP32_32Eq A) (hσ : scvtfSwTcg.ctx σ u) :
    ∃ o, scvtfSwTcg.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FixedToFP32_32Eq at hA
    have hA0 := hA 0
    simp only [UInt32.toNat_zero] at hA0
    by_cases h0 : n.val = 31
    rotate_left
    rotate_left
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [scvtfSwTcg_n0, show scvtfSwTcg.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hA0, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals first
      | rfl
      | fp_side hσ [hA, hA0, hi_lo_mod32, low32_eq, u32_mod, schain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32, f32ConvertI32S_zero, UInt32.toNat_zero]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `SCVTF Sd, Wn` under `tcg` agrees with `exec` for every register number and every
state, where `A` satisfies `FixedToFP32_32Eq`. -/
theorem scvtfSw_tcg (P : Platform) (A : Abstract) (hA : FixedToFP32_32Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] scvtfSwTcg
      (fpFields2 d n) (.scvtfSW d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, scvtfSwTcg, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := scvtfSwTcg.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := scvtfSwTcg_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := scvtfSwTcg_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => scvtfSwTcg_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `SCVTF Sd, Wn` under the profile `kvm`. -/
def scvtfSwKvm : Footprint := isla_trace% "tests/isla/kvm/scvtf-sw"

isla_nodes scvtfSwKvm

set_option maxRecDepth 100000 in
theorem scvtfSwKvm_n0 : scvtfSwKvm.trace = scvtfSwKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx scvtfSwKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `scvtfSwKvm` ends in `exec`'s state. -/
theorem scvtfSwKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FixedToFP32_32Eq A) (hσ : scvtfSwKvm.ctx σ u)
    (h : scvtfSwKvm.Run P (fpFields2 d n) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32ConvertI32S (s.x n).toUInt32).toUInt64 with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FixedToFP32_32Eq at hA
    have hA0 := hA 0
    simp only [UInt32.toNat_zero] at hA0
    unfold Footprint.Run at h
    rw [scvtfSwKvm_n0, show scvtfSwKvm.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hA0, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `scvtfSwKvm` has a path to an outcome. -/
theorem scvtfSwKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FixedToFP32_32Eq A) (hσ : scvtfSwKvm.ctx σ u) :
    ∃ o, scvtfSwKvm.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FixedToFP32_32Eq at hA
    have hA0 := hA 0
    simp only [UInt32.toNat_zero] at hA0
    by_cases h0 : n.val = 31
    rotate_left
    rotate_left
    all_goals
      refine ⟨?_, ?_⟩
      rotate_left
      unfold Footprint.Run
      rw [scvtfSwKvm_n0, show scvtfSwKvm.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hA0, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals first
      | rfl
      | fp_side hσ [hA, hA0, hi_lo_mod32, low32_eq, u32_mod, schain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32, f32ConvertI32S_zero, UInt32.toNat_zero]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `SCVTF Sd, Wn` under `kvm` agrees with `exec` for every register number and every
state, where `A` satisfies `FixedToFP32_32Eq`. -/
theorem scvtfSw_kvm (P : Platform) (A : Abstract) (hA : FixedToFP32_32Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] scvtfSwKvm
      (fpFields2 d n) (.scvtfSW d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, scvtfSwKvm, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := scvtfSwKvm.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := scvtfSwKvm_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := scvtfSwKvm_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => scvtfSwKvm_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FCVTZU Xd, Sn` under the profile `tcg`. -/
def fcvtzuXsTcg : Footprint := isla_trace% "tests/isla/tcg/fcvtzu-xs"

isla_nodes fcvtzuXsTcg

set_option maxRecDepth 100000 in
theorem fcvtzuXsTcg_n0 : fcvtzuXsTcg.trace = fcvtzuXsTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fcvtzuXsTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fcvtzuXsTcg` ends in `exec`'s state. -/
theorem fcvtzuXsTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPToFixed32_64Eq A) (hσ : fcvtzuXsTcg.ctx σ u)
    (h : fcvtzuXsTcg.Run P (fpFields2 d n) s σ o A) :
    o = .done { s.setX d (Wasm.i64TruncSatF32U (s.dregs n).toUInt32) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 293)) := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixed32_64Eq at hA
    unfold Footprint.Run at h
    rw [fcvtzuXsTcg_n0, show fcvtzuXsTcg.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals wreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fcvtzuXsTcg` has a path to `exec`'s state. -/
theorem fcvtzuXsTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPToFixed32_64Eq A) (hσ : fcvtzuXsTcg.ctx σ u) :
    fcvtzuXsTcg.Run P (fpFields2 d n) s σ
      (.done { s.setX d (Wasm.i64TruncSatF32U (s.dregs n).toUInt32) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 293))) A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixed32_64Eq at hA
    by_cases h0 : d.val = 31
    rotate_left
    rotate_left
    all_goals
      unfold Footprint.Run
      rw [fcvtzuXsTcg_n0, show fcvtzuXsTcg.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | (apply Eq.symm; wreg_end; done)
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FCVTZU Xd, Sn` under `tcg` agrees with `exec` for every register number and every
state, where `A` satisfies `FPToFixed32_64Eq`. -/
theorem fcvtzuXs_tcg (P : Platform) (A : Abstract) (hA : FPToFixed32_64Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "FPSR"] fcvtzuXsTcg
      (fpFields2 d n) (.fcvtzuXS d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fcvtzuXsTcg, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fcvtzuXsTcg.ctx_of σ u hσ
      exact ⟨⟨_, fcvtzuXsTcg_bwd hA hc⟩, fun o h => ⟨_, fcvtzuXsTcg_fwd hA hc h, by frame_end⟩⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FCVTZU Xd, Sn` under the profile `kvm`. -/
def fcvtzuXsKvm : Footprint := isla_trace% "tests/isla/kvm/fcvtzu-xs"

isla_nodes fcvtzuXsKvm

set_option maxRecDepth 100000 in
theorem fcvtzuXsKvm_n0 : fcvtzuXsKvm.trace = fcvtzuXsKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fcvtzuXsKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fcvtzuXsKvm` ends in `exec`'s state. -/
theorem fcvtzuXsKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPToFixed32_64Eq A) (hσ : fcvtzuXsKvm.ctx σ u)
    (h : fcvtzuXsKvm.Run P (fpFields2 d n) s σ o A) :
    o = .done { s.setX d (Wasm.i64TruncSatF32U (s.dregs n).toUInt32) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 293)) := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixed32_64Eq at hA
    unfold Footprint.Run at h
    rw [fcvtzuXsKvm_n0, show fcvtzuXsKvm.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals wreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fcvtzuXsKvm` has a path to `exec`'s state. -/
theorem fcvtzuXsKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPToFixed32_64Eq A) (hσ : fcvtzuXsKvm.ctx σ u) :
    fcvtzuXsKvm.Run P (fpFields2 d n) s σ
      (.done { s.setX d (Wasm.i64TruncSatF32U (s.dregs n).toUInt32) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 293))) A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixed32_64Eq at hA
    by_cases h0 : d.val = 31
    rotate_left
    rotate_left
    all_goals
      unfold Footprint.Run
      rw [fcvtzuXsKvm_n0, show fcvtzuXsKvm.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | (apply Eq.symm; wreg_end; done)
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FCVTZU Xd, Sn` under `kvm` agrees with `exec` for every register number and every
state, where `A` satisfies `FPToFixed32_64Eq`. -/
theorem fcvtzuXs_kvm (P : Platform) (A : Abstract) (hA : FPToFixed32_64Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "FPSR"] fcvtzuXsKvm
      (fpFields2 d n) (.fcvtzuXS d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fcvtzuXsKvm, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fcvtzuXsKvm.ctx_of σ u hσ
      exact ⟨⟨_, fcvtzuXsKvm_bwd hA hc⟩, fun o h => ⟨_, fcvtzuXsKvm_fwd hA hc h, by frame_end⟩⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FCVTZS Wd, Sn` under the profile `tcg`. -/
def fcvtzsWsTcg : Footprint := isla_trace% "tests/isla/tcg/fcvtzs-ws"

isla_nodes fcvtzsWsTcg

set_option maxRecDepth 100000 in
theorem fcvtzsWsTcg_n0 : fcvtzsWsTcg.trace = fcvtzsWsTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fcvtzsWsTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fcvtzsWsTcg` ends in `exec`'s state. -/
theorem fcvtzsWsTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPToFixed32_32Eq A) (hσ : fcvtzsWsTcg.ctx σ u)
    (h : fcvtzsWsTcg.Run P (fpFields2 d n) s σ o A) :
    o = .done { s.setX d (Wasm.i32TruncSatF32S (s.dregs n).toUInt32).toUInt64 with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 292)) := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixed32_32Eq at hA
    unfold Footprint.Run at h
    rw [fcvtzsWsTcg_n0, show fcvtzsWsTcg.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals wreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fcvtzsWsTcg` has a path to `exec`'s state. -/
theorem fcvtzsWsTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPToFixed32_32Eq A) (hσ : fcvtzsWsTcg.ctx σ u) :
    fcvtzsWsTcg.Run P (fpFields2 d n) s σ
      (.done { s.setX d (Wasm.i32TruncSatF32S (s.dregs n).toUInt32).toUInt64 with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 292))) A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixed32_32Eq at hA
    by_cases h0 : d.val = 31
    rotate_left
    rotate_left
    all_goals
      unfold Footprint.Run
      rw [fcvtzsWsTcg_n0, show fcvtzsWsTcg.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | (apply Eq.symm; wreg_end; done)
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FCVTZS Wd, Sn` under `tcg` agrees with `exec` for every register number and every
state, where `A` satisfies `FPToFixed32_32Eq`. -/
theorem fcvtzsWs_tcg (P : Platform) (A : Abstract) (hA : FPToFixed32_32Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "FPSR"] fcvtzsWsTcg
      (fpFields2 d n) (.fcvtzsWS d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fcvtzsWsTcg, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fcvtzsWsTcg.ctx_of σ u hσ
      exact ⟨⟨_, fcvtzsWsTcg_bwd hA hc⟩, fun o h => ⟨_, fcvtzsWsTcg_fwd hA hc h, by frame_end⟩⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FCVTZS Wd, Sn` under the profile `kvm`. -/
def fcvtzsWsKvm : Footprint := isla_trace% "tests/isla/kvm/fcvtzs-ws"

isla_nodes fcvtzsWsKvm

set_option maxRecDepth 100000 in
theorem fcvtzsWsKvm_n0 : fcvtzsWsKvm.trace = fcvtzsWsKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fcvtzsWsKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fcvtzsWsKvm` ends in `exec`'s state. -/
theorem fcvtzsWsKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPToFixed32_32Eq A) (hσ : fcvtzsWsKvm.ctx σ u)
    (h : fcvtzsWsKvm.Run P (fpFields2 d n) s σ o A) :
    o = .done { s.setX d (Wasm.i32TruncSatF32S (s.dregs n).toUInt32).toUInt64 with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 292)) := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixed32_32Eq at hA
    unfold Footprint.Run at h
    rw [fcvtzsWsKvm_n0, show fcvtzsWsKvm.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals wreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fcvtzsWsKvm` has a path to `exec`'s state. -/
theorem fcvtzsWsKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPToFixed32_32Eq A) (hσ : fcvtzsWsKvm.ctx σ u) :
    fcvtzsWsKvm.Run P (fpFields2 d n) s σ
      (.done { s.setX d (Wasm.i32TruncSatF32S (s.dregs n).toUInt32).toUInt64 with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 292))) A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixed32_32Eq at hA
    by_cases h0 : d.val = 31
    rotate_left
    rotate_left
    all_goals
      unfold Footprint.Run
      rw [fcvtzsWsKvm_n0, show fcvtzsWsKvm.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | (apply Eq.symm; wreg_end; done)
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FCVTZS Wd, Sn` under `kvm` agrees with `exec` for every register number and every
state, where `A` satisfies `FPToFixed32_32Eq`. -/
theorem fcvtzsWs_kvm (P : Platform) (A : Abstract) (hA : FPToFixed32_32Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "FPSR"] fcvtzsWsKvm
      (fpFields2 d n) (.fcvtzsWS d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fcvtzsWsKvm, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fcvtzsWsKvm.ctx_of σ u hσ
      exact ⟨⟨_, fcvtzsWsKvm_bwd hA hc⟩, fun o h => ⟨_, fcvtzsWsKvm_fwd hA hc h, by frame_end⟩⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FCMP Sn, Sm` under the profile `tcg`. -/
def fcmpSTcg : Footprint := isla_trace% "tests/isla/tcg/fcmp-s"

isla_nodes fcmpSTcg

set_option maxRecDepth 100000 in
theorem fcmpSTcg_n0 : fcmpSTcg.trace = fcmpSTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fcmpSTcg (tcg.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fcmpSTcg` ends in `exec`'s state. -/
theorem fcmpSTcg_fwd {P : Platform} {A : Abstract} {u : Unknown} {n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPCompare32Eq A) (hσ : fcmpSTcg.ctx σ u)
    (h : fcmpSTcg.Run P (fcmpFields n m) s σ o A) :
    o = .done { s.fcmpS (s.dregs n).toUInt32 (s.dregs m).toUInt32 with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 272)) := by
  without_info
    have := n.isLt
    have := m.isLt
    unfold FPCompare32Eq at hA
    unfold Footprint.Run at h
    rw [fcmpSTcg_n0, show fcmpSTcg.vars (fcmpFields n m) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals flags32_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fcmpSTcg` has a path to `exec`'s state. -/
theorem fcmpSTcg_bwd {P : Platform} {A : Abstract} {u : Unknown} {n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPCompare32Eq A) (hσ : fcmpSTcg.ctx σ u) :
    fcmpSTcg.Run P (fcmpFields n m) s σ
      (.done { s.fcmpS (s.dregs n).toUInt32 (s.dregs m).toUInt32 with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 272))) A := by
  without_info
    have := n.isLt
    have := m.isLt
    unfold FPCompare32Eq at hA
    all_goals
      unfold Footprint.Run
      rw [fcmpSTcg_n0, show fcmpSTcg.vars (fcmpFields n m) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | (apply Eq.symm; flags32_end; done)
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq, fcmpNZCV32_lt]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FCMP Sn, Sm` under `tcg` agrees with `exec` for every register number and every
state, where `A` satisfies `FPCompare32Eq`. -/
theorem fcmpS_tcg (P : Platform) (A : Abstract) (hA : FPCompare32Eq A)
    (u : Unknown) (n m : Fin 32) (s : State) :
    AgreesAll P A (tcg.sys .fp u) ["SEE", "__BranchTaken", "FPSR"] fcmpSTcg
      (fcmpFields n m) (.fcmpS n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fcmpSTcg, fcmpFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fcmpSTcg.ctx_of σ u hσ
      exact ⟨⟨_, fcmpSTcg_bwd hA hc⟩, fun o h => ⟨_, fcmpSTcg_fwd hA hc h, by frame_end⟩⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FCMP Sn, Sm` under the profile `kvm`. -/
def fcmpSKvm : Footprint := isla_trace% "tests/isla/kvm/fcmp-s"

isla_nodes fcmpSKvm

set_option maxRecDepth 100000 in
theorem fcmpSKvm_n0 : fcmpSKvm.trace = fcmpSKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fcmpSKvm (kvm.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fcmpSKvm` ends in `exec`'s state. -/
theorem fcmpSKvm_fwd {P : Platform} {A : Abstract} {u : Unknown} {n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPCompare32Eq A) (hσ : fcmpSKvm.ctx σ u)
    (h : fcmpSKvm.Run P (fcmpFields n m) s σ o A) :
    o = .done { s.fcmpS (s.dregs n).toUInt32 (s.dregs m).toUInt32 with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 272)) := by
  without_info
    have := n.isLt
    have := m.isLt
    unfold FPCompare32Eq at hA
    unfold Footprint.Run at h
    rw [fcmpSKvm_n0, show fcmpSKvm.vars (fcmpFields n m) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals flags32_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fcmpSKvm` has a path to `exec`'s state. -/
theorem fcmpSKvm_bwd {P : Platform} {A : Abstract} {u : Unknown} {n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPCompare32Eq A) (hσ : fcmpSKvm.ctx σ u) :
    fcmpSKvm.Run P (fcmpFields n m) s σ
      (.done { s.fcmpS (s.dregs n).toUInt32 (s.dregs m).toUInt32 with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 272))) A := by
  without_info
    have := n.isLt
    have := m.isLt
    unfold FPCompare32Eq at hA
    all_goals
      unfold Footprint.Run
      rw [fcmpSKvm_n0, show fcmpSKvm.vars (fcmpFields n m) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | (apply Eq.symm; flags32_end; done)
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq, fcmpNZCV32_lt]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FCMP Sn, Sm` under `kvm` agrees with `exec` for every register number and every
state, where `A` satisfies `FPCompare32Eq`. -/
theorem fcmpS_kvm (P : Platform) (A : Abstract) (hA : FPCompare32Eq A)
    (u : Unknown) (n m : Fin 32) (s : State) :
    AgreesAll P A (kvm.sys .fp u) ["SEE", "__BranchTaken", "FPSR"] fcmpSKvm
      (fcmpFields n m) (.fcmpS n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fcmpSKvm, fcmpFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fcmpSKvm.ctx_of σ u hσ
      exact ⟨⟨_, fcmpSKvm_bwd hA hc⟩, fun o h => ⟨_, fcmpSKvm_fwd hA hc h, by frame_end⟩⟩

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.fmovSw_tcg
#print axioms TestSupport.A64.Isla.fmovSw_kvm
#print axioms TestSupport.A64.Isla.fmovWs_tcg
#print axioms TestSupport.A64.Isla.fmovWs_kvm
#print axioms TestSupport.A64.Isla.faddS_tcg
#print axioms TestSupport.A64.Isla.faddS_kvm
#print axioms TestSupport.A64.Isla.fsubS_tcg
#print axioms TestSupport.A64.Isla.fsubS_kvm
#print axioms TestSupport.A64.Isla.fmulS_tcg
#print axioms TestSupport.A64.Isla.fmulS_kvm
#print axioms TestSupport.A64.Isla.fdivS_tcg
#print axioms TestSupport.A64.Isla.fdivS_kvm
#print axioms TestSupport.A64.Isla.fsqrtS_tcg
#print axioms TestSupport.A64.Isla.fsqrtS_kvm
#print axioms TestSupport.A64.Isla.frintnS_tcg
#print axioms TestSupport.A64.Isla.frintnS_kvm
#print axioms TestSupport.A64.Isla.ucvtfSx_tcg
#print axioms TestSupport.A64.Isla.ucvtfSx_kvm
#print axioms TestSupport.A64.Isla.scvtfSw_tcg
#print axioms TestSupport.A64.Isla.scvtfSw_kvm
#print axioms TestSupport.A64.Isla.fcvtzuXs_tcg
#print axioms TestSupport.A64.Isla.fcvtzuXs_kvm
#print axioms TestSupport.A64.Isla.fcvtzsWs_tcg
#print axioms TestSupport.A64.Isla.fcvtzsWs_kvm
#print axioms TestSupport.A64.Isla.fcmpS_tcg
#print axioms TestSupport.A64.Isla.fcmpS_kvm
