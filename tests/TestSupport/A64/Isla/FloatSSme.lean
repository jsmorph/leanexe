import LeanExe.A64.Isla.Float

/-!
Theorems of `AgreesAll`, or of `Agrees` for `FMOV Wd, Sn`, for the single-precision forms of
`LeanExe/A64/Machine.lean`, from the traces of `tests/isla/sme` under the profiles
`sme` with the arguments `fp` of `tests/isla/traces.sh`.  Each theorem holds for every value
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
/-- The footprint of `FMOV Sd, Wn` under the profile `sme`. -/
def fmovSwSme : Footprint := isla_trace% "tests/isla/sme/fmov-sw"

isla_nodes fmovSwSme

set_option maxRecDepth 100000 in
theorem fmovSwSme_n0 : fmovSwSme.trace = fmovSwSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmovSwSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmovSwSme` ends in `exec`'s state. -/
theorem fmovSwSme_fwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hσ : fmovSwSme.ctx σ u)
    (h : fmovSwSme.Run P (fpFields2 d n) s σ o) :
    ∃ σ', o = .done
      { s.setD d (s.x n).toUInt32.toUInt64 with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold Footprint.Run at h
    rw [fmovSwSme_n0, show fmovSwSme.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmovSwSme` has a path to an outcome. -/
theorem fmovSwSme_bwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hσ : fmovSwSme.ctx σ u) :
    ∃ o, fmovSwSme.Run P (fpFields2 d n) s σ o := by
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
      rw [fmovSwSme_n0, show fmovSwSme.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals first
      | rfl
      | fp_side hσ [hi_lo_mod32, low32_eq, u32_mod, schain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMOV Sd, Wn` under `sme` agrees with `exec` for every register number and every
state. -/
theorem fmovSw_sme (P : Platform)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P noAbstract (sme.sys .fp u) ["SEE", "__BranchTaken", "_Z"] fmovSwSme
      (fpFields2 d n) (.fmovSW d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmovSwSme, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmovSwSme.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fmovSwSme_bwd (P := P) (d := d) (n := n) (s := s) hc
      obtain ⟨σ', rfl, -⟩ := fmovSwSme_fwd hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fmovSwSme_fwd hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FMOV Wd, Sn` under the profile `sme`. -/
def fmovWsSme : Footprint := isla_trace% "tests/isla/sme/fmov-ws"

isla_nodes fmovWsSme

set_option maxRecDepth 100000 in
theorem fmovWsSme_n0 : fmovWsSme.trace = fmovWsSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmovWsSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmovWsSme` ends in `exec`'s state. -/
theorem fmovWsSme_fwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hσ : fmovWsSme.ctx σ u)
    (h : fmovWsSme.Run P (fpFields2 d n) s σ o) :
    o = .done { s.setX d (s.dregs n).toUInt32.toUInt64 with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 295)) := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold Footprint.Run at h
    rw [fmovWsSme_n0, show fmovWsSme.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals wreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmovWsSme` has a path to `exec`'s state. -/
theorem fmovWsSme_bwd {P : Platform} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hσ : fmovWsSme.ctx σ u) :
    fmovWsSme.Run P (fpFields2 d n) s σ
      (.done { s.setX d (s.dregs n).toUInt32.toUInt64 with pc := s.pc + 4 }
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
      rw [fmovWsSme_n0, show fmovWsSme.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | (apply Eq.symm; wreg_end; done)
      | fp_side hσ [hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMOV Wd, Sn` under `sme` agrees with `exec` for every register number and every
state. -/
theorem fmovWs_sme (P : Platform) (u : Unknown) (d n : Fin 32) (s : State) :
    Agrees P (sme.sys .fp u) ["SEE", "__BranchTaken"] fmovWsSme (fpFields2 d n) (.fmovWS d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmovWsSme, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmovWsSme.ctx_of σ u hσ
      exact ⟨_, fun o => ⟨fun h => fmovWsSme_fwd hc h, fun h => h ▸ fmovWsSme_bwd hc⟩, by frame_end⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FADD Sd, Sn, Sm` under the profile `sme`. -/
def faddSSme : Footprint := isla_trace% "tests/isla/sme/fadd-s"

isla_nodes faddSSme

set_option maxRecDepth 100000 in
theorem faddSSme_n0 : faddSSme.trace = faddSSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx faddSSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `faddSSme` ends in `exec`'s state. -/
theorem faddSSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPAdd32Eq A) (hσ : faddSSme.ctx σ u)
    (h : faddSSme.Run P (fpFields3 d n m) s σ o A) :
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
    rw [faddSSme_n0, show faddSSme.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `faddSSme` has a path to an outcome. -/
theorem faddSSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPAdd32Eq A) (hσ : faddSSme.ctx σ u) :
    ∃ o, faddSSme.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPAdd32Eq at hA
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
      rw [faddSSme_n0, show faddSSme.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FADD Sd, Sn, Sm` under `sme` agrees with `exec` for every register number and every
state, where `A` satisfies `FPAdd32Eq`. -/
theorem faddS_sme (P : Platform) (A : Abstract) (hA : FPAdd32Eq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] faddSSme
      (fpFields3 d n m) (.faddS d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, faddSSme, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := faddSSme.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := faddSSme_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := faddSSme_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => faddSSme_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FSUB Sd, Sn, Sm` under the profile `sme`. -/
def fsubSSme : Footprint := isla_trace% "tests/isla/sme/fsub-s"

isla_nodes fsubSSme

set_option maxRecDepth 100000 in
theorem fsubSSme_n0 : fsubSSme.trace = fsubSSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fsubSSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fsubSSme` ends in `exec`'s state. -/
theorem fsubSSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPSub32Eq A) (hσ : fsubSSme.ctx σ u)
    (h : fsubSSme.Run P (fpFields3 d n m) s σ o A) :
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
    rw [fsubSSme_n0, show fsubSSme.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fsubSSme` has a path to an outcome. -/
theorem fsubSSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPSub32Eq A) (hσ : fsubSSme.ctx σ u) :
    ∃ o, fsubSSme.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPSub32Eq at hA
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
      rw [fsubSSme_n0, show fsubSSme.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FSUB Sd, Sn, Sm` under `sme` agrees with `exec` for every register number and every
state, where `A` satisfies `FPSub32Eq`. -/
theorem fsubS_sme (P : Platform) (A : Abstract) (hA : FPSub32Eq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fsubSSme
      (fpFields3 d n m) (.fsubS d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fsubSSme, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fsubSSme.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fsubSSme_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fsubSSme_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fsubSSme_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FMUL Sd, Sn, Sm` under the profile `sme`. -/
def fmulSSme : Footprint := isla_trace% "tests/isla/sme/fmul-s"

isla_nodes fmulSSme

set_option maxRecDepth 100000 in
theorem fmulSSme_n0 : fmulSSme.trace = fmulSSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fmulSSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fmulSSme` ends in `exec`'s state. -/
theorem fmulSSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPMul32Eq A) (hσ : fmulSSme.ctx σ u)
    (h : fmulSSme.Run P (fpFields3 d n m) s σ o A) :
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
    rw [fmulSSme_n0, show fmulSSme.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fmulSSme` has a path to an outcome. -/
theorem fmulSSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPMul32Eq A) (hσ : fmulSSme.ctx σ u) :
    ∃ o, fmulSSme.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPMul32Eq at hA
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
      rw [fmulSSme_n0, show fmulSSme.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FMUL Sd, Sn, Sm` under `sme` agrees with `exec` for every register number and every
state, where `A` satisfies `FPMul32Eq`. -/
theorem fmulS_sme (P : Platform) (A : Abstract) (hA : FPMul32Eq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fmulSSme
      (fpFields3 d n m) (.fmulS d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fmulSSme, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fmulSSme.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fmulSSme_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fmulSSme_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fmulSSme_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FDIV Sd, Sn, Sm` under the profile `sme`. -/
def fdivSSme : Footprint := isla_trace% "tests/isla/sme/fdiv-s"

isla_nodes fdivSSme

set_option maxRecDepth 100000 in
theorem fdivSSme_n0 : fdivSSme.trace = fdivSSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fdivSSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fdivSSme` ends in `exec`'s state. -/
theorem fdivSSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPDiv32Eq A) (hσ : fdivSSme.ctx σ u)
    (h : fdivSSme.Run P (fpFields3 d n m) s σ o A) :
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
    rw [fdivSSme_n0, show fdivSSme.vars (fpFields3 d n m) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
        (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fdivSSme` has a path to an outcome. -/
theorem fdivSSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPDiv32Eq A) (hσ : fdivSSme.ctx σ u) :
    ∃ o, fdivSSme.Run P (fpFields3 d n m) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    have := m.isLt
    unfold FPDiv32Eq at hA
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
      rw [fdivSSme_n0, show fdivSSme.vars (fpFields3 d n m) =
        Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val)) 2
          (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FDIV Sd, Sn, Sm` under `sme` agrees with `exec` for every register number and every
state, where `A` satisfies `FPDiv32Eq`. -/
theorem fdivS_sme (P : Platform) (A : Abstract) (hA : FPDiv32Eq A)
    (u : Unknown) (d n m : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fdivSSme
      (fpFields3 d n m) (.fdivS d n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fdivSSme, fpFields3, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fdivSSme.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fdivSSme_bwd (P := P) (d := d) (n := n) (m := m) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fdivSSme_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fdivSSme_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FSQRT Sd, Sn` under the profile `sme`. -/
def fsqrtSSme : Footprint := isla_trace% "tests/isla/sme/fsqrt-s"

isla_nodes fsqrtSSme

set_option maxRecDepth 100000 in
theorem fsqrtSSme_n0 : fsqrtSSme.trace = fsqrtSSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fsqrtSSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fsqrtSSme` ends in `exec`'s state. -/
theorem fsqrtSSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPSqrt32Eq A) (hσ : fsqrtSSme.ctx σ u)
    (h : fsqrtSSme.Run P (fpFields2 d n) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32Sqrt (s.dregs n).toUInt32).toUInt64 with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPSqrt32Eq at hA
    unfold Footprint.Run at h
    rw [fsqrtSSme_n0, show fsqrtSSme.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fsqrtSSme` has a path to an outcome. -/
theorem fsqrtSSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPSqrt32Eq A) (hσ : fsqrtSSme.ctx σ u) :
    ∃ o, fsqrtSSme.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPSqrt32Eq at hA
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
      rw [fsqrtSSme_n0, show fsqrtSSme.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FSQRT Sd, Sn` under `sme` agrees with `exec` for every register number and every
state, where `A` satisfies `FPSqrt32Eq`. -/
theorem fsqrtS_sme (P : Platform) (A : Abstract) (hA : FPSqrt32Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] fsqrtSSme
      (fpFields2 d n) (.fsqrtS d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fsqrtSSme, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fsqrtSSme.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := fsqrtSSme_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := fsqrtSSme_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => fsqrtSSme_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FRINTN Sd, Sn` under the profile `sme`. -/
def frintnSSme : Footprint := isla_trace% "tests/isla/sme/frintn-s"

isla_nodes frintnSSme

set_option maxRecDepth 100000 in
theorem frintnSSme_n0 : frintnSSme.trace = frintnSSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx frintnSSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `frintnSSme` ends in `exec`'s state. -/
theorem frintnSSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPRoundInt32Eq A) (hσ : frintnSSme.ctx σ u)
    (h : frintnSSme.Run P (fpFields2 d n) s σ o A) :
    ∃ σ', o = .done
      { s.setD d (Wasm.f32Nearest (s.dregs n).toUInt32).toUInt64 with pc := s.pc + 4 } σ' ∧
      ∀ r, r ∉ ["SEE", "__BranchTaken", "_Z", "FPSR"] → σ' r = σ r := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPRoundInt32Eq at hA
    unfold Footprint.Run at h
    rw [frintnSSme_n0, show frintnSSme.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `frintnSSme` has a path to an outcome. -/
theorem frintnSSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPRoundInt32Eq A) (hσ : frintnSSme.ctx σ u) :
    ∃ o, frintnSSme.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPRoundInt32Eq at hA
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
      rw [frintnSSme_n0, show frintnSSme.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | rfl
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FRINTN Sd, Sn` under `sme` agrees with `exec` for every register number and every
state, where `A` satisfies `FPRoundInt32Eq`. -/
theorem frintnS_sme (P : Platform) (A : Abstract) (hA : FPRoundInt32Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] frintnSSme
      (fpFields2 d n) (.frintnS d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, frintnSSme, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := frintnSSme.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := frintnSSme_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := frintnSSme_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => frintnSSme_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `UCVTF Sd, Xn` under the profile `sme`. -/
def ucvtfSxSme : Footprint := isla_trace% "tests/isla/sme/ucvtf-sx"

isla_nodes ucvtfSxSme

set_option maxRecDepth 100000 in
theorem ucvtfSxSme_n0 : ucvtfSxSme.trace = ucvtfSxSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx ucvtfSxSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `ucvtfSxSme` ends in `exec`'s state. -/
theorem ucvtfSxSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FixedToFP64_32Eq A) (hσ : ucvtfSxSme.ctx σ u)
    (h : ucvtfSxSme.Run P (fpFields2 d n) s σ o A) :
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
    rw [ucvtfSxSme_n0, show ucvtfSxSme.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hA0, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ucvtfSxSme` has a path to an outcome. -/
theorem ucvtfSxSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FixedToFP64_32Eq A) (hσ : ucvtfSxSme.ctx σ u) :
    ∃ o, ucvtfSxSme.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FixedToFP64_32Eq at hA
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
      rw [ucvtfSxSme_n0, show ucvtfSxSme.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hA0, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals first
      | rfl
      | fp_side hσ [hA, hA0, hi_lo_mod32, low32_eq, u32_mod, schain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32, f32ConvertI64U_zero, UInt32.toNat_zero]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `UCVTF Sd, Xn` under `sme` agrees with `exec` for every register number and every
state, where `A` satisfies `FixedToFP64_32Eq`. -/
theorem ucvtfSx_sme (P : Platform) (A : Abstract) (hA : FixedToFP64_32Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] ucvtfSxSme
      (fpFields2 d n) (.ucvtfSX d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, ucvtfSxSme, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := ucvtfSxSme.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := ucvtfSxSme_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := ucvtfSxSme_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => ucvtfSxSme_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `SCVTF Sd, Wn` under the profile `sme`. -/
def scvtfSwSme : Footprint := isla_trace% "tests/isla/sme/scvtf-sw"

isla_nodes scvtfSwSme

set_option maxRecDepth 100000 in
theorem scvtfSwSme_n0 : scvtfSwSme.trace = scvtfSwSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx scvtfSwSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `scvtfSwSme` ends in `exec`'s state. -/
theorem scvtfSwSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FixedToFP32_32Eq A) (hσ : scvtfSwSme.ctx σ u)
    (h : scvtfSwSme.Run P (fpFields2 d n) s σ o A) :
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
    rw [scvtfSwSme_n0, show scvtfSwSme.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hA0, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals sreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `scvtfSwSme` has a path to an outcome. -/
theorem scvtfSwSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FixedToFP32_32Eq A) (hσ : scvtfSwSme.ctx σ u) :
    ∃ o, scvtfSwSme.Run P (fpFields2 d n) s σ o A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FixedToFP32_32Eq at hA
    have hA0 := hA 0
    simp only [UInt32.toNat_zero] at hA0
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
      rw [scvtfSwSme_n0, show scvtfSwSme.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hA0, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32]
    all_goals first
      | rfl
      | fp_side hσ [hA, hA0, hi_lo_mod32, low32_eq, u32_mod, schain_eq, rwchain_eq, ofNat_and32_or, ofNat_and32, f32ConvertI32S_zero, UInt32.toNat_zero]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `SCVTF Sd, Wn` under `sme` agrees with `exec` for every register number and every
state, where `A` satisfies `FixedToFP32_32Eq`. -/
theorem scvtfSw_sme (P : Platform) (A : Abstract) (hA : FixedToFP32_32Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "_Z", "FPSR"] scvtfSwSme
      (fpFields2 d n) (.scvtfSW d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, scvtfSwSme, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := scvtfSwSme.ctx_of σ u hσ
      obtain ⟨o, ho⟩ := scvtfSwSme_bwd (P := P) (d := d) (n := n) (s := s) hA hc
      obtain ⟨σ', rfl, -⟩ := scvtfSwSme_fwd hA hc ho
      exact ⟨⟨σ', ho⟩, fun o h => scvtfSwSme_fwd hA hc h⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FCVTZU Xd, Sn` under the profile `sme`. -/
def fcvtzuXsSme : Footprint := isla_trace% "tests/isla/sme/fcvtzu-xs"

isla_nodes fcvtzuXsSme

set_option maxRecDepth 100000 in
theorem fcvtzuXsSme_n0 : fcvtzuXsSme.trace = fcvtzuXsSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fcvtzuXsSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fcvtzuXsSme` ends in `exec`'s state. -/
theorem fcvtzuXsSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPToFixed32_64Eq A) (hσ : fcvtzuXsSme.ctx σ u)
    (h : fcvtzuXsSme.Run P (fpFields2 d n) s σ o A) :
    o = .done { s.setX d (Wasm.i64TruncSatF32U (s.dregs n).toUInt32) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 293)) := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixed32_64Eq at hA
    unfold Footprint.Run at h
    rw [fcvtzuXsSme_n0, show fcvtzuXsSme.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals wreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fcvtzuXsSme` has a path to `exec`'s state. -/
theorem fcvtzuXsSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPToFixed32_64Eq A) (hσ : fcvtzuXsSme.ctx σ u) :
    fcvtzuXsSme.Run P (fpFields2 d n) s σ
      (.done { s.setX d (Wasm.i64TruncSatF32U (s.dregs n).toUInt32) with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 293))) A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixed32_64Eq at hA
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
      rw [fcvtzuXsSme_n0, show fcvtzuXsSme.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | (apply Eq.symm; wreg_end; done)
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FCVTZU Xd, Sn` under `sme` agrees with `exec` for every register number and every
state, where `A` satisfies `FPToFixed32_64Eq`. -/
theorem fcvtzuXs_sme (P : Platform) (A : Abstract) (hA : FPToFixed32_64Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "FPSR"] fcvtzuXsSme
      (fpFields2 d n) (.fcvtzuXS d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fcvtzuXsSme, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fcvtzuXsSme.ctx_of σ u hσ
      exact ⟨⟨_, fcvtzuXsSme_bwd hA hc⟩, fun o h => ⟨_, fcvtzuXsSme_fwd hA hc h, by frame_end⟩⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FCVTZS Wd, Sn` under the profile `sme`. -/
def fcvtzsWsSme : Footprint := isla_trace% "tests/isla/sme/fcvtzs-ws"

isla_nodes fcvtzsWsSme

set_option maxRecDepth 100000 in
theorem fcvtzsWsSme_n0 : fcvtzsWsSme.trace = fcvtzsWsSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fcvtzsWsSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fcvtzsWsSme` ends in `exec`'s state. -/
theorem fcvtzsWsSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPToFixed32_32Eq A) (hσ : fcvtzsWsSme.ctx σ u)
    (h : fcvtzsWsSme.Run P (fpFields2 d n) s σ o A) :
    o = .done { s.setX d (Wasm.i32TruncSatF32S (s.dregs n).toUInt32).toUInt64 with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 292)) := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixed32_32Eq at hA
    unfold Footprint.Run at h
    rw [fcvtzsWsSme_n0, show fcvtzsWsSme.vars (fpFields2 d n) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals wreg_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fcvtzsWsSme` has a path to `exec`'s state. -/
theorem fcvtzsWsSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {d n : Fin 32} {s : State}
    {σ : Sys} (hA : FPToFixed32_32Eq A) (hσ : fcvtzsWsSme.ctx σ u) :
    fcvtzsWsSme.Run P (fpFields2 d n) s σ
      (.done { s.setX d (Wasm.i32TruncSatF32S (s.dregs n).toUInt32).toUInt64 with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 292))) A := by
  without_info
    have := d.isLt
    have := n.isLt
    unfold FPToFixed32_32Eq at hA
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
      rw [fcvtzsWsSme_n0, show fcvtzsWsSme.vars (fpFields2 d n) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 n.val)) 1 (.bits 5 d.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | (apply Eq.symm; wreg_end; done)
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FCVTZS Wd, Sn` under `sme` agrees with `exec` for every register number and every
state, where `A` satisfies `FPToFixed32_32Eq`. -/
theorem fcvtzsWs_sme (P : Platform) (A : Abstract) (hA : FPToFixed32_32Eq A)
    (u : Unknown) (d n : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "FPSR"] fcvtzsWsSme
      (fpFields2 d n) (.fcvtzsWS d n) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fcvtzsWsSme, fpFields2, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fcvtzsWsSme.ctx_of σ u hσ
      exact ⟨⟨_, fcvtzsWsSme_bwd hA hc⟩, fun o h => ⟨_, fcvtzsWsSme_fwd hA hc h, by frame_end⟩⟩

set_option maxRecDepth 100000 in
/-- The footprint of `FCMP Sn, Sm` under the profile `sme`. -/
def fcmpSSme : Footprint := isla_trace% "tests/isla/sme/fcmp-s"

isla_nodes fcmpSSme

set_option maxRecDepth 100000 in
theorem fcmpSSme_n0 : fcmpSSme.trace = fcmpSSme.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx fcmpSSme (sme.sys .fp)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every path of `fcmpSSme` ends in `exec`'s state. -/
theorem fcmpSSme_fwd {P : Platform} {A : Abstract} {u : Unknown} {n m : Fin 32} {s : State}
    {σ : Sys} {o : Outcome} (hA : FPCompare32Eq A) (hσ : fcmpSSme.ctx σ u)
    (h : fcmpSSme.Run P (fcmpFields n m) s σ o A) :
    o = .done { s.fcmpS (s.dregs n).toUInt32 (s.dregs m).toUInt32 with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 272)) := by
  without_info
    have := n.isLt
    have := m.isLt
    unfold FPCompare32Eq at hA
    unfold Footprint.Run at h
    rw [fcmpSSme_n0, show fcmpSSme.vars (fcmpFields n m) =
      Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val) from rfl] at h
    fp_fwd h using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals flags32_end

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `fcmpSSme` has a path to `exec`'s state. -/
theorem fcmpSSme_bwd {P : Platform} {A : Abstract} {u : Unknown} {n m : Fin 32} {s : State}
    {σ : Sys} (hA : FPCompare32Eq A) (hσ : fcmpSSme.ctx σ u) :
    fcmpSSme.Run P (fcmpFields n m) s σ
      (.done { s.fcmpS (s.dregs n).toUInt32 (s.dregs m).toUInt32 with pc := s.pc + 4 }
      ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 272))) A := by
  without_info
    have := n.isLt
    have := m.isLt
    unfold FPCompare32Eq at hA
    all_goals
      unfold Footprint.Run
      rw [fcmpSSme_n0, show fcmpSSme.vars (fcmpFields n m) =
        Vars.set (Vars.set (fun _ => none) 0 (.bits 5 m.val)) 1 (.bits 5 n.val) from rfl]
      fp_bwd using mem_omega with [Opaque.out hσ, hA, hi_lo_mod32, low32_eq, u32_mod, ofNat_u32, zero_u32, schain_eq, wchain_eq]
    all_goals first
      | (apply Eq.symm; flags32_end; done)
      | fp_side hσ [hA, hi_lo_mod32, low32_eq, u32_mod, schain_eq, fcmpNZCV32_lt]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The trace of `FCMP Sn, Sm` under `sme` agrees with `exec` for every register number and every
state, where `A` satisfies `FPCompare32Eq`. -/
theorem fcmpS_sme (P : Platform) (A : Abstract) (hA : FPCompare32Eq A)
    (u : Unknown) (n m : Fin 32) (s : State) :
    AgreesAll P A (sme.sys .fp u) ["SEE", "__BranchTaken", "FPSR"] fcmpSSme
      (fcmpFields n m) (.fcmpS n m) s := by
  without_info
    refine ⟨by decide, by decide, decode_word ?_, fun σ hσ s' hs => ?_⟩
    · simp only [Opcode.word, Opcode.wordFrom, fcmpSSme, fcmpFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    · simp only [exec, Option.some.injEq] at hs
      subst hs
      have hc := fcmpSSme.ctx_of σ u hσ
      exact ⟨⟨_, fcmpSSme_bwd hA hc⟩, fun o h => ⟨_, fcmpSSme_fwd hA hc h, by frame_end⟩⟩

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.fmovSw_sme
#print axioms TestSupport.A64.Isla.fmovWs_sme
#print axioms TestSupport.A64.Isla.faddS_sme
#print axioms TestSupport.A64.Isla.fsubS_sme
#print axioms TestSupport.A64.Isla.fmulS_sme
#print axioms TestSupport.A64.Isla.fdivS_sme
#print axioms TestSupport.A64.Isla.fsqrtS_sme
#print axioms TestSupport.A64.Isla.frintnS_sme
#print axioms TestSupport.A64.Isla.ucvtfSx_sme
#print axioms TestSupport.A64.Isla.scvtfSw_sme
#print axioms TestSupport.A64.Isla.fcvtzuXs_sme
#print axioms TestSupport.A64.Isla.fcvtzsWs_sme
#print axioms TestSupport.A64.Isla.fcmpS_sme
