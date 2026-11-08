import Armv9fp
import Interpreter.Wasm.Float

/-!
The definitions and lemmas that the proofs of the floating-point equations share, over Sail's Lean
translation of the Armv9.4-A model (`translate.sh` with `fp-slice.isail`, `--lean-real-numbers`,
edited by `fix-output.sh`): lemmas that run the translation's monad, the state hypothesis `Hyp`,
the fields of FPCR 0x02000000, the comparisons of the enumerations, the tactic `sail_simp`, the
unpacking of a binary64 word, the processing of NaNs, and the two loops of FPRoundBase__1.

The Lean back end evaluates both operands of `&&` and `||`, where Sail and the IR that Isla runs
evaluate the second only when the first does not decide the result.  On the paths of FPAdd, FPSub,
FPMul, FPDiv, FPSqrt, and FixedToFP, the eagerly evaluated operands are `HaveAltFP`,
`UsingAArch32`, `HaveSME`, `InStreamingMode`, reads of PSTATE, and `IsFullA64Enabled`, the last in
FPProcessException and in FPRoundBase__1's test of a trapped underflow.  `ro_fullA64` states that
`IsFullA64Enabled` returns without an error and changes nothing but the choice state from every
state whose register map satisfies `FARegs`, whatever the features, PSTATE, and the system
registers hold, and `bind_fa` lets `sail_simp` step over the call.  The other operands read
FeatureImpl and PSTATE only, which the proofs check as they unfold them.

The proofs keep `trivialChoiceSource`, the instance `Real.instInhabited`, and `unspecReal`, the
real that `undefined_real` returns, irreducible, so that the unspecified values that the model
draws stay terms that no step evaluates.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7

attribute [local irreducible] trivialChoiceSource Real.instInhabited

abbrev State := SequentialState RegisterType trivialChoiceSource

theorem bind_readReg {β} (r : Register) (f : RegisterType r → SailM β) (s : State) :
    (readReg r >>= f).run s = (match s.regs.get? r with
      | some v => (f v).run s
      | none => .error .Unreachable s) := by
  cases h : s.regs.get? r <;>
    simp [readReg, PreSail.readReg, EStateM.run, bind, EStateM.bind, get, getThe,
      MonadStateOf.get, EStateM.get, h, pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw,
      EStateM.throw]

theorem run_readReg (r : Register) (s : State) :
    (readReg r).run s = (match s.regs.get? r with
      | some v => .ok v s
      | none => .error .Unreachable s) := by
  cases h : s.regs.get? r <;>
    simp [readReg, PreSail.readReg, EStateM.run, bind, EStateM.bind, get, getThe,
      MonadStateOf.get, EStateM.get, h, pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw,
      EStateM.throw]

def setReg (s : State) (r : Register) (v : RegisterType r) : State :=
  { s with regs := s.regs.insert r v }

@[simp] theorem setReg_regs (s : State) (r : Register) (v : RegisterType r) :
    (setReg s r v).regs = s.regs.insert r v := rfl

theorem bind_writeReg {β} (r : Register) (v : RegisterType r) (f : PUnit → SailM β) (s : State) :
    (writeReg r v >>= f).run s = (f ()).run (setReg s r v) := rfl

theorem run_writeReg (r : Register) (v : RegisterType r) (s : State) :
    (writeReg r v).run s = .ok () (setReg s r v) := rfl

/-- The state after an unspecified value of the primitive type `p`. -/
def bump (p : Sail.Primitive) (s : State) : State :=
  { s with choiceState := trivialChoiceSource.nextState p s.choiceState }

@[simp] theorem bump_regs (p : Sail.Primitive) (s : State) : (bump p s).regs = s.regs := rfl

theorem bind_choose {β} (p : Sail.Primitive) (f : p.reflect → SailM β) (s : State) :
    (PreSail.choose p >>= f).run s =
      (f (trivialChoiceSource.choose p s.choiceState)).run (bump p s) := rfl

theorem bind_run {α β} {x : SailM α} {f : α → SailM β} {s s' : State} {a : α}
    (h : x.run s = .ok a s') : (x >>= f).run s = (f a).run s' := by
  simp only [EStateM.run, bind, EStateM.bind] at h ⊢
  rw [h]

@[simp] theorem run_pure {α} (a : α) (s : State) : (pure a : SailM α).run s = .ok a s := rfl

@[simp] theorem assert_true (m : String) : (assert true m : SailM Unit) = pure () := rfl

/-- The value of FPCR that the startup writes. -/
abbrev fpcrV : BitVec 64 := 0x02000000#64

/-- The state hypothesis: the register map holds FeatureImpl, PSTATE, FPSR, SCR_EL3, HCR_EL2, and
SMCR_EL1 to SMCR_EL3, at least one of FEAT_AA64EL0 to FEAT_AA64EL3 is implemented, and PSTATE.nRW
is 0.  The other features, among them FEAT_AFP, FEAT_SME, and FEAT_SME_FA64, the other fields of
PSTATE, and the values of FPSR and of the five system registers are free. -/
structure Hyp (R : Std.ExtDHashMap Register RegisterType) (fi : Vector Bool 259) (ps : ProcState)
    (fpsr : BitVec 64) : Prop where
  hfi : R.get? Register.FeatureImpl = some fi
  aa64 : (((fi[num_of_Feature .FEAT_AA64EL0]! || fi[num_of_Feature .FEAT_AA64EL1]!) ||
    fi[num_of_Feature .FEAT_AA64EL2]!) || fi[num_of_Feature .FEAT_AA64EL3]!) = true
  hps : R.get? Register.PSTATE = some ps
  nrw : ps.nRW = 0#1
  hfpsr : R.get? Register.FPSR = some fpsr
  scr3 : (R.get? Register.SCR_EL3).isSome = true
  hcr2 : (R.get? Register.HCR_EL2).isSome = true
  smcr1 : (R.get? Register.SMCR_EL1).isSome = true
  smcr2 : (R.get? Register.SMCR_EL2).isSome = true
  smcr3 : (R.get? Register.SMCR_EL3).isSome = true

theorem get?_insert_ne {R : Std.ExtDHashMap Register RegisterType} {k r : Register}
    {v : RegisterType k} (h : (k == r) = false) : (R.insert k v).get? r = R.get? r := by
  simp [Std.ExtDHashMap.get?_insert, h]

/-- The registers that IsFullA64Enabled reads, with an implemented AArch64 exception level. -/
structure FARegs (R : Std.ExtDHashMap Register RegisterType) : Prop where
  hfi : ∃ fi : Vector Bool 259, R.get? Register.FeatureImpl = some fi ∧
    (((fi[num_of_Feature .FEAT_AA64EL0]! || fi[num_of_Feature .FEAT_AA64EL1]!) ||
      fi[num_of_Feature .FEAT_AA64EL2]!) || fi[num_of_Feature .FEAT_AA64EL3]!) = true
  ps : (R.get? Register.PSTATE).isSome = true
  scr3 : (R.get? Register.SCR_EL3).isSome = true
  hcr2 : (R.get? Register.HCR_EL2).isSome = true
  smcr1 : (R.get? Register.SMCR_EL1).isSome = true
  smcr2 : (R.get? Register.SMCR_EL2).isSome = true
  smcr3 : (R.get? Register.SMCR_EL3).isSome = true

/-- `m` returns a value that satisfies `P`, without an error, and changes nothing but the choice
state, from every state whose register map satisfies `FARegs`. -/
structure ROP {α} (P : α → Prop) (m : SailM α) : Prop where
  run : ∀ s : State, FARegs s.regs → ∃ v c, P v ∧ m.run s = .ok v { s with choiceState := c }

abbrev RO {α} (m : SailM α) : Prop := ROP (fun _ => True) m

/-- The same for a computation of `SailME`, which may end by `SailME.throw` but not by an error. -/
abbrev ROE {ε α} (m : SailME ε α) : Prop :=
  ROP (fun r => ∀ e, r ≠ .error (.inl e)) (ExceptT.run m)

theorem ROP.pure' {α} {P : α → Prop} {a : α} (h : P a) : ROP P (pure a) :=
  ⟨fun s _ => ⟨a, s.choiceState, h, rfl⟩⟩

theorem ROP.bind' {α β} {Q : α → Prop} {P : β → Prop} {x : SailM α} {f : α → SailM β}
    (hx : ROP Q x) (hf : ∀ a, Q a → ROP P (f a)) : ROP P (x >>= f) := by
  refine ⟨fun s hs => ?_⟩
  obtain ⟨v, c, hq, h⟩ := hx.run s hs
  obtain ⟨w, c', hp, h'⟩ := (hf v hq).run { s with choiceState := c } hs
  exact ⟨w, c', hp, by rw [bind_run h, h']⟩

theorem ROP.ite' {α} {P : α → Prop} {c : Prop} [Decidable c] {a b : SailM α}
    (ha : ROP P a) (hb : ROP P b) : ROP P (if c then a else b) := by
  split <;> assumption

theorem RO.readReg' {r : Register} (hr : ∀ R, FARegs R → (R.get? r).isSome = true) :
    RO (readReg r) := by
  refine ⟨fun s hs => ?_⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hr _ hs)
  exact ⟨v, s.choiceState, trivial, by rw [run_readReg, hv]⟩

theorem RO.choose' (p : Sail.Primitive) : RO (PreSail.choose p : SailM p.reflect) :=
  ⟨fun s _ => ⟨_, _, trivial, rfl⟩⟩

theorem ro_ubool : RO (undefined_bool ()) := RO.choose' .bool
theorem ro_ubv (n : Nat) : RO (undefined_bitvector n) := RO.choose' (.bitvector n)
theorem ro_uint : RO (undefined_int ()) := RO.choose' .int

theorem ROE.lift' {ε α} {x : SailM α} (hx : RO x) : ROE (liftM x : SailME ε α) := by
  refine ⟨fun s hs => ?_⟩
  obtain ⟨v, c, -, h⟩ := hx.run s hs
  refine ⟨.ok v, c, ⟨(by intro e he; cases he), ?_⟩⟩
  show (ExceptT.lift x).run.run s = _
  simp only [ExceptT.run_lift, map_eq_pure_bind]
  rw [bind_run h]
  rfl

theorem ROE.bind' {ε α β} {x : SailME ε α} {f : α → SailME ε β}
    (hx : ROE x) (hf : ∀ a, ROE (f a)) : ROE (x >>= f) := by
  rw [ROE, ExceptT.run_bind]
  refine ROP.bind' hx ?_
  intro r hr
  match r, hr with
  | .ok a, _ => exact hf a
  | .error (.inr _), _ => exact ROP.pure' (fun e' h => nomatch h)
  | .error (.inl e), hr => exact absurd rfl (hr e)

theorem ROE.pure' {ε α} (a : α) : ROE (pure a : SailME ε α) :=
  ROP.pure' (fun e h => nomatch h)

theorem ROE.throw' {α β} (e : α) : ROE (SailME.throw e : SailME α β) :=
  ROP.pure' (fun e h => nomatch h)

theorem ROE.ite' {ε α} {c : Prop} [Decidable c] {a b : SailME ε α}
    (ha : ROE a) (hb : ROE b) : ROE (if c then a else b) := by
  split <;> assumption

theorem RO.sailME_run {α} {m : SailME α α} (hm : ROE m) : RO (SailME.run m) := by
  unfold SailME.run PreSail.PreSailME.run
  refine ROP.bind' hm ?_
  intro r hr
  match r, hr with
  | .ok a, _ => exact ROP.pure' trivial
  | .error (.inr _), _ => exact ROP.pure' trivial
  | .error (.inl e), hr => exact absurd rfl (hr e)

theorem ro_feat (f : Feature) : RO (IsFeatureImplemented f) := by
  unfold IsFeatureImplemented
  refine ROP.bind' (RO.readReg' fun R h => ?_) fun _ _ => ROP.pure' trivial
  obtain ⟨fi, hfi, -⟩ := h.hfi
  simp [hfi]

theorem ro_ps : RO (readReg Register.PSTATE) := RO.readReg' fun _ h => h.ps
theorem ro_scr3 : RO (readReg Register.SCR_EL3) := RO.readReg' fun _ h => h.scr3
theorem ro_hcr2 : RO (readReg Register.HCR_EL2) := RO.readReg' fun _ h => h.hcr2
theorem ro_smcr1 : RO (readReg Register.SMCR_EL1) := RO.readReg' fun _ h => h.smcr1
theorem ro_smcr2 : RO (readReg Register.SMCR_EL2) := RO.readReg' fun _ h => h.smcr2
theorem ro_smcr3 : RO (readReg Register.SMCR_EL3) := RO.readReg' fun _ h => h.smcr3

theorem rop_aa64 : ROP (· = true) (HaveAArch64 ()) := by
  refine ⟨fun s hs => ?_⟩
  obtain ⟨fi, hfi, haa⟩ := hs.hfi
  refine ⟨true, s.choiceState, rfl, ?_⟩
  simp only [HaveAArch64, IsFeatureImplemented, bind_assoc, pure_bind,
    bind_readReg (r := Register.FeatureImpl), hfi, run_pure, haa]

theorem ROP.bind_aa64 {β} {P : β → Prop} {f : Bool → SailM β} (hf : ROP P (f true)) :
    ROP P (HaveAArch64 () >>= f) :=
  ROP.bind' rop_aa64 fun a ha => ha ▸ hf

theorem bv2_cases (x : BitVec 2) : x = 0#2 ∨ x = 1#2 ∨ x = 2#2 ∨ x = 3#2 := by
  have h := x.isLt
  have : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 ∨ x.toNat = 3 := by omega
  rcases this with h | h | h | h
  · exact .inl (BitVec.eq_of_toNat_eq (by simp [h]))
  · exact .inr (.inl (BitVec.eq_of_toNat_eq (by simp [h])))
  · exact .inr (.inr (.inl (BitVec.eq_of_toNat_eq (by simp [h]))))
  · exact .inr (.inr (.inr (BitVec.eq_of_toNat_eq (by simp [h]))))

open Lean Elab Tactic in
/-- Closes the goal with the first of the terms that `exact` accepts. -/
elab "ro_try" "[" ts:term,* "]" : tactic => do
  for t in ts.getElems do
    let st ← saveState
    try
      evalTactic (← `(tactic| exact $t))
      return
    catch _ => st.restore
  throwError "ro_try: no term applies"

/-- Proves `ROP P m` by the structure of `m`, with the lemmas `ts` for called functions. -/
macro "ro_auto" "[" ts:term,* "]" : tactic => `(tactic| repeat' (first
  | ro_try [$ts,*]
  | exact ROP.pure' trivial
  | exact ROE.pure' _
  | exact ROE.throw' _
  | exact ro_ubool | exact ro_ubv _ | exact ro_uint
  | exact ro_feat _
  | exact ro_ps | exact ro_scr3 | exact ro_hcr2 | exact ro_smcr1 | exact ro_smcr2
  | exact ro_smcr3
  | apply RO.sailME_run
  | apply ROE.lift'
  | apply ROE.ite'
  | apply ROE.bind'
  | apply ROP.bind_aa64
  | apply ROP.ite'
  | refine ROP.bind' (Q := fun _ => True) ?_ fun _ _ => ?_
  | intro _
  | (simp only [HaveEL, HaveAArch32EL, assert_true, pure_bind, Bool.not_true, Bool.not_false,
      Bool.false_eq_true, ↓reduceIte, Bool.true_and, Bool.and_true, Bool.false_or, Bool.or_false,
      __UNKNOWN_boolean, ImpDefBool])
  | dsimp only))

theorem ro_scr : RO (SCR_GEN_read ()) := by
  unfold SCR_GEN_read
  ro_auto []

theorem ro_isSecureBelow : RO (IsSecureBelowEL3 ()) := by
  unfold IsSecureBelowEL3
  ro_auto [ro_scr]

theorem ro_elUsing2 : RO (ELUsingAArch32 EL2) := by
  unfold ELUsingAArch32 ELStateUsingAArch32 ELStateUsingAArch32K
  simp only [HaveAArch32EL, EL0, EL2, BitVec.reduceBEq, Bool.not_false, ↓reduceIte, pure_bind,
    assert_true, bind_assoc]
  ro_auto [ro_isSecureBelow]

theorem ro_elUsing3 : RO (ELUsingAArch32 EL3) := by
  unfold ELUsingAArch32 ELStateUsingAArch32 ELStateUsingAArch32K
  simp only [HaveAArch32EL, EL0, EL3, BitVec.reduceBEq, Bool.not_false, ↓reduceIte, pure_bind,
    assert_true, bind_assoc]
  ro_auto [ro_isSecureBelow]

theorem ro_isSecureEL2 : RO (IsSecureEL2Enabled ()) := by
  unfold IsSecureEL2Enabled SecureOnlyImplementation
  ro_auto [ro_elUsing3]

theorem ro_el2Enabled : RO (EL2Enabled ()) := by
  unfold EL2Enabled
  ro_auto [ro_scr, ro_isSecureEL2]

theorem ro_elIsInHost (el : BitVec 2) : RO (ELIsInHost el) := by
  rcases bv2_cases el with rfl | rfl | rfl | rfl <;>
    simp only [ELIsInHost, EL0, EL1, EL2, EL3, BitVec.reduceBEq, ↓reduceIte, Bool.false_eq_true] <;>
    ro_auto [ro_elUsing2, ro_el2Enabled]

theorem ro_isInHost : RO (IsInHost ()) := by
  unfold IsInHost
  ro_auto [ro_elIsInHost _]

theorem ro_fullA64 : RO (IsFullA64Enabled ()) := by
  unfold IsFullA64Enabled HaveSMEFullA64
  ro_auto [ro_isInHost, ro_el2Enabled]


theorem Hyp.fa {R : Std.ExtDHashMap Register RegisterType} {fi : Vector Bool 259} {ps : ProcState}
    {fpsr : BitVec 64} (h : Hyp R fi ps fpsr) : FARegs R :=
  ⟨⟨fi, h.hfi, h.aa64⟩, by simp [h.hps], h.scr3, h.hcr2, h.smcr1, h.smcr2, h.smcr3⟩

theorem faRegs_insert (R : Std.ExtDHashMap Register RegisterType) (v : BitVec 64) :
    FARegs (R.insert Register.FPSR v) = FARegs R := by
  have e : ∀ r, (Register.FPSR == r) = false → (R.insert Register.FPSR v).get? r = R.get? r :=
    fun _ h => get?_insert_ne h
  have e1 := e .FeatureImpl (by decide)
  have e2 := e .PSTATE (by decide)
  have e3 := e .SCR_EL3 (by decide)
  have e4 := e .HCR_EL2 (by decide)
  have e5 := e .SMCR_EL1 (by decide)
  have e6 := e .SMCR_EL2 (by decide)
  have e7 := e .SMCR_EL3 (by decide)
  apply propext
  constructor
  · rintro ⟨⟨fi, h1, h2⟩, h3, h4, h5, h6, h7, h8⟩
    rw [e1] at h1
    rw [e2] at h3
    rw [e3] at h4
    rw [e4] at h5
    rw [e5] at h6
    rw [e6] at h7
    rw [e7] at h8
    exact ⟨⟨fi, h1, h2⟩, h3, h4, h5, h6, h7, h8⟩
  · rintro ⟨⟨fi, h1, h2⟩, h3, h4, h5, h6, h7, h8⟩
    refine ⟨⟨fi, ?_, h2⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [e1]; exact h1
    · rw [e2]; exact h3
    · rw [e3]; exact h4
    · rw [e4]; exact h5
    · rw [e5]; exact h6
    · rw [e6]; exact h7
    · rw [e7]; exact h8

/-- The value and the choice state that IsFullA64Enabled leaves from `s`. -/
noncomputable def faV (s : State) : Bool :=
  match (IsFullA64Enabled ()).run s with
  | .ok v _ => v
  | .error _ _ => false

noncomputable def faC (s : State) : trivialChoiceSource.α :=
  match (IsFullA64Enabled ()).run s with
  | .ok _ s' => s'.choiceState
  | .error _ s' => s'.choiceState

noncomputable def faS (s : State) : State := { s with choiceState := faC s }

@[simp] theorem faS_regs (s : State) : (faS s).regs = s.regs := rfl

theorem run_fa (s : State) (h : FARegs s.regs) :
    (IsFullA64Enabled ()).run s = .ok (faV s) (faS s) := by
  obtain ⟨v, c, -, hr⟩ := ro_fullA64.run s h
  simp only [faV, faC, faS, hr]

/-- `m.run s`, under a name that `sail_simp` does not unfold. -/
@[irreducible] def stuckRun {β} (m : SailM β) (s : State) := m.run s

open Classical in
/-- The step of `sail_simp` over IsFullA64Enabled.  The rewrite is unconditional, so that `sail_simp`
needs no discharger: it rewrites the condition `FARegs s.regs` to `True` with the hypotheses that it
is given, and a call from a state that it cannot show to satisfy `FARegs` stays as `stuckRun`. -/
theorem bind_fa {β} (f : Bool → SailM β) (s : State) :
    (IsFullA64Enabled () >>= f).run s =
      if FARegs s.regs then (f (faV s)).run (faS s) else stuckRun (IsFullA64Enabled () >>= f) s := by
  by_cases h : FARegs s.regs
  · rw [if_pos h, bind_run (run_fa s h)]
  · rw [if_neg h]; unfold stuckRun; rfl

/-- The real that `undefined_real` returns: `default` in the translation, and an opaque constant in
the variant that `check.sh` also checks.  The proofs keep it irreducible. -/
noncomputable def unspecReal : ℝ :=
  match (undefined_real () : SailM ℝ).run default with
  | .ok v _ => v
  | .error _ _ => 0

/-- `undefined_real` returns `unspecReal` and changes no state. -/
theorem bind_undefined_real {β} (f : ℝ → SailM β) (s : State) :
    (undefined_real () >>= f).run s = (f unspecReal).run s := rfl

attribute [local irreducible] unspecReal

theorem fpcr_AH : _get_FPCRType_AH fpcrV = 0#1 := by decide
theorem fpcr_DN : _get_FPCRType_DN fpcrV = 1#1 := by decide
theorem fpcr_FZ : _get_FPCRType_FZ fpcrV = 0#1 := by decide
theorem fpcr_FZ16 : _get_FPCRType_FZ16 fpcrV = 0#1 := by decide
theorem fpcr_FIZ : _get_FPCRType_FIZ fpcrV = 0#1 := by decide
theorem fpcr_AHP : _get_FPCRType_AHP fpcrV = 0#1 := by decide
theorem fpcr_UFE : _get_FPCRType_UFE fpcrV = 0#1 := by decide
theorem fpcr_RMode : _get_FPCRType_RMode fpcrV = 0#2 := by decide
theorem fpcr_clear26 : Sail.BitVec.updateSubrange fpcrV 26 26 0#1 = fpcrV := by decide
theorem en0 : (BitVec.join1 [BitVec.access fpcrV ((0 : Int) + 8).toNat] == 1#1) = false := by decide
theorem en1 : (BitVec.join1 [BitVec.access fpcrV ((1 : Int) + 8).toNat] == 1#1) = false := by decide
theorem en2 : (BitVec.join1 [BitVec.access fpcrV ((2 : Int) + 8).toNat] == 1#1) = false := by decide
theorem en3 : (BitVec.join1 [BitVec.access fpcrV ((3 : Int) + 8).toNat] == 1#1) = false := by decide
theorem en4 : (BitVec.join1 [BitVec.access fpcrV ((4 : Int) + 8).toNat] == 1#1) = false := by decide
theorem en7 : (BitVec.join1 [BitVec.access fpcrV ((7 : Int) + 8).toNat] == 1#1) = false := by decide

theorem ftb_Zero_Zero : (FPType.FPType_Zero == FPType.FPType_Zero) = true := rfl
theorem ftb_Zero_Denormal : (FPType.FPType_Zero == FPType.FPType_Denormal) = false := rfl
theorem ftb_Zero_Nonzero : (FPType.FPType_Zero == FPType.FPType_Nonzero) = false := rfl
theorem ftb_Zero_Infinity : (FPType.FPType_Zero == FPType.FPType_Infinity) = false := rfl
theorem ftb_Zero_QNaN : (FPType.FPType_Zero == FPType.FPType_QNaN) = false := rfl
theorem ftb_Zero_SNaN : (FPType.FPType_Zero == FPType.FPType_SNaN) = false := rfl
theorem ftb_Denormal_Zero : (FPType.FPType_Denormal == FPType.FPType_Zero) = false := rfl
theorem ftb_Denormal_Denormal : (FPType.FPType_Denormal == FPType.FPType_Denormal) = true := rfl
theorem ftb_Denormal_Nonzero : (FPType.FPType_Denormal == FPType.FPType_Nonzero) = false := rfl
theorem ftb_Denormal_Infinity : (FPType.FPType_Denormal == FPType.FPType_Infinity) = false := rfl
theorem ftb_Denormal_QNaN : (FPType.FPType_Denormal == FPType.FPType_QNaN) = false := rfl
theorem ftb_Denormal_SNaN : (FPType.FPType_Denormal == FPType.FPType_SNaN) = false := rfl
theorem ftb_Nonzero_Zero : (FPType.FPType_Nonzero == FPType.FPType_Zero) = false := rfl
theorem ftb_Nonzero_Denormal : (FPType.FPType_Nonzero == FPType.FPType_Denormal) = false := rfl
theorem ftb_Nonzero_Nonzero : (FPType.FPType_Nonzero == FPType.FPType_Nonzero) = true := rfl
theorem ftb_Nonzero_Infinity : (FPType.FPType_Nonzero == FPType.FPType_Infinity) = false := rfl
theorem ftb_Nonzero_QNaN : (FPType.FPType_Nonzero == FPType.FPType_QNaN) = false := rfl
theorem ftb_Nonzero_SNaN : (FPType.FPType_Nonzero == FPType.FPType_SNaN) = false := rfl
theorem ftb_Infinity_Zero : (FPType.FPType_Infinity == FPType.FPType_Zero) = false := rfl
theorem ftb_Infinity_Denormal : (FPType.FPType_Infinity == FPType.FPType_Denormal) = false := rfl
theorem ftb_Infinity_Nonzero : (FPType.FPType_Infinity == FPType.FPType_Nonzero) = false := rfl
theorem ftb_Infinity_Infinity : (FPType.FPType_Infinity == FPType.FPType_Infinity) = true := rfl
theorem ftb_Infinity_QNaN : (FPType.FPType_Infinity == FPType.FPType_QNaN) = false := rfl
theorem ftb_Infinity_SNaN : (FPType.FPType_Infinity == FPType.FPType_SNaN) = false := rfl
theorem ftb_QNaN_Zero : (FPType.FPType_QNaN == FPType.FPType_Zero) = false := rfl
theorem ftb_QNaN_Denormal : (FPType.FPType_QNaN == FPType.FPType_Denormal) = false := rfl
theorem ftb_QNaN_Nonzero : (FPType.FPType_QNaN == FPType.FPType_Nonzero) = false := rfl
theorem ftb_QNaN_Infinity : (FPType.FPType_QNaN == FPType.FPType_Infinity) = false := rfl
theorem ftb_QNaN_QNaN : (FPType.FPType_QNaN == FPType.FPType_QNaN) = true := rfl
theorem ftb_QNaN_SNaN : (FPType.FPType_QNaN == FPType.FPType_SNaN) = false := rfl
theorem ftb_SNaN_Zero : (FPType.FPType_SNaN == FPType.FPType_Zero) = false := rfl
theorem ftb_SNaN_Denormal : (FPType.FPType_SNaN == FPType.FPType_Denormal) = false := rfl
theorem ftb_SNaN_Nonzero : (FPType.FPType_SNaN == FPType.FPType_Nonzero) = false := rfl
theorem ftb_SNaN_Infinity : (FPType.FPType_SNaN == FPType.FPType_Infinity) = false := rfl
theorem ftb_SNaN_QNaN : (FPType.FPType_SNaN == FPType.FPType_QNaN) = false := rfl
theorem ftb_SNaN_SNaN : (FPType.FPType_SNaN == FPType.FPType_SNaN) = true := rfl
theorem frb_TIEEVEN_TIEEVEN :
    (FPRounding.FPRounding_TIEEVEN == FPRounding.FPRounding_TIEEVEN) = true := rfl
theorem frb_TIEEVEN_POSINF :
    (FPRounding.FPRounding_TIEEVEN == FPRounding.FPRounding_POSINF) = false := rfl
theorem frb_TIEEVEN_NEGINF :
    (FPRounding.FPRounding_TIEEVEN == FPRounding.FPRounding_NEGINF) = false := rfl
theorem frb_TIEEVEN_ZERO :
    (FPRounding.FPRounding_TIEEVEN == FPRounding.FPRounding_ZERO) = false := rfl
theorem frb_TIEEVEN_TIEAWAY :
    (FPRounding.FPRounding_TIEEVEN == FPRounding.FPRounding_TIEAWAY) = false := rfl
theorem frb_TIEEVEN_ODD :
    (FPRounding.FPRounding_TIEEVEN == FPRounding.FPRounding_ODD) = false := rfl
theorem frb_POSINF_TIEEVEN :
    (FPRounding.FPRounding_POSINF == FPRounding.FPRounding_TIEEVEN) = false := rfl
theorem frb_POSINF_POSINF :
    (FPRounding.FPRounding_POSINF == FPRounding.FPRounding_POSINF) = true := rfl
theorem frb_POSINF_NEGINF :
    (FPRounding.FPRounding_POSINF == FPRounding.FPRounding_NEGINF) = false := rfl
theorem frb_POSINF_ZERO :
    (FPRounding.FPRounding_POSINF == FPRounding.FPRounding_ZERO) = false := rfl
theorem frb_POSINF_TIEAWAY :
    (FPRounding.FPRounding_POSINF == FPRounding.FPRounding_TIEAWAY) = false := rfl
theorem frb_POSINF_ODD : (FPRounding.FPRounding_POSINF == FPRounding.FPRounding_ODD) = false := rfl
theorem frb_NEGINF_TIEEVEN :
    (FPRounding.FPRounding_NEGINF == FPRounding.FPRounding_TIEEVEN) = false := rfl
theorem frb_NEGINF_POSINF :
    (FPRounding.FPRounding_NEGINF == FPRounding.FPRounding_POSINF) = false := rfl
theorem frb_NEGINF_NEGINF :
    (FPRounding.FPRounding_NEGINF == FPRounding.FPRounding_NEGINF) = true := rfl
theorem frb_NEGINF_ZERO :
    (FPRounding.FPRounding_NEGINF == FPRounding.FPRounding_ZERO) = false := rfl
theorem frb_NEGINF_TIEAWAY :
    (FPRounding.FPRounding_NEGINF == FPRounding.FPRounding_TIEAWAY) = false := rfl
theorem frb_NEGINF_ODD : (FPRounding.FPRounding_NEGINF == FPRounding.FPRounding_ODD) = false := rfl
theorem frb_ZERO_TIEEVEN :
    (FPRounding.FPRounding_ZERO == FPRounding.FPRounding_TIEEVEN) = false := rfl
theorem frb_ZERO_POSINF :
    (FPRounding.FPRounding_ZERO == FPRounding.FPRounding_POSINF) = false := rfl
theorem frb_ZERO_NEGINF :
    (FPRounding.FPRounding_ZERO == FPRounding.FPRounding_NEGINF) = false := rfl
theorem frb_ZERO_ZERO : (FPRounding.FPRounding_ZERO == FPRounding.FPRounding_ZERO) = true := rfl
theorem frb_ZERO_TIEAWAY :
    (FPRounding.FPRounding_ZERO == FPRounding.FPRounding_TIEAWAY) = false := rfl
theorem frb_ZERO_ODD : (FPRounding.FPRounding_ZERO == FPRounding.FPRounding_ODD) = false := rfl
theorem frb_TIEAWAY_TIEEVEN :
    (FPRounding.FPRounding_TIEAWAY == FPRounding.FPRounding_TIEEVEN) = false := rfl
theorem frb_TIEAWAY_POSINF :
    (FPRounding.FPRounding_TIEAWAY == FPRounding.FPRounding_POSINF) = false := rfl
theorem frb_TIEAWAY_NEGINF :
    (FPRounding.FPRounding_TIEAWAY == FPRounding.FPRounding_NEGINF) = false := rfl
theorem frb_TIEAWAY_ZERO :
    (FPRounding.FPRounding_TIEAWAY == FPRounding.FPRounding_ZERO) = false := rfl
theorem frb_TIEAWAY_TIEAWAY :
    (FPRounding.FPRounding_TIEAWAY == FPRounding.FPRounding_TIEAWAY) = true := rfl
theorem frb_TIEAWAY_ODD :
    (FPRounding.FPRounding_TIEAWAY == FPRounding.FPRounding_ODD) = false := rfl
theorem frb_ODD_TIEEVEN :
    (FPRounding.FPRounding_ODD == FPRounding.FPRounding_TIEEVEN) = false := rfl
theorem frb_ODD_POSINF : (FPRounding.FPRounding_ODD == FPRounding.FPRounding_POSINF) = false := rfl
theorem frb_ODD_NEGINF : (FPRounding.FPRounding_ODD == FPRounding.FPRounding_NEGINF) = false := rfl
theorem frb_ODD_ZERO : (FPRounding.FPRounding_ODD == FPRounding.FPRounding_ZERO) = false := rfl
theorem frb_ODD_TIEAWAY :
    (FPRounding.FPRounding_ODD == FPRounding.FPRounding_TIEAWAY) = false := rfl
theorem frb_ODD_ODD : (FPRounding.FPRounding_ODD == FPRounding.FPRounding_ODD) = true := rfl

macro "sail_simp" "[" xs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp (config := {decide := true}) only [bind_assoc, pure_bind, run_pure, assert_true,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, Bool.true_or,
    Bool.or_true, Bool.false_or, Bool.or_false, Bool.and_true, Bool.true_and, Bool.and_false,
    Bool.false_and, BitVec.reduceBEq, BitVec.reduceBNe, Nat.reduceBEq, Nat.reduceBNe,
    Int.reduceBEq, Int.reduceBNe, Int.reduceToNat, beq_self_eq_true, Sail.BitVec.length,
    decide_true, decide_false,
    bump_regs, setReg_regs,
    bind_readReg (r := Register.FeatureImpl), bind_readReg (r := Register.PSTATE),
    bind_readReg (r := Register.FPSR), run_readReg (r := Register.FPSR),
    bind_writeReg (r := Register.FPSR), run_writeReg (r := Register.FPSR),
    Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self,
    SailME.run, PreSail.PreSailME.run, liftM, monadLift, MonadLiftT.monadLift,
    MonadLift.monadLift, ExceptT.run_bind_lift, ExceptT.run_pure, ExceptT.run_bind,
    ExceptT.run_throw,
    ExceptT.run_lift, bind_map_left, SailME.throw, PreSail.PreSailME.throw,
    PreSail.undefined_bool, PreSail.undefined_bitvector, PreSail.undefined_int,
    bind_undefined_real, undefined_FPType, PreSail.internal_pick, bind_choose (p := .bool), bind_choose (p := .int),
    bind_choose (p := .bitvector _), bind_choose (p := .fin _),
    UsingAArch32, HaveAArch64, IsFeatureImplemented, HaveAArch32, HaveAltFP, HaveSME,
    InStreamingMode, bind_fa, faS_regs, faRegs_insert,
    fpcr_AH, fpcr_DN, fpcr_FZ, fpcr_FZ16, fpcr_FIZ, fpcr_AHP, fpcr_UFE, fpcr_RMode, fpcr_clear26,
    en0, en1, en2, en3, en4, en7,
    ftb_Zero_Zero, ftb_Zero_Denormal, ftb_Zero_Nonzero, ftb_Zero_Infinity, ftb_Zero_QNaN,
    ftb_Zero_SNaN, ftb_Denormal_Zero, ftb_Denormal_Denormal, ftb_Denormal_Nonzero,
    ftb_Denormal_Infinity, ftb_Denormal_QNaN, ftb_Denormal_SNaN, ftb_Nonzero_Zero,
    ftb_Nonzero_Denormal, ftb_Nonzero_Nonzero, ftb_Nonzero_Infinity, ftb_Nonzero_QNaN,
    ftb_Nonzero_SNaN, ftb_Infinity_Zero, ftb_Infinity_Denormal, ftb_Infinity_Nonzero,
    ftb_Infinity_Infinity, ftb_Infinity_QNaN, ftb_Infinity_SNaN, ftb_QNaN_Zero, ftb_QNaN_Denormal,
    ftb_QNaN_Nonzero, ftb_QNaN_Infinity, ftb_QNaN_QNaN, ftb_QNaN_SNaN, ftb_SNaN_Zero,
    ftb_SNaN_Denormal, ftb_SNaN_Nonzero, ftb_SNaN_Infinity, ftb_SNaN_QNaN, ftb_SNaN_SNaN,
    frb_TIEEVEN_TIEEVEN, frb_TIEEVEN_POSINF, frb_TIEEVEN_NEGINF, frb_TIEEVEN_ZERO,
    frb_TIEEVEN_TIEAWAY, frb_TIEEVEN_ODD, frb_POSINF_TIEEVEN, frb_POSINF_POSINF, frb_POSINF_NEGINF,
    frb_POSINF_ZERO, frb_POSINF_TIEAWAY, frb_POSINF_ODD, frb_NEGINF_TIEEVEN, frb_NEGINF_POSINF,
    frb_NEGINF_NEGINF, frb_NEGINF_ZERO, frb_NEGINF_TIEAWAY, frb_NEGINF_ODD, frb_ZERO_TIEEVEN,
    frb_ZERO_POSINF, frb_ZERO_NEGINF, frb_ZERO_ZERO, frb_ZERO_TIEAWAY, frb_ZERO_ODD,
    frb_TIEAWAY_TIEEVEN, frb_TIEAWAY_POSINF, frb_TIEAWAY_NEGINF, frb_TIEAWAY_ZERO,
    frb_TIEAWAY_TIEAWAY, frb_TIEAWAY_ODD, frb_ODD_TIEEVEN, frb_ODD_POSINF, frb_ODD_NEGINF,
    frb_ODD_ZERO, frb_ODD_TIEAWAY, frb_ODD_ODD,
    $xs,*])

variable {s : State} {fi : Vector Bool 259} {ps : ProcState} {fpsr : BitVec 64}

theorem ok_congr {α} {a b : α} {σ : State} (h : a = b) :
    (EStateM.Result.ok a σ : EStateM.Result (Error exception) State α) = .ok b σ := h ▸ rfl

structure Frame (s s' : State) : Prop where
  mem : s'.mem = s.mem
  tags : s'.tags = s.tags
  cyc : s'.cycleCount = s.cycleCount
  out : s'.sailOutput = s.sailOutput

theorem Frame.trans {s₁ s₂ s₃ : State} (h₁ : Frame s₁ s₂) (h₂ : Frame s₂ s₃) : Frame s₁ s₃ :=
  ⟨h₂.mem.trans h₁.mem, h₂.tags.trans h₁.tags, h₂.cyc.trans h₁.cyc, h₂.out.trans h₁.out⟩

theorem exists_of_run {α} {x : SailM α} {s σ : State} {v : α}
    {R : Std.ExtDHashMap Register RegisterType} (h : x.run s = .ok v σ) (hr : σ.regs = R)
    (hf : Frame s σ) : ∃ s', x.run s = .ok v s' ∧ s'.regs = R ∧ Frame s s' := ⟨σ, h, hr, hf⟩

theorem exists_of_run' {α} {x : SailM α} {s0 s σ : State} {v : α}
    {R : Std.ExtDHashMap Register RegisterType} (h : x.run s0 = .ok v σ) (hr : σ.regs = R)
    (hf : Frame s σ) : ∃ s', x.run s0 = .ok v s' ∧ s'.regs = R ∧ Frame s s' := ⟨σ, h, hr, hf⟩

theorem ite_ok {α} (c : Prop) [Decidable c] (a b : α) (σ : State) :
    (if c then (EStateM.Result.ok a σ : EStateM.Result (Error exception) State α)
      else .ok b σ) = .ok (if c then a else b) σ := by
  split <;> rfl

theorem run_ite {α} (c : Prop) [Decidable c] (a b : SailM α) (σ : State) :
    (if c then a else b).run σ = if c then a.run σ else b.run σ := by
  split <;> rfl

theorem ite_bind' {α β} (c : Prop) [Decidable c] (a b : SailM α) (f : α → SailM β) :
    ((if c then a else b) >>= f) = if c then a >>= f else b >>= f := by
  split <;> rfl

/-- The fields of a binary64 word, as Talos computes them. -/
def ex (x : BitVec 64) : Nat := x.toNat / 2 ^ 52 % 2 ^ 11
def fr (x : BitVec 64) : Nat := x.toNat % 2 ^ 52
def sg (x : BitVec 64) : Bool := decide (2 ^ 63 ≤ x.toNat)

theorem isZero_eq {n : Nat} (y : BitVec n) : IsZero y = decide (y.toNat = 0) := by
  simp only [IsZero, Sail.BitVec.length, BitVec.zero]
  by_cases hy : y = 0#n
  · subst hy; simp
  · have : y.toNat ≠ 0 := fun h => hy (BitVec.eq_of_toNat_eq (by simpa using h))
    simp [hy, this]

theorem isOnes_eq {n : Nat} (y : BitVec n) : IsOnes y = decide (y.toNat = 2 ^ n - 1) := by
  simp only [IsOnes, sail_ones, Sail.BitVec.length, BitVec.zero]
  by_cases hy : y = BitVec.allOnes n
  · subst hy; simp
  · have : y.toNat ≠ 2 ^ n - 1 := fun h => hy (BitVec.eq_of_toNat_eq (by simpa using h))
    simp [hy, this]

theorem ex_eq (x : BitVec 64) : (Sail.BitVec.extractLsb x 62 52).toNat = ex x := by
  simp [Sail.BitVec.extractLsb, ex, BitVec.extractLsb_toNat, Nat.shiftRight_eq_div_pow]

theorem fr_eq (x : BitVec 64) : (Sail.BitVec.extractLsb x 51 0).toNat = fr x := by
  simp [Sail.BitVec.extractLsb, fr, BitVec.extractLsb_toNat]

theorem join1_bool (b : Bool) : BitVec.join1 [BitVec.ofBool b] = if b then 1#1 else 0#1 := by
  cases b <;> decide

theorem join1_access {w : Nat} (x : BitVec w) (i : Nat) (hi : i < w) :
    BitVec.join1 [BitVec.access x i] = (if x.toNat / 2 ^ i % 2 = 1 then 1#1 else 0#1) := by
  have hx : BitVec.access x i = BitVec.ofBool (decide (x.toNat / 2 ^ i % 2 = 1)) := by
    simp only [BitVec.access]
    congr 1
    rw [getElem!_pos x i hi, BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
  rw [hx, join1_bool]
  simp

def sgBit (x : BitVec 64) : BitVec 1 := if sg x then 1#1 else 0#1

theorem sign_join (x : BitVec 64) : BitVec.join1 [BitVec.access x 63] = sgBit x := by
  rw [join1_access x 63 (by decide)]
  have := x.isLt
  unfold sgBit sg
  by_cases h : 2 ^ 63 ≤ x.toNat
  · rw [if_pos (by omega), decide_eq_true h]; rfl
  · rw [if_neg (by omega), decide_eq_false h]; rfl

theorem qbit (x : BitVec 64) :
    (BitVec.join1 [BitVec.access (Sail.BitVec.extractLsb x 51 0) 51] == 1#1) =
      decide (2 ^ 51 ≤ fr x) := by
  rw [join1_access _ 51 (by decide), fr_eq]
  have : fr x < 2 ^ 52 := Nat.mod_lt _ (by decide)
  by_cases h : 2 ^ 51 ≤ fr x
  · rw [if_pos (by omega), decide_eq_true h]; rfl
  · rw [if_neg (by omega), decide_eq_false h]; rfl

theorem denorm_val (f : ℕ) :
    (2 : ℝ) ^ (-1022 : ℤ) * (((f : ℤ) : ℝ) * (2 : ℝ) ^ (-52 : ℤ)) =
      ((f : ℤ) : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) := by
  rw [show (-1074 : ℤ) = -1022 + -52 by norm_num, zpow_add₀ two_ne_zero]
  ring

theorem t_sign (x : BitVec 64) : Wasm.IEEE64.sign (UInt64.ofBitVec x) = sg x := by
  simp [Wasm.IEEE64.sign, sg]
theorem t_exp (x : BitVec 64) : Wasm.IEEE64.exponent (UInt64.ofBitVec x) = ex x := by
  simp [Wasm.IEEE64.exponent, ex]
theorem t_frac (x : BitVec 64) : Wasm.IEEE64.fraction (UInt64.ofBitVec x) = fr x := by
  simp [Wasm.IEEE64.fraction, fr]

theorem pow_normal (e : ℕ) (he : e ≠ 0) :
    (2 : ℝ) ^ ((e : ℤ) - 1023) = 4503599627370496 * 2 ^ (e - 1) * (2 ^ 1074)⁻¹ := by
  rw [show ((e : ℤ) - 1023) = ((e - 1 : ℕ) : ℤ) - 1074 + 52 by omega, zpow_add₀ two_ne_zero,
    zpow_sub₀ two_ne_zero]
  simp only [zpow_natCast, zpow_ofNat, div_eq_mul_inv]
  ring

theorem val_normal (e : ℕ) (he : e ≠ 0) (f : ℝ) :
    (2 : ℝ) ^ ((e : ℤ) - 1023) * (1 + f * (2 ^ 52)⁻¹) =
      (4503599627370496 + f) * 2 ^ (e - 1) * (2 ^ 1074)⁻¹ := by
  rw [pow_normal e he]
  ring

def ty64 (x : BitVec 64) : FPType :=
  if ex x = 0 then (if fr x = 0 then .FPType_Zero else .FPType_Denormal)
  else if ex x = 2047 then
    (if fr x = 0 then .FPType_Infinity else if 2 ^ 51 ≤ fr x then .FPType_QNaN else .FPType_SNaN)
  else .FPType_Nonzero

noncomputable def val64 (x : BitVec 64) : ℝ :=
  if ex x = 2047 then
    (if fr x = 0 then (if sg x then -(2 : ℝ) ^ (1000000 : ℤ) else (2 : ℝ) ^ (1000000 : ℤ)) else 0)
  else (Wasm.IEEE64.scaledValue (UInt64.ofBitVec x) : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)

theorem fpUnpack_run (x : BitVec 64) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPUnpack__1 x fpcrV true).run s = .ok (ty64 x, sgBit x, val64 x) s' ∧
      s'.regs = R ∧ Frame s s' := by
  subst hs
  refine exists_of_run (σ := ?σ) ?run ?regs ?frame
  case run =>
    sail_simp [FPUnpack__1, FPUnpackBase, FPUnpackBase__1, h.hfi, h.hps, h.nrw, h.aa64, ite_bind',
      run_ite, ite_ok, isZero_eq, isOnes_eq, ex_eq, fr_eq]
    refine ok_congr ?_
    rw [sign_join, qbit]
    have hx := x.isLt
    unfold ty64 sgBit val64
    simp only [Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, t_sign, t_exp, t_frac,
      mult_real, add_real, neg_real, to_real, real_power, denorm_val]
    have e2047 : (2 : ℕ) ^ 11 - 1 = 2047 := by norm_num
    rw [e2047]
    by_cases h0 : ex x = 0 <;> by_cases h1 : fr x = 0 <;> by_cases h2 : ex x = 2047 <;>
      by_cases h3 : sg x <;> by_cases h4 : 2 ^ 51 ≤ fr x <;>
      simp [h0, h1, h2, h3, h4]
    all_goals first | exact pow_normal _ h0 | exact val_normal _ h0 _
  case regs => rfl
  case frame => exact ⟨rfl, rfl, rfl, rfl⟩

def isNaNT (t : FPType) : Bool := t == .FPType_QNaN || t == .FPType_SNaN

/-- FPSR after an invalid-operation exception. -/
def ioc (v : BitVec 64) : BitVec 64 := Sail.BitVec.update v 0 (Bit 1#1)

set_option maxHeartbeats 2000000 in
theorem fpProcessNaNs_run (t1 t2 : FPType) (a b : BitVec 64) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPProcessNaNs__1 t1 t2 a b fpcrV true).run s =
      .ok (isNaNT t1 || isNaNT t2, if isNaNT t1 || isNaNT t2 then 0x7FF8000000000000#64 else 0#64) s' ∧
      s'.regs = (if t1 == .FPType_SNaN || t2 == .FPType_SNaN then R.insert .FPSR (ioc fpsr) else R) ∧
      Frame s s' := by
  subst hs
  cases t1 <;> cases t2 <;> (
    apply exists_of_run
    · sail_simp [FPProcessNaNs__1, FPProcessNaN__1, FPProcessException, h.hfi,
        h.hps, h.nrw, h.aa64, h.fa, h.hfpsr, isNaNT, ite_self]
      try sail_simp [FPDefaultNaN__1, h.hfi, h.hps, h.nrw, h.aa64, ite_self]
      rfl
    · sail_simp [ioc]
    · exact ⟨rfl, rfl, rfl, rfl⟩)

/-- The loop of a `whileFuelM` whose condition and body are pure. -/
def loopP {α} (c : α → Bool) (g : α → α) : Nat → α → α
  | 0, x => x
  | n + 1, x => if c x then loopP c g n (g x) else x

theorem loopP_of_exit {α} (c : α → Bool) (g : α → α) :
    ∀ (k fuel : ℕ) (x : α), k < fuel → (∀ i < k, c (g^[i] x) = true) → c (g^[k] x) = false →
      loopP c g fuel x = g^[k] x
  | _, 0, _, hk, _, _ => absurd hk (Nat.not_lt_zero _)
  | 0, f + 1, x, _, _, h0 => by
    have h0' : c x = false := h0
    simp only [loopP, h0']
    rfl
  | k + 1, f + 1, x, hk, hc, hk' => by
    have hx : c x = true := hc 0 (Nat.succ_pos _)
    simp only [loopP, hx, if_true]
    exact loopP_of_exit c g k f (g x) (by omega) (fun i hi => hc (i + 1) (by omega)) hk'

theorem whileFuelM_pure {m : Type → Type} [Monad m] [LawfulMonad m] {α} (c : α → Bool)
    (g : α → α) : ∀ (fuel : ℕ) (x : α),
      whileFuelM fuel (fun y => (pure (c y) : m Bool)) x (fun y => pure (g y)) =
        (pure (loopP c g fuel x) : m α)
  | 0, x => by simp [whileFuelM, whileFuelM.go, loopP]
  | n + 1, x => by
    have ih := whileFuelM_pure (m := m) c g n (g x)
    simp only [whileFuelM] at ih ⊢
    simp only [whileFuelM.go, pure_bind, loopP]
    split <;> simp_all

noncomputable def c1 (y : ℤ × ℝ) : Bool := lt_real y.2 1
noncomputable def g1 (y : ℤ × ℝ) : ℤ × ℝ := (y.1 - 1, mult_real y.2 2)
noncomputable def c2 (y : ℤ × ℝ) : Bool := gteq_real y.2 2
noncomputable def g2 (y : ℤ × ℝ) : ℤ × ℝ := (y.1 + 1, div_real y.2 2)

theorem g1_iter (i : ℕ) (e : ℤ) (m : ℝ) : g1^[i] (e, m) = (e - i, m * 2 ^ i) := by
  induction i generalizing e m with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply, show g1 (e, m) = (e - 1, m * 2) from rfl, ih]
    simp only [Prod.mk.injEq]; constructor
    · push_cast; ring
    · ring

theorem g2_iter (j : ℕ) (e : ℤ) (m : ℝ) : g2^[j] (e, m) = (e + j, m / 2 ^ j) := by
  induction j generalizing e m with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply, show g2 (e, m) = (e + 1, m / 2) from rfl, ih]
    simp only [Prod.mk.injEq]; constructor
    · push_cast; ring
    · rw [pow_succ]; field_simp

/-- The doubling loop of FPRoundBase__1 exits by its condition within its fuel `⌈1/M⌉`. -/
theorem loop1_exit (M : ℝ) (hM : 0 < M) :
    ∃ k : ℕ, k < (⌈1 / M⌉).toNat ∧ (∀ i < k, M * 2 ^ i < 1) ∧ 1 ≤ M * 2 ^ k ∧
      (0 < k → M * 2 ^ k < 2) := by
  have hex : ∃ i : ℕ, 1 ≤ M * 2 ^ i := by
    obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (1 / M) (by norm_num : (1 : ℝ) < 2)
    refine ⟨i, ?_⟩
    rw [div_lt_iff₀ hM] at hi
    linarith
  classical
  have h1 : (0 : ℝ) < 1 / M := by positivity
  have hmin : ∀ i < Nat.find hex, M * 2 ^ i < 1 := fun i hi => not_le.mp (Nat.find_min hex hi)
  refine ⟨Nat.find hex, ?_, hmin, Nat.find_spec hex, fun hk => ?_⟩
  · apply Int.lt_toNat.mpr
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · rw [h0]
      have : (0 : ℤ) < ⌈1 / M⌉ := Int.ceil_pos.mpr h1
      exact_mod_cast this
    · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hlt : M * 2 ^ j < 1 := hmin j (by omega)
      have h2 : (2 : ℝ) ^ j < 1 / M := by
        rw [lt_div_iff₀ hM]; linarith
      have h3 : (((2 ^ j : ℕ) : ℤ) : ℝ) < ⌈1 / M⌉ := by
        push_cast; exact lt_of_lt_of_le h2 (Int.le_ceil _)
      have h4 : ((2 ^ j : ℕ) : ℤ) < ⌈1 / M⌉ := by exact_mod_cast h3
      have h5 : j < 2 ^ j := Nat.lt_two_pow_self
      rw [hj]
      omega
  · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hlt : M * 2 ^ j < 1 := hmin j (by omega)
    rw [hj, pow_succ]
    linarith

/-- The halving loop of FPRoundBase__1 exits by its condition within its fuel `⌈m⌉`. -/
theorem loop2_exit (m : ℝ) (hm : 1 ≤ m) :
    ∃ k : ℕ, k < (⌈m⌉).toNat ∧ (∀ j < k, 2 ≤ m / 2 ^ j) ∧ m / 2 ^ k < 2 ∧ 1 ≤ m / 2 ^ k := by
  have hex : ∃ j : ℕ, m / 2 ^ j < 2 := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt m (by norm_num : (1 : ℝ) < 2)
    refine ⟨j, ?_⟩
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j]
  classical
  have hmin : ∀ j < Nat.find hex, 2 ≤ m / 2 ^ j := fun j hj => not_lt.mp (Nat.find_min hex hj)
  refine ⟨Nat.find hex, ?_, hmin, Nat.find_spec hex, ?_⟩
  · apply Int.lt_toNat.mpr
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · rw [h0]
      have : (0 : ℤ) < ⌈m⌉ := Int.ceil_pos.mpr (by linarith)
      exact_mod_cast this
    · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hge : 2 ≤ m / 2 ^ j := hmin j (by omega)
      have h2 : (2 : ℝ) ^ (j + 1) ≤ m := by
        rw [le_div_iff₀ (by positivity)] at hge
        rw [pow_succ]; linarith
      have h3 : (((2 ^ (j + 1) : ℕ) : ℤ) : ℝ) ≤ ⌈m⌉ := by
        push_cast; exact le_trans h2 (Int.le_ceil _)
      have h4 : ((2 ^ (j + 1) : ℕ) : ℤ) ≤ ⌈m⌉ := by exact_mod_cast h3
      have h5 : j + 1 < 2 ^ (j + 1) := Nat.lt_two_pow_self
      rw [hj]
      omega
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · rw [h0]; simpa using hm
    · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hge : 2 ≤ m / 2 ^ j := hmin j (by omega)
      rw [hj, pow_succ, ← div_div]
      rw [le_div_iff₀ (by norm_num)]
      linarith

/-- The two loops of FPRoundBase__1 from a positive mantissa `M`: the exponent `e` and the
mantissa `M * 2^(-e)` in `[1, 2)`. -/
theorem loops_eq (M : ℝ) (hM : 0 < M) :
    ∃ e : ℤ, loopP c2 g2 (⌈(loopP c1 g1 (⌈1 / M⌉).toNat (0, M)).2⌉).toNat
        (loopP c1 g1 (⌈1 / M⌉).toNat (0, M)) = (e, M * 2 ^ (-e)) ∧
      1 ≤ M * 2 ^ (-e) ∧ M * 2 ^ (-e) < 2 := by
  obtain ⟨k1, hk1, hlt1, hge1, -⟩ := loop1_exit M hM
  have hL : loopP c1 g1 (⌈1 / M⌉).toNat (0, M) = ((0 : ℤ) - k1, M * 2 ^ k1) := by
    rw [loopP_of_exit c1 g1 k1 _ (0, M) hk1 (fun i hi => by
        rw [g1_iter]; simp [c1, lt_real, hlt1 i hi]) (by rw [g1_iter]; simp [c1, lt_real, hge1]),
      g1_iter]
  rw [hL]
  obtain ⟨k2, hk2, hge2, hlt2, hge2'⟩ := loop2_exit (M * 2 ^ k1) hge1
  rw [loopP_of_exit c2 g2 k2 _ _ hk2 (fun j hj => by
      rw [g2_iter]; simp [c2, gteq_real, hge2 j hj]) (by rw [g2_iter]; simp [c2, gteq_real, hlt2]),
    g2_iter]
  have he : M * 2 ^ k1 / 2 ^ k2 = M * (2 : ℝ) ^ (-((0 : ℤ) - k1 + k2)) := by
    rw [show -((0 : ℤ) - k1 + k2) = (k1 : ℤ) - k2 by ring, zpow_sub₀ two_ne_zero, zpow_natCast,
      zpow_natCast]
    ring
  exact ⟨(0 : ℤ) - k1 + k2, by rw [he], he ▸ hge2', he ▸ hlt2⟩

theorem loops_eq' (M : ℝ) (hM : 0 < M) :
    ∃ e : ℤ, loopP (fun y => gteq_real y.2 2) (fun y => (y.1 + 1, div_real y.2 2))
        (round_up (loopP (fun y => lt_real y.2 1) (fun y => (y.1 - 1, mult_real y.2 2))
          (round_up (div_real (to_real 1) M)).toNat ((0 : ℤ), M)).2).toNat
        ((loopP (fun y => lt_real y.2 1) (fun y => (y.1 - 1, mult_real y.2 2))
          (round_up (div_real (to_real 1) M)).toNat ((0 : ℤ), M)).1,
         (loopP (fun y => lt_real y.2 1) (fun y => (y.1 - 1, mult_real y.2 2))
          (round_up (div_real (to_real 1) M)).toNat ((0 : ℤ), M)).2) = (e, M * 2 ^ (-e)) ∧
      1 ≤ M * 2 ^ (-e) ∧ M * 2 ^ (-e) < 2 := by
  obtain ⟨e, he, h1, h2⟩ := loops_eq M hM
  refine ⟨e, ?_, h1, h2⟩
  have : div_real (to_real 1) M = 1 / M := by simp [div_real, to_real]
  rw [this]
  simp only [round_up, Prod.mk.eta]
  exact he

end F7
