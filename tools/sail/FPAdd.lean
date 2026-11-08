import Armv9fp
import Interpreter.Wasm.Float

/-!
The pilot of increment F7: the FPAdd of Sail's Lean translation of the Armv9.4-A model
(`translate.sh` with `fp-slice.isail`, `--lean-real-numbers`, edited by `fix-output.sh`), at 64
bits under FPCR 0x02000000, returns Talos's `f64Add` of its operands for every pair of words and
sets in FPSR the bits of `addMask`, from every state that satisfies `Hyp`.  The proof runs the
translated code: `fpUnpack_run`, `fpProcessNaNs_run`, and `fpRound_run` state what FPUnpack__1,
FPProcessNaNs__1, and FPRound__2 return, and `fpAdd_run` puts them together case by case.
`loop1_exit` and `loop2_exit` state that the two `whileFuelM` loops of FPRoundBase__1, the only
ones of the slice, exit by their conditions within their fuel for every positive mantissa.  The
proof keeps `trivialChoiceSource` irreducible, so the unspecified values that the model draws stay
unevaluated terms.  `Frame` states that memory, tags, cycle count, and output do not change.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions

namespace F7Pilot

attribute [local irreducible] trivialChoiceSource

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

/-- The state hypothesis: the register map holds FeatureImpl, PSTATE, and FPSR, at least one of
FEAT_AA64EL0 to FEAT_AA64EL3 is implemented, FEAT_SME_FA64 is not, and PSTATE.nRW is 0.
FEAT_AFP, FEAT_SME, the other features, the other fields of PSTATE, and FPSR's value are free. -/
structure Hyp (R : Std.ExtDHashMap Register RegisterType) (fi : Vector Bool 259) (ps : ProcState)
    (fpsr : BitVec 64) : Prop where
  hfi : R.get? Register.FeatureImpl = some fi
  aa64 : (((fi[num_of_Feature .FEAT_AA64EL0]! || fi[num_of_Feature .FEAT_AA64EL1]!) ||
    fi[num_of_Feature .FEAT_AA64EL2]!) || fi[num_of_Feature .FEAT_AA64EL3]!) = true
  fa64 : fi[num_of_Feature .FEAT_SME_FA64]! = false
  hps : R.get? Register.PSTATE = some ps
  nrw : ps.nRW = 0#1
  hfpsr : R.get? Register.FPSR = some fpsr

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
    PreSail.undefined_bool, PreSail.undefined_bitvector, PreSail.undefined_int, undefined_real,
    undefined_FPType, PreSail.internal_pick, bind_choose (p := .bool), bind_choose (p := .int),
    bind_choose (p := .bitvector _), bind_choose (p := .fin _),
    UsingAArch32, HaveAArch64, IsFeatureImplemented, HaveAArch32, HaveAltFP, HaveSME,
    HaveSMEFullA64, IsFullA64Enabled, InStreamingMode,
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
        h.hps, h.nrw, h.aa64, h.fa64, h.hfpsr, isNaNT, ite_self]
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

theorem exp_eq (N : ℕ) (hN : 0 < N) (e : ℤ)
    (h1 : 1 ≤ (N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) * 2 ^ (-e))
    (h2 : (N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) * 2 ^ (-e) < 2) :
    e = (Nat.log2 N : ℤ) - 1074 := by
  have hL1 : 2 ^ Nat.log2 N ≤ N := Nat.log2_self_le (by omega)
  have hL2 : N < 2 ^ (Nat.log2 N + 1) := Nat.lt_log2_self
  have hr1 : ((2 : ℝ) ^ (Nat.log2 N : ℤ)) ≤ N := by
    rw [zpow_natCast]; exact_mod_cast hL1
  have hr2 : (N : ℝ) < (2 : ℝ) ^ ((Nat.log2 N : ℤ) + 1) := by
    rw [show ((Nat.log2 N : ℤ) + 1) = ((Nat.log2 N + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
    exact_mod_cast hL2
  have ht : (N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) * 2 ^ (-e) = N * 2 ^ (-1074 - e) := by
    rw [mul_assoc, ← zpow_add₀ two_ne_zero]; ring_nf
  rw [ht] at h1 h2
  have hpos : (0 : ℝ) < 2 ^ (-1074 - e) := zpow_pos (by norm_num) _
  have a1 : (2 : ℝ) ^ (0 : ℤ) < 2 ^ ((Nat.log2 N : ℤ) + 1 + (-1074 - e)) := by
    rw [zpow_add₀ two_ne_zero, zpow_zero]
    calc (1 : ℝ) ≤ N * 2 ^ (-1074 - e) := h1
      _ < 2 ^ ((Nat.log2 N : ℤ) + 1) * 2 ^ (-1074 - e) := by
        exact mul_lt_mul_of_pos_right hr2 hpos
  have a2 : (2 : ℝ) ^ ((Nat.log2 N : ℤ) + (-1074 - e)) < 2 ^ (1 : ℤ) := by
    rw [zpow_add₀ two_ne_zero, zpow_one]
    calc (2 : ℝ) ^ (Nat.log2 N : ℤ) * 2 ^ (-1074 - e) ≤ N * 2 ^ (-1074 - e) :=
          mul_le_mul_of_nonneg_right hr1 hpos.le
      _ < 2 := h2
  rw [zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)] at a1 a2
  omega

theorem join1_beq (b : BitVec 1) : (BitVec.join1 [b] == 1#1) = (b == 1#1) := by
  have hb : b = 0#1 ∨ b = 1#1 := by
    have h2 := b.isLt
    rcases (show b.toNat = 0 ∨ b.toNat = 1 by omega) with h0 | h0
    · left; exact BitVec.eq_of_toNat_eq (by simpa using h0)
    · right; exact BitVec.eq_of_toNat_eq (by simpa using h0)
  rcases hb with rfl | rfl <;> decide

theorem int_access (m : ℕ) : (integer_access (m : ℤ) 0 == 1#1) = decide (m % 2 = 1) := by
  simp [integer_access, integer_subrange, get_slice_int, BitVec.access]
  have h0 : (BitVec.ofNat 2 m)[0] = decide (m % 2 = 1) := by
    rw [BitVec.getElem_eq_testBit_toNat, BitVec.toNat_ofNat, Nat.testBit_eq_decide_div_mod_eq]
    apply decide_eq_decide.mpr
    simp only [pow_zero, Nat.div_one]
    omega
  rw [h0]
  by_cases hm : m % 2 = 1 <;> simp [*]

theorem man_normal (N : ℕ) (e : ℤ) (hE : e = (Nat.log2 N : ℤ) - 1074) (hL : 52 ≤ Nat.log2 N) :
    mult_real ((N : ℝ) * 2 ^ (-1074 : ℤ) * 2 ^ (-e)) (real_power 2 52) =
      (N : ℝ) / ((2 ^ (Nat.log2 N - 52) : ℕ) : ℝ) := by
  simp only [mult_real, real_power]
  rw [mul_assoc, mul_assoc, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero, div_eq_mul_inv]
  congr 1
  push_cast
  rw [← zpow_natCast, ← zpow_neg]
  congr 1
  omega

theorem man_sub (N : ℕ) (e : ℤ) (hE : e = (Nat.log2 N : ℤ) - 1074) :
    mult_real (div_real ((N : ℝ) * 2 ^ (-1074 : ℤ) * 2 ^ (-e)) (real_power 2 (-1022 - e)))
      (real_power 2 52) = (N : ℝ) := by
  simp only [mult_real, div_real, real_power]
  rw [div_eq_mul_inv, ← zpow_neg, mul_assoc, mul_assoc, mul_assoc, ← zpow_add₀ two_ne_zero,
    ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]
  rw [show (-1074 : ℤ) + (-e + (-(-1022 - e) + 52)) = 0 by omega, zpow_zero, mul_one]

theorem floor_div_nat (N d : ℕ) : round_down ((N : ℝ) / (d : ℝ)) = ((N / d : ℕ) : ℤ) := by
  simp only [round_down]
  rw [Int.floor_div_natCast, Int.floor_natCast]
  push_cast; rfl

theorem floor_nat (N : ℕ) : round_down (N : ℝ) = (N : ℤ) := by
  simp [round_down]

theorem err_div (N d : ℕ) (hd : 0 < d) :
    sub_real ((N : ℝ) / (d : ℝ)) (to_real ((N / d : ℕ) : ℤ)) = ((N % d : ℕ) : ℝ) / (d : ℝ) := by
  simp only [sub_real, to_real]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hN : (N : ℝ) = d * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod N d).symm
  rw [eq_div_iff hd', sub_mul, div_mul_cancel₀ _ hd', Int.cast_natCast]
  rw [hN]
  ring

theorem gt_half (r d : ℕ) (hd : 0 < d) :
    gt_real ((r : ℝ) / (d : ℝ)) (1 / 2) = decide (d < 2 * r) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  simp only [gt_real, gt_iff_lt, decide_eq_decide]
  rw [lt_div_iff₀ hd']
  constructor
  · intro h; have : (d : ℝ) < 2 * r := by linarith
    exact_mod_cast this
  · intro h; have : (d : ℝ) < 2 * r := by exact_mod_cast h
    linarith

theorem eq_half (r d : ℕ) (hd : 0 < d) :
    eq_real ((r : ℝ) / (d : ℝ)) (1 / 2) = decide (2 * r = d) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [eq_real, decide_eq_decide]
  rw [div_eq_iff hd']
  constructor
  · intro h; have : (2 * r : ℝ) = d := by linarith
    exact_mod_cast this
  · intro h; have : (2 * r : ℝ) = d := by exact_mod_cast h
    linarith

theorem beq_zero_div (r d : ℕ) (hd : 0 < d) : (((r : ℝ) / (d : ℝ)) == 0) = decide (r = 0) := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [beq_eq_decide]
  simp [hd']

theorem sub_self_nat (N : ℕ) : sub_real (N : ℝ) (to_real (N : ℤ)) = 0 := by
  simp [sub_real, to_real]

theorem subrange_toNat (x hi : ℤ) (hx : 0 ≤ x) (hh : 0 ≤ hi) :
    (integer_subrange x hi 0).toNat = x.toNat % 2 ^ ((hi - 0 + 1).toNat) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hx
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hh
  simp only [integer_subrange, get_slice_int]
  simp [BitVec.extractLsb'_toNat, BitVec.toNat_ofInt]
  exact Nat.mod_mod_of_dvd m (Nat.pow_dvd_pow 2 (by omega))

set_option maxRecDepth 10000 in
theorem bits_eq (sb : BitVec 1) (be im hi1 hi2 : ℤ) (w0 : ℕ) (h1 : hi1 = 10) (h2 : hi2 = 51)
    (h0 : w0 = 0) (hbe : 0 ≤ be) (hbe' : be < 2047) (him : 2 ^ 52 ≤ im) (him' : im < 2 ^ 53) :
    BitVec.setWidth 64 (sb +++ integer_subrange be hi1 0 +++ integer_subrange im hi2 0 +++
      (Zeros (n := w0))) =
      BitVec.ofNat 64 (sb.toNat * 2 ^ 63 + be.toNat * 2 ^ 52 + (im.toNat - 2 ^ 52)) := by
  subst h1 h2 h0
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append, subrange_toNat be 10 hbe (by norm_num),
    subrange_toNat im 51 (by omega) (by norm_num), Zeros, BitVec.zero, BitVec.toNat_ofNat]
  have e11 : ((10 : ℤ) - 0 + 1).toNat = 11 := rfl
  have e52 : ((51 : ℤ) - 0 + 1).toNat = 52 := rfl
  have f11 : Int.toNat 10 - Int.toNat 0 + 1 = 11 := rfl
  have f52 : Int.toNat 51 - Int.toNat 0 + 1 = 52 := rfl
  rw [e11, e52, f11, f52]
  have hb1 : be.toNat < 2 ^ 11 := by omega
  have hi1 : 2 ^ 52 ≤ im.toNat := by omega
  have hi2 : im.toNat < 2 ^ 53 := by omega
  have hs : sb.toNat < 2 := sb.isLt
  have hm : im.toNat % 2 ^ 52 = im.toNat - 2 ^ 52 := by omega
  rw [Nat.mod_eq_of_lt hb1, hm]
  have o1 : sb.toNat <<< 11 ||| be.toNat = sb.toNat * 2 ^ 11 + be.toNat := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hb1, Nat.shiftLeft_eq]
  have o2 : (sb.toNat * 2 ^ 11 + be.toNat) <<< 52 ||| (im.toNat - 2 ^ 52) =
      (sb.toNat * 2 ^ 11 + be.toNat) * 2 ^ 52 + (im.toNat - 2 ^ 52) := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), Nat.shiftLeft_eq]
  have z : ∀ x : BitVec 0, x.toNat = 0 := fun x => by have := x.isLt; simp at this; omega
  have o3 : (sb.toNat * 2 ^ 11 + be.toNat) * 2 ^ 52 = sb.toNat * 2 ^ 63 + be.toNat * 2 ^ 52 := by
    rw [Nat.add_mul, Nat.mul_assoc, ← Nat.pow_add]
  rw [o1, o2, Nat.shiftLeft_zero, z, Nat.or_zero, o3]

theorem one_beq_zero : ((1 : ℝ) == 0) = false := by simp

theorem ipow (x y : ℤ) : @HPow.hPow ℤ ℤ ℤ instHPowInt_sail x y = x ^ y.toNat := rfl

theorem fdiv_two (a : ℤ) (h : 0 ≤ a) : fdiv_int a 2 = a / 2 := by
  have h1 : (decide (a < 0) && decide ((2 : ℤ) > 0)) = false := by simp; omega
  have h2 : (decide (a > 0) && decide ((2 : ℤ) < 0)) = false := by simp
  simp only [fdiv_int, h1, h2, Bool.false_eq_true, ↓reduceIte]
  exact Int.tdiv_eq_ediv_of_nonneg h

/-- Talos's result of rounding the magnitude `N`, in units of 2^-1074, with the sign `neg`. -/
def tRound (neg : Bool) (N : ℕ) : BitVec 64 := (Wasm.IEEE64.roundScaledMagnitude neg N).toBitVec

theorem toBV_encode (neg : Bool) (e f : ℕ) :
    (Wasm.IEEE64.encodeFinite neg e f).toBitVec =
      BitVec.ofNat 64 ((if neg then 2 ^ 63 else 0) + e * 2 ^ 52 + f) := rfl

theorem toBV_inf (neg : Bool) :
    (Wasm.IEEE64.infinity neg).toBitVec =
      (if neg then 0xFFF0000000000000#64 else 0x7FF0000000000000#64) := by
  cases neg <;> rfl

theorem enc_congr {neg : Bool} {a a' b b' : ℕ} (h1 : a = a') (h2 : b = b') :
    (Wasm.IEEE64.encodeFinite neg a b).toBitVec = (Wasm.IEEE64.encodeFinite neg a' b').toBitVec := by
  subst h1 h2; rfl

set_option maxHeartbeats 1000000 in
theorem tRound_normal (neg : Bool) (N k q r : ℕ) (hk : Nat.log2 N = k + 52) (hq : N / 2 ^ k = q)
    (hr : N % 2 ^ k = r) (hq1 : 2 ^ 52 ≤ q) (hq2 : q < 2 ^ 53) (hrk : r < 2 ^ k)
    (hL1 : 2 ^ (k + 52) ≤ N) :
    tRound neg N =
      (if (2 ^ k < 2 * r ∨ 2 * r = 2 ^ k ∧ q % 2 = 1) then
        (if q + 1 = 2 ^ 53 then
          (if 2047 ≤ k + 2 then (Wasm.IEEE64.infinity neg).toBitVec
           else (Wasm.IEEE64.encodeFinite neg (k + 2) 0).toBitVec)
         else (if 2047 ≤ k + 1 then (Wasm.IEEE64.infinity neg).toBitVec
           else (Wasm.IEEE64.encodeFinite neg (k + 1) (q + 1 - 2 ^ 52)).toBitVec))
       else (if 2047 ≤ k + 1 then (Wasm.IEEE64.infinity neg).toBitVec
         else (Wasm.IEEE64.encodeFinite neg (k + 1) (q - 2 ^ 52)).toBitVec)) := by
  have hk2 : 2 ^ k * q + r = N := by rw [← hq, ← hr]; exact Nat.div_add_mod N (2 ^ k)
  unfold tRound Wasm.IEEE64.roundScaledMagnitude
  by_cases hN53 : N < 2 ^ 53
  · have hk0 : k = 0 := by
      by_contra hne
      have : 2 ^ 53 ≤ 2 ^ (k + 52) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hk0
    simp only [pow_zero, Nat.mod_one, Nat.div_one] at hq hr
    subst hq hr
    have h52 : ¬ N < 2 ^ 52 := by
      have : 2 ^ 52 ≤ N := by simpa using hL1
      omega
    simp only [h52, hN53, if_false, if_true]
    have hup : ¬ (2 ^ 0 < 2 * 0 ∨ 2 * 0 = 2 ^ 0 ∧ N % 2 = 1) := by omega
    rw [if_neg hup, if_neg (by omega)]
  · have h52 : ¬ N < 2 ^ 52 := by omega
    have hk1 : 1 ≤ k := by
      by_contra h0
      have : k = 0 := by omega
      subst this
      have := Nat.lt_log2_self (n := N)
      rw [hk] at this
      omega
    simp only [h52, hN53, if_false, hk, Nat.add_sub_cancel, Wasm.IEEE32.roundShift, hq, hr]
    have hhalf : 2 ^ k / 2 = 2 ^ (k - 1) := by
      rw [show k = k - 1 + 1 by omega, pow_succ]; simp
    have hpk : 2 ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hhalf]
    by_cases hup : (2 ^ k < 2 * r ∨ 2 * r = 2 ^ k ∧ q % 2 = 1)
    · simp only [hup, if_true]
      have hround : (if r < 2 ^ (k - 1) then q else if 2 ^ (k - 1) < r then q + 1
          else if q % 2 == 0 then q else q + 1) = q + 1 := by
        rcases hup with h | ⟨h, ho⟩
        · rw [if_neg (by omega), if_pos (by omega)]
        · rw [if_neg (by omega), if_neg (by omega)]
          simp [ho]
      rw [hround]
      by_cases hc : q + 1 = 2 ^ 53
      · simp only [hc, if_true, beq_self_eq_true]
        split_ifs <;> first | omega | (exact enc_congr (by omega) (by omega)) | rfl
      · have hc' : (q + 1 == 2 ^ 53) = false := by simpa using hc
        simp only [hc, hc', if_false, Bool.false_eq_true]
        split_ifs <;> first | omega | (exact enc_congr (by omega) (by omega)) | rfl
    · simp only [hup, if_false]
      have hround : (if r < 2 ^ (k - 1) then q else if 2 ^ (k - 1) < r then q + 1
          else if q % 2 == 0 then q else q + 1) = q := by
        simp only [not_or, not_and, not_lt] at hup
        by_cases h1 : r < 2 ^ (k - 1)
        · rw [if_pos h1]
        · rw [if_neg h1, if_neg (by omega)]
          have : q % 2 = 0 := by omega
          simp [this]
      rw [hround]
      have hc' : (q == 2 ^ 53) = false := by simp; omega
      simp only [hc', if_false, Bool.false_eq_true]
      split_ifs <;> first | omega | (exact enc_congr (by omega) (by omega)) | rfl

theorem insert_insert (R : Std.ExtDHashMap Register RegisterType) (r : Register)
    (v w : RegisterType r) : (R.insert r v).insert r w = R.insert r w := by
  apply Std.ExtDHashMap.ext_get?
  intro k
  simp only [Std.ExtDHashMap.get?_insert]
  split <;> rfl

theorem insert_self (R : Std.ExtDHashMap Register RegisterType) (r : Register) (v : RegisterType r)
    (h : R.get? r = some v) : R.insert r v = R := by
  apply Std.ExtDHashMap.ext_get?
  intro k
  simp only [Std.ExtDHashMap.get?_insert]
  split
  · rename_i hk
    have := eq_of_beq hk
    subst this
    simp [h]
  · rfl

theorem upd_or (v : BitVec 64) (k : ℕ) (hk : k < 64) :
    Sail.BitVec.update v k (Bit 1#1) = v ||| (1#64 <<< k) := by
  ext i hi
  simp [Sail.BitVec.update, Sail.BitVec.updateSubrange', Bit, BitVec.access]
  by_cases h1 : i < k <;> by_cases h2 : i - k = 0 <;> simp [h1, h2]

/-- The bits of FPSR that FPRoundBase__1 sets for the nonzero magnitude `N`, in units of
2^-1074, at 64 bits under FPCR 0x02000000: OFC and IXC on overflow, IXC on an inexact result. -/
def roundMask (N : ℕ) : BitVec 64 :=
  let k := Nat.log2 N - 52
  let q := N / 2 ^ k
  let r := N % 2 ^ k
  let be := if (2 ^ k < 2 * r ∨ 2 * r = 2 ^ k ∧ q % 2 = 1) ∧ q + 1 = 2 ^ 53 then k + 2 else k + 1
  if 2047 ≤ be then 0x14#64 else if r = 0 then 0#64 else 0x10#64

theorem or_masks (v : BitVec 64) :
    (v ||| 1#64 <<< 2) ||| 1#64 <<< 4 = v ||| 0x14#64 ∧ v ||| 1#64 <<< 4 = v ||| 0x10#64 ∧
      v ||| 1#64 <<< 0 = v ||| 1#64 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [BitVec.or_assoc]; congr 1
  · congr 1
  · congr 1

/-- The real number `±N · 2^-1074`. -/
noncomputable def sop (neg : Bool) (N : ℕ) : ℝ :=
  if neg then -((N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) else (N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)

theorem sop_facts (neg : Bool) (N : ℕ) (hN : 0 < N) :
    lt_real (sop neg N) 0 = neg ∧ (sop neg N == 0) = false ∧
      neg_real (-((N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ))) = (N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) := by
  have hM : (0 : ℝ) < (N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) :=
    mul_pos (by exact_mod_cast hN) (zpow_pos (by norm_num) _)
  refine ⟨?_, ?_, by simp [neg_real]⟩
  · cases neg <;> simp [sop, lt_real, hM, hM.le, hN]
  · cases neg <;> simp [sop, hM.ne', Nat.pos_iff_ne_zero.mp hN]

set_option maxHeartbeats 0 in
theorem round_normal (neg : Bool) (N : ℕ) (hN : 0 < N) (hL : 52 ≤ Nat.log2 N)
    {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 (sop neg N) fpcrV .FPRounding_TIEEVEN true 64).run s =
      .ok (tRound neg N) s' ∧ s'.regs = R.insert .FPSR (fpsr ||| roundMask N) ∧ Frame s s' := by
  subst hs
  have hM : (0 : ℝ) < (N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) :=
    mul_pos (by exact_mod_cast hN) (zpow_pos (by norm_num) _)
  obtain ⟨e, he, h1, h2⟩ := loops_eq' _ hM
  have hE := exp_eq N hN e h1 h2
  obtain ⟨hlt, hne, hneg⟩ := sop_facts neg N hN
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, sop] at hlt hne ⊢
  all_goals (
    have hb : max (e - -1022 + 1) 0 = (Nat.log2 N : ℤ) - 51 := by omega
    have hb0 : ((Nat.log2 N : ℤ) - 51 == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    have hd : 0 < 2 ^ (Nat.log2 N - 52) := Nat.two_pow_pos _
    sail_simp [FPRound__2, FPRoundBase__1, h.hfi, h.hps, h.nrw, h.aa64, h.fa64, h.hfpsr, ite_self,
      whileFuelM_pure, ExceptT.lift_pure, hne, bne, hlt, hneg]
    rw [he]
    sail_simp [↓join1_beq, h.hfi, h.hps, h.nrw, h.aa64, h.fa64, h.hfpsr, ite_self, hne, bne, hlt, hb,
      hb0, man_normal N e hE hL, floor_div_nat, err_div _ _ hd, gt_half _ _ hd, eq_half _ _ hd,
      beq_zero_div _ _ hd, int_access]
    have hL1 : 2 ^ Nat.log2 N ≤ N := Nat.log2_self_le (by omega)
    have hL2 : N < 2 ^ (Nat.log2 N + 1) := Nat.lt_log2_self
    obtain ⟨k, hk⟩ : ∃ k, Nat.log2 N = k + 52 := ⟨Nat.log2 N - 52, by omega⟩
    have hmask : roundMask N = (let q := N / 2 ^ k; let r := N % 2 ^ k
        let be := if (2 ^ k < 2 * r ∨ 2 * r = 2 ^ k ∧ q % 2 = 1) ∧ q + 1 = 2 ^ 53 then k + 2
          else k + 1
        if 2047 ≤ be then 0x14#64 else if r = 0 then 0#64 else 0x10#64) := by
      simp only [roundMask, hk, Nat.add_sub_cancel]
    rw [hk] at hL1 hL2 hd ⊢
    rw [hmask]
    simp only [Nat.add_sub_cancel] at hd ⊢
    have hq1 : 2 ^ 52 ≤ N / 2 ^ k := by
      rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos k)]; rw [pow_add] at hL1; linarith
    have hq2 : N / 2 ^ k < 2 ^ 53 := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
      rw [show k + 52 + 1 = 53 + k by omega, pow_add] at hL2; linarith
    have hr : N % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
    rw [tRound_normal _ N k (N / 2 ^ k) (N % 2 ^ k) hk rfl rfl hq1 hq2 hr hL1]
    generalize hq : N / 2 ^ k = q at *
    generalize hrr : N % 2 ^ k = r at *
    clear he h1 h2 hlt hne hb hb0 hmask hE
    simp only [ipow, Int.reduceToNat, Int.reducePow, Int.reduceSub, Int.reduceAdd, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, ge_iff_le]
    have hfd : fdiv_int ((q : ℤ) + 1) 2 = ((q : ℤ) + 1) / 2 := fdiv_two _ (by omega)
    have c2 : ((q : ℤ) + 1 = 4503599627370496) = False := by simp; omega
    have o1 : (2047 ≤ (↑(k + 52) : ℤ) - 51 + 1) = (2047 ≤ k + 2) := by
      apply propext; constructor <;> intro <;> omega
    have o2 : (2047 ≤ (↑(k + 52) : ℤ) - 51) = (2047 ≤ k + 1) := by
      apply propext; constructor <;> intro <;> omega
    simp only [c2, o1, o2, ↓reduceIte]
    by_cases hup : (2 ^ k < 2 * r ∨ 2 * r = 2 ^ k ∧ q % 2 = 1) <;>
    by_cases hc : q + 1 = 2 ^ 53 <;> by_cases hv1 : 2047 ≤ k + 1 <;> by_cases hv2 : 2047 ≤ k + 2 <;>
    by_cases hr0 : r = 0
    all_goals first | (exfalso; omega) | skip
    all_goals (
      have hcI : ((q : ℤ) + 1 = 9007199254740992) = (q + 1 = 2 ^ 53) := by
        apply propext; constructor <;> intro <;> omega
      have e1 := by first | exact eq_false hup | exact eq_true hup
      have e2 := by first | exact eq_false hc | exact eq_true hc
      have e3 := by first | exact eq_false hv1 | exact eq_true hv1
      have e4 := by first | exact eq_false hv2 | exact eq_true hv2
      have e5 := by first | exact eq_false hr0 | exact eq_true hr0
      simp only [hcI, e1, e2, e3, e4, e5, true_and, and_true, false_and,
        and_false, ↓reduceIte, decide_true, decide_false, Bool.not_true, Bool.not_false]
      try simp only [o1, o2, e3, e4, ↓reduceIte]
      apply exists_of_run'
      · sail_simp [FPInfinity, FPProcessException, h.hfi, h.hps, h.nrw, h.aa64, h.fa64,
          h.hfpsr, ite_self, toBV_inf, toBV_encode, one_beq_zero, beq_zero_div _ _ hd, cast_eq, e5]
        refine ok_congr ?_
        first
        | decide
        | (rw [bits_eq]
           · apply congrArg (BitVec.ofNat 64)
             simp only [BitVec.toNat_ofNat, Nat.zero_mod, zero_mul, zero_add, hfd, Nat.reducePow]
             omega
           all_goals first | decide | omega | (simp only [hfd, Int.reducePow]; omega))
      · simp only [setReg_regs, bump_regs, insert_insert, upd_or _ _ (by norm_num : 2 < 64),
          upd_or _ _ (by norm_num : 4 < 64), (or_masks _).1, (or_masks _).2.1, BitVec.or_zero,
          cast_eq] <;> first | rfl | exact (insert_self _ _ _ h.hfpsr).symm
      · exact ⟨rfl, rfl, rfl, rfl⟩))

set_option maxRecDepth 10000 in
theorem bits_sub (sb : BitVec 1) (be im hi1 hi2 : ℤ) (w0 : ℕ) (h1 : hi1 = 10) (h2 : hi2 = 51)
    (h0 : w0 = 0) (hbe : be = 0) (him : 0 ≤ im) (him' : im < 4503599627370496) :
    BitVec.setWidth 64 (sb +++ integer_subrange be hi1 0 +++ integer_subrange im hi2 0 +++
      (Zeros (n := w0))) = BitVec.ofNat 64 (sb.toNat * 2 ^ 63 + im.toNat) := by
  subst h1 h2 h0 hbe
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_append, subrange_toNat 0 10 le_rfl (by norm_num),
    subrange_toNat im 51 him (by norm_num), Zeros, BitVec.zero, BitVec.toNat_ofNat]
  have e11 : ((10 : ℤ) - 0 + 1).toNat = 11 := rfl
  have e52 : ((51 : ℤ) - 0 + 1).toNat = 52 := rfl
  have f11 : Int.toNat 10 - Int.toNat 0 + 1 = 11 := rfl
  have f52 : Int.toNat 51 - Int.toNat 0 + 1 = 52 := rfl
  rw [e11, e52, f11, f52]
  have hi2 : im.toNat < 2 ^ 52 := by omega
  have hs : sb.toNat < 2 := sb.isLt
  have z : ∀ x : BitVec 0, x.toNat = 0 := fun x => by have := x.isLt; simp at this; omega
  rw [Nat.mod_eq_of_lt hi2]
  have o0 : Int.toNat 0 % 2 ^ 11 = 0 := rfl
  have o1 : sb.toNat <<< 11 ||| 0 = sb.toNat * 2 ^ 11 := by rw [Nat.or_zero, Nat.shiftLeft_eq]
  have o2 : (sb.toNat * 2 ^ 11) <<< 52 ||| im.toNat = sb.toNat * 2 ^ 11 * 2 ^ 52 + im.toNat := by
    rw [← Nat.shiftLeft_add_eq_or_of_lt hi2, Nat.shiftLeft_eq]
  rw [o0, o1, o2, Nat.shiftLeft_zero, z, Nat.or_zero, Nat.mul_assoc, ← Nat.pow_add]

theorem roundMask_small (N : ℕ) (hN : N < 2 ^ 53) : roundMask N = 0#64 := by
  have hl : Nat.log2 N < 53 := by
    rcases Nat.eq_zero_or_pos N with h0 | hp
    · subst h0; decide
    · exact (Nat.log2_lt hp.ne').mpr hN
  have hk : Nat.log2 N - 52 = 0 := by omega
  simp [roundMask, hk, Nat.mod_one]

theorem tRound_sub (neg : Bool) (N : ℕ) (hN : N < 2 ^ 52) :
    tRound neg N = (Wasm.IEEE64.encodeFinite neg 0 N).toBitVec := by
  simp [tRound, Wasm.IEEE64.roundScaledMagnitude, show N < 4503599627370496 from hN]

theorem gt_zero_half : gt_real 0 (1 / 2) = false := by simp [gt_real]
theorem eq_zero_half : eq_real 0 (1 / 2) = false := by simp [eq_real]
theorem zero_beq_zero : ((0 : ℝ) == 0) = true := by simp

set_option maxHeartbeats 0 in
theorem round_sub (neg : Bool) (N : ℕ) (hN : 0 < N) (hL : Nat.log2 N ≤ 51)
    {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 (sop neg N) fpcrV .FPRounding_TIEEVEN true 64).run s =
      .ok (tRound neg N) s' ∧ s'.regs = R.insert .FPSR (fpsr ||| roundMask N) ∧ Frame s s' := by
  subst hs
  have hM : (0 : ℝ) < (N : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) :=
    mul_pos (by exact_mod_cast hN) (zpow_pos (by norm_num) _)
  obtain ⟨e, he, h1, h2⟩ := loops_eq' _ hM
  have hE := exp_eq N hN e h1 h2
  obtain ⟨hlt, hne, hneg⟩ := sop_facts neg N hN
  have hN52 : N < 2 ^ 52 := by
    have := Nat.lt_log2_self (n := N)
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [roundMask_small N (by omega), BitVec.or_zero, insert_self _ _ _ h.hfpsr, tRound_sub _ _ hN52]
  have hb : max (e - -1022 + 1) 0 = 0 := by omega
  have hNi : ((N : ℤ)) < 4503599627370496 := by omega
  cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, sop] at hlt hne ⊢
  all_goals (
    apply exists_of_run
    · sail_simp [FPRound__2, FPRoundBase__1, h.hfi, h.hps, h.nrw, h.aa64, h.fa64, h.hfpsr,
        ite_self, whileFuelM_pure, ExceptT.lift_pure, hne, bne, hlt, hneg]
      rw [he]
      sail_simp [↓join1_beq, h.hfi, h.hps, h.nrw, h.aa64, h.fa64, h.hfpsr, ite_self, hne, bne, hlt,
        hb, man_sub N e hE, floor_nat, sub_self_nat, gt_zero_half, eq_zero_half, zero_beq_zero,
        FPZero, toBV_encode, ipow]
      refine ok_congr ?_
      rw [bits_sub]
      all_goals first | decide | omega | (apply congrArg (BitVec.ofNat 64); simp)
    · rfl
    · exact ⟨rfl, rfl, rfl, rfl⟩)

theorem fpRound_run (neg : Bool) (N : ℕ) (hN : 0 < N) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPRound__2 (sop neg N) fpcrV .FPRounding_TIEEVEN true 64).run s =
      .ok (tRound neg N) s' ∧ s'.regs = R.insert .FPSR (fpsr ||| roundMask N) ∧ Frame s s' := by
  by_cases hL : 52 ≤ Nat.log2 N
  · exact round_normal neg N hN hL h hs
  · exact round_sub neg N hN (by omega) h hs

theorem step {α β} {x : SailM α} {f : α → SailM β} {s0 σ : State} {a : α} {v : β}
    {R R' : Std.ExtDHashMap Register RegisterType} (hσ : Frame s0 σ)
    (hx : ∃ σ1, x.run σ = .ok a σ1 ∧ σ1.regs = R ∧ Frame σ σ1)
    (k : ∀ σ1, σ1.regs = R → Frame s0 σ1 →
      ∃ s', (f a).run σ1 = .ok v s' ∧ s'.regs = R' ∧ Frame s0 s') :
    ∃ s', (x >>= f).run σ = .ok v s' ∧ s'.regs = R' ∧ Frame s0 s' := by
  obtain ⟨σ1, h1, h2, h3⟩ := hx
  rw [bind_run h1]
  exact k σ1 h2 (hσ.trans h3)

theorem t_isNaN (x : BitVec 64) : Wasm.IEEE64.isNaN (UInt64.ofBitVec x) = isNaNT (ty64 x) := by
  simp only [Wasm.IEEE64.isNaN, t_exp, t_frac]
  unfold ty64
  by_cases h0 : ex x = 0
  · simp only [h0, if_true]
    split <;> rfl
  · by_cases h2 : ex x = 2047
    · by_cases h1 : fr x = 0
      · simp only [h0, h2, h1, if_true, if_false]; rfl
      · by_cases h3 : 2 ^ 51 ≤ fr x
        · have h1' : (fr x != 0) = true := by simpa using h1
          have h1'' : (fr x == 0) = false := by simpa using h1
          rw [if_neg h0, if_pos h2, if_neg h1, if_pos h3, h2]; simp only [h1', h1'']; rfl
        · have h1' : (fr x != 0) = true := by simpa using h1
          have h1'' : (fr x == 0) = false := by simpa using h1
          rw [if_neg h0, if_pos h2, if_neg h1, if_neg h3, h2]; simp only [h1', h1'']; rfl
    · have : (ex x == 0x7FF) = false := by simpa using h2
      simp only [h0, h2, this, if_false, Bool.false_and]; rfl

theorem t_isInf (x : BitVec 64) :
    Wasm.IEEE64.isInfinite (UInt64.ofBitVec x) = (ty64 x == .FPType_Infinity) := by
  simp only [Wasm.IEEE64.isInfinite, t_exp, t_frac]
  unfold ty64
  by_cases h0 : ex x = 0
  · simp only [h0, if_true]
    split <;> rfl
  · by_cases h2 : ex x = 2047
    · by_cases h1 : fr x = 0
      · simp only [h0, h2, h1, if_true, if_false]; rfl
      · by_cases h3 : 2 ^ 51 ≤ fr x
        · have h1' : (fr x != 0) = true := by simpa using h1
          have h1'' : (fr x == 0) = false := by simpa using h1
          rw [if_neg h0, if_pos h2, if_neg h1, if_pos h3, h2]; simp only [h1', h1'']; rfl
        · have h1' : (fr x != 0) = true := by simpa using h1
          have h1'' : (fr x == 0) = false := by simpa using h1
          rw [if_neg h0, if_pos h2, if_neg h1, if_neg h3, h2]; simp only [h1', h1'']; rfl
    · have : (ex x == 0x7FF) = false := by simpa using h2
      simp only [h0, h2, this, if_false, Bool.false_and]; rfl

theorem ty_inf (x : BitVec 64) (h : ty64 x = .FPType_Infinity) : ex x = 2047 ∧ fr x = 0 := by
  unfold ty64 at h
  split_ifs at h with h0 h1 h2 h3 <;> first | exact ⟨‹_›, ‹_›⟩ | cases h

theorem ty_fin (x : BitVec 64) (h1 : ty64 x ≠ .FPType_Infinity) (h2 : isNaNT (ty64 x) = false) :
    ex x ≠ 2047 := by
  intro he
  unfold ty64 at h1 h2
  have : ex x ≠ 0 := by omega
  simp only [this, he, if_false, if_true] at h1 h2
  split_ifs at h1 h2 <;> first | contradiction | exact h1 rfl | (exfalso; omega) | exact absurd h2 (by decide)

theorem ty_zero (x : BitVec 64) (hfin : ex x ≠ 2047) :
    Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec x) = 0 ↔ ty64 x = .FPType_Zero := by
  simp only [Wasm.IEEE64.scaledMagnitude, t_exp, t_frac]
  unfold ty64
  by_cases h0 : ex x = 0
  · simp only [h0, beq_self_eq_true, if_true]
    by_cases h1 : fr x = 0 <;> simp [h1]
  · have : (ex x == 0) = false := by simpa using h0
    simp only [this, if_false, Bool.false_eq_true, h0, hfin]
    constructor
    · intro hm; have := Nat.mul_eq_zero.mp hm; simp at this
    · intro hc; cases hc

theorem inf_word (x : BitVec 64) (h : ty64 x = .FPType_Infinity) :
    x = if sg x then 0xFFF0000000000000#64 else 0x7FF0000000000000#64 := by
  obtain ⟨he, hf⟩ := ty_inf x h
  have hx := x.isLt
  unfold ex at he
  unfold fr at hf
  apply BitVec.eq_of_toNat_eq
  unfold sg
  split <;> simp_all <;> omega

theorem val_fin (x : BitVec 64) (h : ex x ≠ 2047) :
    val64 x = (Wasm.IEEE64.scaledValue (UInt64.ofBitVec x) : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) := by
  simp [val64, h]

theorem add_sum (A B : ℤ) :
    add_real ((A : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) ((B : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) =
      ((A + B : ℤ) : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) := by
  simp only [add_real]; push_cast; ring

theorem eq_sum (z : ℤ) : eq_real ((z : ℝ) * (2 : ℝ) ^ (-1074 : ℤ)) 0 = decide (z = 0) := by
  simp [eq_real]

theorem sop_eq (z : ℤ) (hz : z ≠ 0) :
    (z : ℝ) * (2 : ℝ) ^ (-1074 : ℤ) = sop (decide (z < 0)) z.natAbs := by
  by_cases hneg : z < 0
  · simp only [sop, hneg, decide_true, if_true]
    rw [Nat.cast_natAbs, abs_of_neg (by exact_mod_cast hneg)]
    push_cast; ring
  · simp only [sop, hneg, decide_false, Bool.false_eq_true, if_false]
    rw [Nat.cast_natAbs, abs_of_nonneg (by exact_mod_cast (not_lt.mp hneg))]

theorem sv_eq (x : BitVec 64) : Wasm.IEEE64.scaledValue (UInt64.ofBitVec x) =
    if sg x then -(Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec x) : ℤ)
    else (Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec x) : ℤ) := by
  simp only [Wasm.IEEE64.scaledValue, t_sign]

/-- Two finite operands, not both zeros, whose exact sum is zero are not both negative. -/
theorem not_both_neg (a b : BitVec 64) (hfa : ex a ≠ 2047) (hfb : ex b ≠ 2047)
    (hz : ¬ (ty64 a = .FPType_Zero ∧ ty64 b = .FPType_Zero))
    (hs : Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) +
      Wasm.IEEE64.scaledValue (UInt64.ofBitVec b) = 0) : (sg a && sg b) = false := by
  rw [sv_eq, sv_eq] at hs
  cases hsa : sg a <;> cases hsb : sg b <;> simp only [hsa, hsb, if_true, if_false,
    Bool.false_eq_true, Bool.and_false, Bool.false_and, Bool.and_self] at hs ⊢
  exfalso
  have ha0 : Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec a) = 0 := by omega
  have hb0 : Wasm.IEEE64.scaledMagnitude (UInt64.ofBitVec b) = 0 := by omega
  exact hz ⟨(ty_zero a hfa).mp ha0, (ty_zero b hfb).mp hb0⟩

/-- The bits of FPSR that FPAdd sets at 64 bits under FPCR 0x02000000. -/
def addMask (a b : BitVec 64) : BitVec 64 :=
  if isNaNT (ty64 a) || isNaNT (ty64 b) then
    (if ty64 a == .FPType_SNaN || ty64 b == .FPType_SNaN then 1#64 else 0#64)
  else if ty64 a == .FPType_Infinity || ty64 b == .FPType_Infinity then
    (if ty64 a == .FPType_Infinity && ty64 b == .FPType_Infinity && sg a != sg b then 1#64
     else 0#64)
  else
    let z := Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) +
      Wasm.IEEE64.scaledValue (UInt64.ofBitVec b)
    if z = 0 then 0#64 else roundMask z.natAbs

set_option hygiene false in
macro "fin_script" : tactic => `(tactic| (
  have hfa : ex a ≠ 2047 := ty_fin a (by rw [ha]; exact fun h => FPType.noConfusion h) (by rw [ha]; rfl)
  have hfb : ex b ≠ 2047 := ty_fin b (by rw [hb]; exact fun h => FPType.noConfusion h) (by rw [hb]; rfl)
  have hnz : ¬ (ty64 a = .FPType_Zero ∧ ty64 b = .FPType_Zero) := by
    rw [ha, hb]; intro ⟨h1, h2⟩; first | exact FPType.noConfusion h1 | exact FPType.noConfusion h2
  have hr3' : σ3.regs = s.regs := by rw [hr3, ha, hb]; rfl
  rw [val_fin a hfa, val_fin b hfb, add_sum, eq_sum]
  by_cases hz : Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) +
      Wasm.IEEE64.scaledValue (UInt64.ofBitVec b) = 0
  · have hsg := not_both_neg a b hfa hfb hnz hz
    sail_simp [hz, hsg, FPZero, FPProcessDenorms, hr3', h.hfi, h.hps, h.nrw, h.aa64, h.fa64]
    refine ⟨_, rfl, ?_, hf3⟩
    rw [hr3', BitVec.or_zero]
    exact (insert_self _ _ _ h.hfpsr).symm
  · rw [sop_eq _ hz]
    sail_simp [hz]
    refine step hf3 (fpRound_run _ _ (Int.natAbs_pos.mpr hz) h hr3') ?_
    intro σ4 hr4 hf4
    sail_simp [FPProcessDenorms, hr4, h.hfi, h.hps, h.nrw, h.aa64, h.fa64, Std.ExtDHashMap.get?_insert]
    have hz' : (Wasm.IEEE64.scaledValue (UInt64.ofBitVec a) +
        Wasm.IEEE64.scaledValue (UInt64.ofBitVec b) == 0) = false := by simpa using hz
    simp only [hz', Bool.false_eq_true, ↓reduceIte, tRound]
    exact ⟨σ4, rfl, hr4, hf4⟩))

theorem val_zero (x : BitVec 64) (h : ty64 x = .FPType_Zero) : val64 x = 0 := by
  have hfin : ex x ≠ 2047 := ty_fin x (by rw [h]; exact fun h => FPType.noConfusion h) (by rw [h]; rfl)
  rw [val_fin x hfin, sv_eq, (ty_zero x hfin).mpr h]
  simp

theorem sv_zero (x : BitVec 64) (h : ty64 x = .FPType_Zero) :
    Wasm.IEEE64.scaledValue (UInt64.ofBitVec x) = 0 := by
  have hfin : ex x ≠ 2047 := ty_fin x (by rw [h]; exact fun h => FPType.noConfusion h) (by rw [h]; rfl)
  rw [sv_eq, (ty_zero x hfin).mpr h]
  simp

theorem add_real_zero : add_real 0 0 = 0 := by simp [add_real]
theorem eq_real_zero : eq_real 0 0 = true := by simp [eq_real]

set_option hygiene false in
macro "sgn_script" : tactic => `(tactic| (
  have hr3' : σ3.regs = s.regs := by rw [hr3, ha, hb]; rfl
  cases hsa : sg a <;> cases hsb : sg b <;> (try simp only [sgBit, hsa, hsb, ↓reduceIte] at ⊢)
  all_goals try sail_simp [FPZero, FPInfinity, FPProcessDenorms, FPProcessException, hr3', h.hfi,
    h.hps, h.nrw, h.aa64, h.fa64, h.hfpsr]
  all_goals try sail_simp [FPDefaultNaN__1, FPProcessException, FPProcessDenorms, hr3', h.hfi,
    h.hps, h.nrw, h.aa64, h.fa64, h.hfpsr, setReg_regs, cast_eq, ite_self]
  all_goals try rw [inf_word a (by assumption)]
  all_goals try rw [inf_word b (by assumption)]
  all_goals try rw [val_zero a (by assumption)]
  all_goals try rw [val_zero b (by assumption)]
  all_goals try rw [sv_zero a (by assumption)]
  all_goals try rw [sv_zero b (by assumption)]
  all_goals try simp only [hsa, hsb, ↓reduceIte, add_real_zero, eq_real_zero, add_zero,
    beq_self_eq_true, Bool.false_eq_true, Bool.and_false, Bool.false_and, Bool.and_self]
  all_goals try sail_simp [FPZero, FPProcessDenorms, hr3', h.hfi, h.hps, h.nrw, h.aa64, h.fa64]
  all_goals (
    refine ⟨_, ok_congr ?v, ?r, ⟨hf3.mem, hf3.tags, hf3.cyc, hf3.out⟩⟩
    case v => decide
    case r =>
      first
      | (rw [hr3', BitVec.or_zero]; exact (insert_self _ _ _ h.hfpsr).symm)
      | (simp only [setReg_regs, bump_regs, hr3', upd_or _ _ (by norm_num : 0 < 64),
          (or_masks _).2.2]))))

set_option maxHeartbeats 0 in
theorem fpAdd_run (a b : BitVec 64) {R : Std.ExtDHashMap Register RegisterType}
    (h : Hyp R fi ps fpsr) (hs : s.regs = R) :
    ∃ s', (FPAdd a b fpcrV).run s = .ok (Wasm.f64Add (.ofBitVec a) (.ofBitVec b)).toBitVec s' ∧
      s'.regs = R.insert .FPSR (fpsr ||| addMask a b) ∧ Frame s s' := by
  subst hs
  simp only [FPAdd, FPAdd__1]
  sail_simp [FPRoundingMode, FPDecodeRounding, fpcr_RMode]
  refine step ⟨rfl, rfl, rfl, rfl⟩ (fpUnpack_run a h rfl) ?_
  intro σ1 hr1 hf1
  sail_simp []
  refine step hf1 (fpUnpack_run b h hr1) ?_
  intro σ2 hr2 hf2
  sail_simp []
  refine step hf2 (fpProcessNaNs_run _ _ a b h hr2) ?_
  intro σ3 hr3 hf3
  simp only [Wasm.f64Add, Wasm.IEEE64.add, t_isNaN, t_isInf, t_sign, addMask]
  have hioc : ioc fpsr = fpsr ||| 1#64 := by rw [ioc, upd_or _ _ (by norm_num), (or_masks _).2.2]
  cases ha : ty64 a <;> cases hb : ty64 b <;> simp only [isNaNT] at hr3 ⊢ <;> sail_simp []
  -- The NaN cases.
  all_goals first
    | (refine ⟨σ3, ?_, ?_, hf3⟩
       · rfl
       · rw [hr3]
         simp only [ha, hb, ftb_SNaN_SNaN, ftb_QNaN_SNaN,
           ftb_Zero_SNaN, ftb_Denormal_SNaN,
           ftb_Nonzero_SNaN, ftb_Infinity_SNaN, Bool.or_true,
           Bool.true_or, Bool.or_false, Bool.false_or, ↓reduceIte, Bool.false_eq_true, hioc,
           BitVec.or_zero] <;> first | rfl | exact (insert_self _ _ _ h.hfpsr).symm)
    | skip
  all_goals first | fin_script | skip
  all_goals sgn_script

/-- FPAdd at 64 bits under FPCR 0x02000000 returns Talos's `f64Add` for every pair of words from
every state that satisfies the state hypothesis.  FPSR becomes `fpsr ||| addMask a b`, and the
other registers, the memory, the tags, the cycle count, and the output do not change. -/
theorem fpAdd_eq_f64Add (a b : BitVec 64) (s : State) (fi : Vector Bool 259) (ps : ProcState)
    (fpsr : BitVec 64) (h : Hyp s.regs fi ps fpsr) :
    ∃ s', (FPAdd a b fpcrV).run s =
        .ok (Wasm.f64Add (UInt64.ofBitVec a) (UInt64.ofBitVec b)).toBitVec s' ∧
      s'.regs = s.regs.insert .FPSR (fpsr ||| addMask a b) ∧ Frame s s' :=
  fpAdd_run a b h rfl

end F7Pilot

#print axioms F7Pilot.fpAdd_eq_f64Add
#print axioms F7Pilot.loop1_exit
#print axioms F7Pilot.loop2_exit
