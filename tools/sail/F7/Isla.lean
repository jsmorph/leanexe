import F7.FPAdd
import F7.FPSub
import F7.FPMul
import LeanExe.A64.Isla.Float

/-!
The join of the translation's floating-point functions and the equations that the Isla theorems of
the floating-point forms take (`LeanExe/A64/Isla/Float.lean`).

An equation such as `FPAddEq A` constrains `A`, the meaning that Isla's semantics gives the
abstract call `FPAdd64` of a trace, on Isla's values: two 64-bit vectors and the struct of FPCR
whose one field `bits` holds 0x02000000.  The theorems of `F7/` speak of the translation's
functions on `BitVec 64` and its FPCR, a `BitVec 64`, from a state that satisfies `Hyp`.
`SailFPAdd A` states the link between the two, which review supports and Lean does not check: from
every state that satisfies `Hyp`, whatever the translation's `FPAdd a b 0x02000000` returns, `A`
returns on the same words and on `islaFPCR fpcrV`, the struct with `bits` equal to FPCR.  The link
rests on three claims: the IR's `zFPAdd64` returns `zFPAdd`'s result at 64 bits
(`tests/isla/armv9p4-checked-fp.diff`); the IR's `zFPAdd`, which isla-sail compiled from sail-arm
111345b, computes what the translation's FPAdd, from sail-arm 7d0581642, computes; and Isla's state
at each abstract call, read as a register map of the translation, satisfies `Hyp`.
`fpAddEq_of_sail` derives `FPAddEq A` from `SailFPAdd A` and `fpAdd_eq_f64Add`, converting between
`UInt64` and `BitVec 64`, and `fpSubEq_of_sail` and `fpMulEq_of_sail` derive `FPSubEq` and
`FPMulEq` in the same way.

The derivation needs a state that satisfies `Hyp`.  `islaState p u` builds one from the profile `p`
of `LeanExe/A64/Isla/Profile.lean` and its unknown values `u`: FeatureImpl from the values of the
`features` file's lines, in order, with `u.feature` last, as Isla's `InitFeatureImpl` builds it;
PSTATE with the fields that the profile sets and those that `u` holds; HCR_EL2, SCR_EL3, and
SMCR_EL3 as the profile sets them; and SMCR_EL1 and SMCR_EL2 from `u`.  `hyp_tcg`, `hyp_kvm`, and
`hyp_sme` check `Hyp` for each profile, reading each feature through the translation's
`num_of_Feature`, and `names_tcg`, `names_kvm`, and `names_sme` check that the line of the
`features` file at the index `num_of_Feature F` names `F`, for each feature that the proofs read.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions
open LeanExe.A64.Isla (Val Abstract Profile Unknown)

namespace F7

/-- FeatureImpl of Isla's state: the values `impl` of the `features` file's lines whose names
begin with `FEAT_`, in order, and the unknown last element `x`. -/
def featureImpl (impl : List Bool) (x : Bool) : Vector Bool 259 :=
  if h : (impl ++ [x]).toArray.size = 259 then ⟨(impl ++ [x]).toArray, h⟩
  else Vector.replicate 259 false

/-- PSTATE of Isla's state: EL1, SP, D, PAN, and nRW as `Profile.sys` sets them, the fields of `u`,
and 0 in the fields that no trace of a floating-point form reads. -/
def islaPSTATE (u : Unknown) : ProcState :=
  { (default : ProcState) with
    EL := 1#2, SP := 1#1, D := 1#1, PAN := 0#1, nRW := 0#1, A := u.a, F := u.f, I := u.i,
    IL := u.il, SS := u.ss, BTYPE := u.btype, DIT := u.dit, SSBS := u.ssbs, UAO := u.uao,
    SM := u.sm }

/-- The registers of Isla's state that `Hyp` names, under the profile `p` for the floating-point
forms, with FPSR 0. -/
def islaRegs (p : Profile) (u : Unknown) : Std.ExtDHashMap Register RegisterType :=
  (((((((((∅ : Std.ExtDHashMap Register RegisterType).insert Register.FeatureImpl
    (featureImpl p.features.impl u.feature)).insert Register.PSTATE (islaPSTATE u)).insert
    Register.FPSR 0#64).insert Register.SCR_EL3 0x401#64).insert Register.HCR_EL2
    (BitVec.ofNat 64 p.hcr)).insert Register.SMCR_EL1 u.smcr1).insert Register.SMCR_EL2
    u.smcr2).insert Register.SMCR_EL3 (BitVec.ofNat 64 p.smcr3))

/-- A state of the translation with the registers of `islaRegs`. -/
def islaState (p : Profile) (u : Unknown) : State := { (default : State) with regs := islaRegs p u }

attribute [local irreducible] trivialChoiceSource Real.instInhabited unspecReal

theorem islaRegs_get (p : Profile) (u : Unknown) :
    (islaRegs p u).get? Register.FeatureImpl = some (featureImpl p.features.impl u.feature) ∧
    (islaRegs p u).get? Register.PSTATE = some (islaPSTATE u) ∧
    (islaRegs p u).get? Register.FPSR = some 0#64 ∧
    ((islaRegs p u).get? Register.SCR_EL3).isSome = true ∧
    ((islaRegs p u).get? Register.HCR_EL2).isSome = true ∧
    ((islaRegs p u).get? Register.SMCR_EL1).isSome = true ∧
    ((islaRegs p u).get? Register.SMCR_EL2).isSome = true ∧
    ((islaRegs p u).get? Register.SMCR_EL3).isSome = true := by
  simp (config := {decide := true}) only [islaRegs, Std.ExtDHashMap.get?_insert,
    Std.ExtDHashMap.get?_insert_self, ↓reduceDIte, cast_eq, Option.isSome_some, and_self]

/-- `islaState p u` satisfies `Hyp` when the profile's features implement an AArch64 exception
level. -/
theorem hyp_isla (p : Profile) (u : Unknown)
    (haa : ((((featureImpl p.features.impl u.feature)[num_of_Feature .FEAT_AA64EL0]! ||
      (featureImpl p.features.impl u.feature)[num_of_Feature .FEAT_AA64EL1]!) ||
      (featureImpl p.features.impl u.feature)[num_of_Feature .FEAT_AA64EL2]!) ||
      (featureImpl p.features.impl u.feature)[num_of_Feature .FEAT_AA64EL3]!) = true) :
    Hyp (islaState p u).regs (featureImpl p.features.impl u.feature) (islaPSTATE u) 0#64 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := islaRegs_get p u
  exact ⟨h1, haa, h2, rfl, h3, h4, h5, h6, h7, h8⟩

set_option maxRecDepth 20000 in
theorem hyp_tcg (u : Unknown) :
    Hyp (islaState LeanExe.A64.Isla.tcg u).regs
      (featureImpl LeanExe.A64.Isla.tcg.features.impl u.feature) (islaPSTATE u) 0#64 :=
  hyp_isla _ u (by generalize u.feature = x; cases x <;> decide)

set_option maxRecDepth 20000 in
theorem hyp_kvm (u : Unknown) :
    Hyp (islaState LeanExe.A64.Isla.kvm u).regs
      (featureImpl LeanExe.A64.Isla.kvm.features.impl u.feature) (islaPSTATE u) 0#64 :=
  hyp_isla _ u (by generalize u.feature = x; cases x <;> decide)

set_option maxRecDepth 20000 in
theorem hyp_sme (u : Unknown) :
    Hyp (islaState LeanExe.A64.Isla.sme u).regs
      (featureImpl LeanExe.A64.Isla.sme.features.impl u.feature) (islaPSTATE u) 0#64 :=
  hyp_isla _ u (by generalize u.feature = x; cases x <;> decide)

/-- The features that the proofs read, with their names in the `features` files. -/
def readFeatures : List (Feature × String) :=
  [(.FEAT_AA64EL0, "FEAT_AA64EL0_IMPLEMENTED"), (.FEAT_AA64EL1, "FEAT_AA64EL1_IMPLEMENTED"),
   (.FEAT_AA64EL2, "FEAT_AA64EL2_IMPLEMENTED"), (.FEAT_AA64EL3, "FEAT_AA64EL3_IMPLEMENTED"),
   (.FEAT_AFP, "FEAT_AFP_IMPLEMENTED"), (.FEAT_SME, "FEAT_SME_IMPLEMENTED"),
   (.FEAT_SME_FA64, "FEAT_SME_FA64_IMPLEMENTED"), (.FEAT_VHE, "FEAT_VHE_IMPLEMENTED"),
   (.FEAT_SEL2, "FEAT_SEL2_IMPLEMENTED")]

/-- The line of the `features` file at the index `num_of_Feature F` names `F`, for each feature of
`readFeatures`. -/
abbrev NamesAgree (p : Profile) : Prop :=
  ∀ q ∈ readFeatures, (p.features.settings[num_of_Feature q.1]?.map (·.1)) = some q.2

set_option maxRecDepth 20000 in
theorem names_tcg : NamesAgree LeanExe.A64.Isla.tcg := by decide
set_option maxRecDepth 20000 in
theorem names_kvm : NamesAgree LeanExe.A64.Isla.kvm := by decide
set_option maxRecDepth 20000 in
theorem names_sme : NamesAgree LeanExe.A64.Isla.sme := by decide

/-- The struct of FPCR in Isla's values, with `bits` holding `x`. -/
def islaFPCR (x : BitVec 64) : Val := .struct [("bits", .bits 64 x.toNat)]

theorem islaFPCR_fpcrV : islaFPCR fpcrV = .struct [("bits", .bits 64 0x2000000)] := rfl

/-- The link between the abstract call `FPAdd64` and the translation's FPAdd at 64 bits under FPCR
0x02000000, which review supports. -/
def SailFPAdd (A : Abstract) : Prop :=
  ∀ (a b : BitVec 64) (s : State) (fi : Vector Bool 259) (ps : ProcState) (fpsr v : BitVec 64)
    (s' : State), Hyp s.regs fi ps fpsr → (FPAdd a b fpcrV).run s = .ok v s' →
    A "FPAdd64" [.bits 64 a.toNat, .bits 64 b.toNat, islaFPCR fpcrV] = some (.bits 64 v.toNat)

/-- A value of Isla's unknowns, for the witness. -/
def unknown0 : Unknown where
  feature := false
  tcr := 0
  vbar := 0
  ttbr0 := 0
  ttbr0el1 := 0
  sctlr2 := 0
  spsr := 0
  zcr1 := 0
  zcr2 := 0
  smcr1 := 0
  smcr2 := 0
  a := 0
  f := 0
  i := 0
  il := 0
  ss := 0
  btype := 0
  dit := 0
  ssbs := 0
  uao := 0
  sm := 0
  z := fun _ => 0

theorem fpAddEq_of_sail (A : Abstract) (h : SailFPAdd A) : LeanExe.A64.Isla.FPAddEq A := by
  intro a b
  obtain ⟨s', hrun, -, -⟩ := fpAdd_eq_f64Add a.toBitVec b.toBitVec _ _ _ _ (hyp_tcg unknown0)
  have e := h a.toBitVec b.toBitVec _ _ _ _ _ _ (hyp_tcg unknown0) hrun
  rw [islaFPCR_fpcrV] at e
  exact e

/-- The link between the abstract call `FPMul64` and the translation's FPMul at 64 bits under FPCR
0x02000000, which review supports. -/
def SailFPMul (A : Abstract) : Prop :=
  ∀ (a b : BitVec 64) (s : State) (fi : Vector Bool 259) (ps : ProcState) (fpsr v : BitVec 64)
    (s' : State), Hyp s.regs fi ps fpsr → (FPMul a b fpcrV).run s = .ok v s' →
    A "FPMul64" [.bits 64 a.toNat, .bits 64 b.toNat, islaFPCR fpcrV] = some (.bits 64 v.toNat)

theorem fpMulEq_of_sail (A : Abstract) (h : SailFPMul A) : LeanExe.A64.Isla.FPMulEq A := by
  intro a b
  obtain ⟨s', hrun, -, -⟩ := fpMul_eq_f64Mul a.toBitVec b.toBitVec _ _ _ _ (hyp_tcg unknown0)
  have e := h a.toBitVec b.toBitVec _ _ _ _ _ _ (hyp_tcg unknown0) hrun
  rw [islaFPCR_fpcrV] at e
  exact e

/-- The link between the abstract call `FPSub64` and the translation's FPSub at 64 bits under FPCR
0x02000000, which review supports. -/
def SailFPSub (A : Abstract) : Prop :=
  ∀ (a b : BitVec 64) (s : State) (fi : Vector Bool 259) (ps : ProcState) (fpsr v : BitVec 64)
    (s' : State), Hyp s.regs fi ps fpsr → (FPSub a b fpcrV).run s = .ok v s' →
    A "FPSub64" [.bits 64 a.toNat, .bits 64 b.toNat, islaFPCR fpcrV] = some (.bits 64 v.toNat)

theorem fpSubEq_of_sail (A : Abstract) (h : SailFPSub A) : LeanExe.A64.Isla.FPSubEq A := by
  intro a b
  obtain ⟨s', hrun, -, -⟩ := fpSub_eq_f64Sub a.toBitVec b.toBitVec _ _ _ _ (hyp_tcg unknown0)
  have e := h a.toBitVec b.toBitVec _ _ _ _ _ _ (hyp_tcg unknown0) hrun
  rw [islaFPCR_fpcrV] at e
  exact e

end F7
