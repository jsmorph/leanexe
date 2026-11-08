import F7.Isla
import F7.FPSub32
import F7.FPDiv32
import F7.FPSqrt32
import F7.FixedToFP32
import F7.FPToFixed32
import F7.FPCompare32

/-!
The join of the translation's floating-point functions at 32 bits and the equations of the 32-bit
wrappers that the Isla theorems of the single-precision forms take (`LeanExe/A64/Isla/Float.lean`).

The pattern is that of `F7/Isla.lean`.  An equation such as `FPAdd32Eq A` constrains `A`, the
meaning that Isla's semantics gives the abstract call `FPAdd32`, on two 32-bit vectors and the
struct of FPCR.  `SailFPAdd32 A` states the link that review supports and Lean does not check:
from every state that satisfies `Hyp`, whatever the translation's `FPAdd a b 0x02000000` returns
on 32-bit words `a` and `b`, `A` returns on the same words and on `islaFPCR fpcrV`.  The link rests
on the claims of `F7/Isla.lean` with the 32-bit wrapper in place of the 64-bit one: the IR's
`zFPAdd32` returns `zFPAdd`'s result at 32 bits (`tests/isla/armv9p4-checked-fp.diff`), the IR's
`zFPAdd` computes what the translation's FPAdd computes, and Isla's state at each abstract call
satisfies `Hyp`.  `fpAdd32Eq_of_sail` derives `FPAdd32Eq A` from `SailFPAdd32 A` and
`fpAdd32_eq_f32Add`, with the witness `hyp_tcg` of `F7/Isla.lean`, and `fpSub32Eq_of_sail`,
`fpMul32Eq_of_sail`, `fpDiv32Eq_of_sail`, and `fpSqrt32Eq_of_sail` derive `FPSub32Eq`,
`FPMul32Eq`, `FPDiv32Eq`, and `FPSqrt32Eq` from the links `SailFPSub32`, `SailFPMul32`,
`SailFPDiv32`, and `SailFPSqrt32` likewise, and `fixedToFP64_32Eq_of_sail` derives
`FixedToFP64_32Eq` from `SailFixedToFP64_32`, which identifies Isla's 128-bit vector 0 with the
integer `fbits` 0 and the enumeration member `FPRounding_TIEEVEN` with the rounding mode, as
`SailFixedToFP` of `F7/Isla.lean` does, and `fixedToFP32_32Eq_of_sail` derives `FixedToFP32_32Eq`
from `SailFixedToFP32_32` likewise.  `fpToFixed32_64Eq_of_sail` derives `FPToFixed32_64Eq`, the
equation of FCVTZU X←S, from `SailFPToFixed32_64`, and `fpCompare32Eq_of_sail` derives
`FPCompare32Eq`, the equation of FCMP S, from `SailFPCompare32`, which names the abstract call
`FPCompare` on two 32-bit operands, as `SailFPCompare` names it on two 64-bit ones.
-/

open Sail Sail.ConcurrencyInterfaceV1 Armv9fp Armv9fp.Functions
open LeanExe.A64.Isla (Abstract)

namespace F7

/-- The link between the abstract call `FPAdd32` and the translation's FPAdd at 32 bits under
FPCR 0x02000000, which review supports. -/
def SailFPAdd32 (A : Abstract) : Prop :=
  ∀ (a b : BitVec 32) (s : State) (fi : Vector Bool 259) (ps : ProcState) (fpsr : BitVec 64)
    (v : BitVec 32) (s' : State), Hyp s.regs fi ps fpsr → (FPAdd a b fpcrV).run s = .ok v s' →
    A "FPAdd32" [.bits 32 a.toNat, .bits 32 b.toNat, islaFPCR fpcrV] = some (.bits 32 v.toNat)

theorem fpAdd32Eq_of_sail (A : Abstract) (h : SailFPAdd32 A) :
    LeanExe.A64.Isla.FPAdd32Eq A := by
  intro a b
  obtain ⟨s', hrun, -, -⟩ := fpAdd32_eq_f32Add a.toBitVec b.toBitVec _ _ _ _ (hyp_tcg unknown0)
  have e := h a.toBitVec b.toBitVec _ _ _ _ _ _ (hyp_tcg unknown0) hrun
  rw [islaFPCR_fpcrV, UInt32.ofBitVec_toBitVec, UInt32.ofBitVec_toBitVec] at e
  exact e

/-- The link between the abstract call `FPSub32` and the translation's FPSub at 32 bits under
FPCR 0x02000000, which review supports. -/
def SailFPSub32 (A : Abstract) : Prop :=
  ∀ (a b : BitVec 32) (s : State) (fi : Vector Bool 259) (ps : ProcState) (fpsr : BitVec 64)
    (v : BitVec 32) (s' : State), Hyp s.regs fi ps fpsr → (FPSub a b fpcrV).run s = .ok v s' →
    A "FPSub32" [.bits 32 a.toNat, .bits 32 b.toNat, islaFPCR fpcrV] = some (.bits 32 v.toNat)

theorem fpSub32Eq_of_sail (A : Abstract) (h : SailFPSub32 A) :
    LeanExe.A64.Isla.FPSub32Eq A := by
  intro a b
  obtain ⟨s', hrun, -, -⟩ := fpSub32_eq_f32Sub a.toBitVec b.toBitVec _ _ _ _ (hyp_tcg unknown0)
  have e := h a.toBitVec b.toBitVec _ _ _ _ _ _ (hyp_tcg unknown0) hrun
  rw [islaFPCR_fpcrV, UInt32.ofBitVec_toBitVec, UInt32.ofBitVec_toBitVec] at e
  exact e

/-- The link between the abstract call `FPMul32` and the translation's FPMul at 32 bits under
FPCR 0x02000000, which review supports. -/
def SailFPMul32 (A : Abstract) : Prop :=
  ∀ (a b : BitVec 32) (s : State) (fi : Vector Bool 259) (ps : ProcState) (fpsr : BitVec 64)
    (v : BitVec 32) (s' : State), Hyp s.regs fi ps fpsr → (FPMul a b fpcrV).run s = .ok v s' →
    A "FPMul32" [.bits 32 a.toNat, .bits 32 b.toNat, islaFPCR fpcrV] = some (.bits 32 v.toNat)

theorem fpMul32Eq_of_sail (A : Abstract) (h : SailFPMul32 A) :
    LeanExe.A64.Isla.FPMul32Eq A := by
  intro a b
  obtain ⟨s', hrun, -, -⟩ := fpMul32_eq_f32Mul a.toBitVec b.toBitVec _ _ _ _ (hyp_tcg unknown0)
  have e := h a.toBitVec b.toBitVec _ _ _ _ _ _ (hyp_tcg unknown0) hrun
  rw [islaFPCR_fpcrV, UInt32.ofBitVec_toBitVec, UInt32.ofBitVec_toBitVec] at e
  exact e

/-- The link between the abstract call `FPDiv32` and the translation's FPDiv at 32 bits under
FPCR 0x02000000, which review supports. -/
def SailFPDiv32 (A : Abstract) : Prop :=
  ∀ (a b : BitVec 32) (s : State) (fi : Vector Bool 259) (ps : ProcState) (fpsr : BitVec 64)
    (v : BitVec 32) (s' : State), Hyp s.regs fi ps fpsr → (FPDiv a b fpcrV).run s = .ok v s' →
    A "FPDiv32" [.bits 32 a.toNat, .bits 32 b.toNat, islaFPCR fpcrV] = some (.bits 32 v.toNat)

theorem fpDiv32Eq_of_sail (A : Abstract) (h : SailFPDiv32 A) :
    LeanExe.A64.Isla.FPDiv32Eq A := by
  intro a b
  obtain ⟨s', hrun, -, -⟩ := fpDiv32_eq_f32Div a.toBitVec b.toBitVec _ _ _ _ (hyp_tcg unknown0)
  have e := h a.toBitVec b.toBitVec _ _ _ _ _ _ (hyp_tcg unknown0) hrun
  rw [islaFPCR_fpcrV, UInt32.ofBitVec_toBitVec, UInt32.ofBitVec_toBitVec] at e
  exact e

/-- The link between the abstract call `FPSqrt32` and the translation's FPSqrt at 32 bits under
FPCR 0x02000000, which review supports. -/
def SailFPSqrt32 (A : Abstract) : Prop :=
  ∀ (a : BitVec 32) (s : State) (fi : Vector Bool 259) (ps : ProcState) (fpsr : BitVec 64)
    (v : BitVec 32) (s' : State), Hyp s.regs fi ps fpsr → (FPSqrt a fpcrV).run s = .ok v s' →
    A "FPSqrt32" [.bits 32 a.toNat, islaFPCR fpcrV] = some (.bits 32 v.toNat)

theorem fpSqrt32Eq_of_sail (A : Abstract) (h : SailFPSqrt32 A) :
    LeanExe.A64.Isla.FPSqrt32Eq A := by
  intro a
  obtain ⟨s', hrun, -, -⟩ := fpSqrt32_eq_f32Sqrt a.toBitVec _ _ _ _ (hyp_tcg unknown0)
  have e := h a.toBitVec _ _ _ _ _ _ (hyp_tcg unknown0) hrun
  rw [islaFPCR_fpcrV, UInt32.ofBitVec_toBitVec] at e
  exact e

/-- The link between the abstract call `FixedToFP64_32` and the translation's FixedToFP from a
64-bit unsigned integer with no fraction bits to 32 bits under FPCR 0x02000000, rounding to
nearest with ties to even, which review supports. -/
def SailFixedToFP64_32 (A : Abstract) : Prop :=
  ∀ (a : BitVec 64) (s : State) (fi : Vector Bool 259) (ps : ProcState) (fpsr : BitVec 64)
    (v : BitVec 32) (s' : State), Hyp s.regs fi ps fpsr →
    (FixedToFP a 0 true fpcrV .FPRounding_TIEEVEN 32).run s = .ok v s' →
    A "FixedToFP64_32" [.bits 64 a.toNat, .bits 128 0, .bool true, islaFPCR fpcrV,
      .enum "FPRounding_TIEEVEN"] = some (.bits 32 v.toNat)

theorem fixedToFP64_32Eq_of_sail (A : Abstract) (h : SailFixedToFP64_32 A) :
    LeanExe.A64.Isla.FixedToFP64_32Eq A := by
  intro a
  obtain ⟨s', hrun, -, -⟩ :=
    fixedToFP32_eq_f32ConvertI64U a.toBitVec _ _ _ _ (hyp_tcg unknown0)
  have e := h a.toBitVec _ _ _ _ _ _ (hyp_tcg unknown0) hrun
  rw [islaFPCR_fpcrV, UInt64.ofBitVec_toBitVec] at e
  exact e

/-- The link between the abstract call `FixedToFP32_32` and the translation's FixedToFP from a
32-bit signed integer with no fraction bits to 32 bits under FPCR 0x02000000, rounding to nearest
with ties to even, which review supports. -/
def SailFixedToFP32_32 (A : Abstract) : Prop :=
  ∀ (a : BitVec 32) (s : State) (fi : Vector Bool 259) (ps : ProcState) (fpsr : BitVec 64)
    (v : BitVec 32) (s' : State), Hyp s.regs fi ps fpsr →
    (FixedToFP a 0 false fpcrV .FPRounding_TIEEVEN 32).run s = .ok v s' →
    A "FixedToFP32_32" [.bits 32 a.toNat, .bits 128 0, .bool false, islaFPCR fpcrV,
      .enum "FPRounding_TIEEVEN"] = some (.bits 32 v.toNat)

theorem fixedToFP32_32Eq_of_sail (A : Abstract) (h : SailFixedToFP32_32 A) :
    LeanExe.A64.Isla.FixedToFP32_32Eq A := by
  intro a
  obtain ⟨s', hrun, -, -⟩ :=
    fixedToFP32_eq_f32ConvertI32S a.toBitVec _ _ _ _ (hyp_tcg unknown0)
  have e := h a.toBitVec _ _ _ _ _ _ (hyp_tcg unknown0) hrun
  rw [islaFPCR_fpcrV, UInt32.ofBitVec_toBitVec] at e
  exact e

/-- The link between the abstract call `FPToFixed32_64` and the translation's FPToFixed of a
32-bit operand to an unsigned 64-bit integer with no fraction bits under FPCR 0x02000000,
rounding toward zero, which review supports. -/
def SailFPToFixed32_64 (A : Abstract) : Prop :=
  ∀ (a : BitVec 32) (s : State) (fi : Vector Bool 259) (ps : ProcState) (fpsr v : BitVec 64)
    (s' : State), Hyp s.regs fi ps fpsr →
    (FPToFixed a 0 true fpcrV .FPRounding_ZERO 64).run s = .ok v s' →
    A "FPToFixed32_64" [.bits 32 a.toNat, .bits 128 0, .bool true, islaFPCR fpcrV,
      .enum "FPRounding_ZERO"] = some (.bits 64 v.toNat)

theorem fpToFixed32_64Eq_of_sail (A : Abstract) (h : SailFPToFixed32_64 A) :
    LeanExe.A64.Isla.FPToFixed32_64Eq A := by
  intro a
  obtain ⟨s', hrun, -, -⟩ :=
    fpToFixed32_eq_i64TruncSatF32U a.toBitVec _ _ _ _ (hyp_tcg unknown0)
  have e := h a.toBitVec _ _ _ _ _ _ (hyp_tcg unknown0) hrun
  rw [islaFPCR_fpcrV, UInt32.ofBitVec_toBitVec] at e
  exact e

/-- The link between the abstract call `FPCompare` on two 32-bit operands and the translation's
FPCompare at 32 bits under FPCR 0x02000000 with `signal_nans` false, which review supports. -/
def SailFPCompare32 (A : Abstract) : Prop :=
  ∀ (a b : BitVec 32) (s : State) (fi : Vector Bool 259) (ps : ProcState) (fpsr : BitVec 64)
    (v : BitVec 4) (s' : State), Hyp s.regs fi ps fpsr →
    (FPCompare a b false fpcrV).run s = .ok v s' →
    A "FPCompare" [.bits 32 a.toNat, .bits 32 b.toNat, .bool false, islaFPCR fpcrV] =
      some (.bits 4 v.toNat)

theorem fpCompare32Eq_of_sail (A : Abstract) (h : SailFPCompare32 A) :
    LeanExe.A64.Isla.FPCompare32Eq A := by
  intro a b
  obtain ⟨s', hrun, -, -⟩ :=
    fpCompare32_eq_fcmpNZCV32 a.toBitVec b.toBitVec _ _ _ _ (hyp_tcg unknown0)
  have e := h a.toBitVec b.toBitVec _ _ _ _ _ _ (hyp_tcg unknown0) hrun
  rw [islaFPCR_fpcrV, UInt32.ofBitVec_toBitVec, UInt32.ofBitVec_toBitVec, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_of_lt_of_eq (LeanExe.A64.Isla.fcmpNZCV32_lt a b)
      (by norm_num : (16 : ℕ) = 2 ^ 4))] at e
  exact e

end F7
