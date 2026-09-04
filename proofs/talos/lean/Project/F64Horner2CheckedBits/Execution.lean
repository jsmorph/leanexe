import Project.F64Horner2CheckedBits.Program
import Project.F64Horner2CheckedBits.Numerical
import Project.TalosCompat
import Interpreter.Wasm.Wp.Call

/-!
# Fuel-independent execution of guarded binary64 Horner evaluation

The helper theorem gives the compiler-generated raw-bit guard its exact
integer meaning.  The exported-entry theorem composes four calls to that
helper and follows both the accepted and rejected branches.  The decoded
control-type annotations are erased only at the WP boundary by
`Wasm.wp_iff_control_types`; they remain part of the exact generated module.

Floating-point instructions occur only in the accepted branch.  Their exact
Talos bit-model result is then connected to the source numerical theorem.
-/

namespace Project.F64Horner2CheckedBits.Spec

open Wasm
open Project.ProofKit

/-- Exact i64 result returned by the generated raw-bit guard helper. -/
private def guardResultModel (bits : UInt64) : UInt64 :=
  if F64Bounds.f64AbsBits bits ≤ 0x3FE0000000000000 then 1 else 0

/-- The generated helper returns one exactly when the sign-cleared encoding
is at most the encoding of one half, and otherwise returns zero. -/
theorem func0_exact
    (env : HostEnv Unit) (initial : Store Unit) (bits : UInt64) :
    TerminatesWith env Project.F64Horner2CheckedBits.«module» 0 initial
      [.i64 bits]
      (fun final values =>
        final = initial ∧ values = [.i64 (guardResultModel bits)]) := by
  apply TerminatesWith.of_wp_entry_for
    (f := Project.F64Horner2CheckedBits.func0Def)
  · simp [Project.F64Horner2CheckedBits.«module»]
  · change wp Project.F64Horner2CheckedBits.«module»
      Project.F64Horner2CheckedBits.func0 _ initial
      { params := [.i64 bits], locals := [.i64 0], values := [] } env
    unfold Project.F64Horner2CheckedBits.func0
    wp_run
    apply wp_iff_cons <;> try rfl
    by_cases hguard :
        F64Bounds.f64AbsBits bits ≤ (0x3FE0000000000000 : UInt64)
    · rw [if_pos (by simpa [F64Bounds.f64AbsBits] using hguard)]
      wp_run
      simp [Project.F64Horner2CheckedBits.func0Def, guardResultModel, hguard]
    · rw [if_neg (by
        have hnat :
            (0x3FE0000000000000 : UInt64).toNat <
              (F64Bounds.f64AbsBits bits).toNat := by
          rw [← Nat.not_le]
          intro hle
          exact hguard (UInt64.le_iff_toNat_le.mpr hle)
        have hlt :
            (0x3FE0000000000000 : UInt64) < F64Bounds.f64AbsBits bits :=
          UInt64.lt_iff_toNat_lt.mpr hnat
        simpa [F64Bounds.f64AbsBits] using hlt)]
      wp_run
      simp [Project.F64Horner2CheckedBits.func0Def, guardResultModel, hguard]

/-- Fuel-independent exact behavior of the compiler-generated exported entry.
Wasm's operand stack is top-first, so source arguments `x, c₂, c₁, c₀` are
supplied in reverse order, and source structure fields `status, bits` are
observed as `bits, status`. -/
def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
    (x c₂ c₁ c₀ : UInt64),
    TerminatesWith env m 1 initial
      [.i64 c₀, .i64 c₁, .i64 c₂, .i64 x]
      (fun final values =>
        final = initial ∧
          values =
            [.i64 (horner2ResultBitsModel x c₂ c₁ c₀),
             .i64 (horner2StatusModel x c₂ c₁ c₀)])

/-- The exact generated-WAT result additionally satisfies the total source
contract: accepted inputs carry the finite/error theorem, while rejected
inputs return status one and positive-zero result bits. -/
noncomputable def RealErrorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
    (x c₂ c₁ c₀ : UInt64),
    TerminatesWith env m 1 initial
      [.i64 c₀, .i64 c₁, .i64 c₂, .i64 x]
      (fun final values =>
        final = initial ∧
          values =
            [.i64 (horner2ResultBitsModel x c₂ c₁ c₀),
             .i64 (horner2StatusModel x c₂ c₁ c₀)] ∧
          CheckedResult x c₂ c₁ c₀
            (horner2StatusModel x c₂ c₁ c₀)
            (horner2ResultBitsModel x c₂ c₁ c₀))

/-- Every input takes one of five paths: the first failing guard rejects, or
all four guards pass and the four explicitly rounded Horner operations run.
All paths preserve the complete WebAssembly store. -/
theorem horner2CheckedBits_exact :
    ExactSpecFor Project.F64Horner2CheckedBits.«module» := by
  intro env initial x c₂ c₁ c₀
  apply TerminatesWith.of_wp_entry_for
    (f := Project.F64Horner2CheckedBits.func1Def)
  · simp [Project.F64Horner2CheckedBits.«module»]
  · change wp Project.F64Horner2CheckedBits.«module»
      Project.F64Horner2CheckedBits.func1 _ initial
      { params := [.i64 x, .i64 c₂, .i64 c₁, .i64 c₀],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold Project.F64Horner2CheckedBits.func1
    wp_run
    refine wp_call_tw (func0_exact env initial x) ?_
    rintro st₁ values₁ ⟨hst₁, rfl⟩
    subst st₁
    wp_run
    refine wp_iff_cons rfl ?_
    by_cases hx :
        F64Bounds.f64AbsBits x ≤ (0x3FE0000000000000 : UInt64)
    · rw [if_pos (by simp [guardResultModel, hx])]
      wp_run
      refine wp_call_tw (func0_exact env initial c₂) ?_
      rintro st₂ values₂ ⟨hst₂, rfl⟩
      subst st₂
      wp_run
      refine wp_iff_cons rfl ?_
      by_cases hc₂ :
          F64Bounds.f64AbsBits c₂ ≤ (0x3FE0000000000000 : UInt64)
      · rw [if_pos (by simp [guardResultModel, hc₂])]
        wp_run
        refine wp_call_tw (func0_exact env initial c₁) ?_
        rintro st₃ values₃ ⟨hst₃, rfl⟩
        subst st₃
        wp_run
        refine wp_iff_cons rfl ?_
        by_cases hc₁ :
            F64Bounds.f64AbsBits c₁ ≤ (0x3FE0000000000000 : UInt64)
        · rw [if_pos (by simp [guardResultModel, hc₁])]
          wp_run
          refine wp_call_tw (func0_exact env initial c₀) ?_
          rintro st₄ values₄ ⟨hst₄, rfl⟩
          subst st₄
          wp_run
          refine wp_iff_cons rfl ?_
          by_cases hc₀ :
              F64Bounds.f64AbsBits c₀ ≤ (0x3FE0000000000000 : UInt64)
          · rw [if_pos (by simp [guardResultModel, hc₀])]
            wp_run
            refine wp_iff_cons rfl ?_
            rw [if_pos (by simp)]
            wp_run
            refine wp_iff_cons rfl ?_
            rw [if_pos (by simp)]
            wp_run
            simp [Project.F64Horner2CheckedBits.func1Def,
              horner2ResultBitsModel, horner2StatusModel, horner2Guard,
              F64Bounds.boundedByHalfBits, horner2BitsModel,
              F64Numerical.horner2Bits, F64Numerical.hornerStepBits,
              Wasm.f64Mul, Wasm.f64Add, hx, hc₂, hc₁, hc₀]
          · rw [if_neg (by simp [guardResultModel, hc₀])]
            wp_run
            refine wp_iff_cons rfl ?_
            rw [if_neg (by simp)]
            wp_run
            refine wp_iff_cons rfl ?_
            rw [if_neg (by simp)]
            wp_run
            simp [Project.F64Horner2CheckedBits.func1Def,
              horner2ResultBitsModel, horner2StatusModel, horner2Guard,
              F64Bounds.boundedByHalfBits, hc₀]
        · rw [if_neg (by simp [guardResultModel, hc₁])]
          wp_run
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          wp_run
          simp [Project.F64Horner2CheckedBits.func1Def,
            horner2ResultBitsModel, horner2StatusModel, horner2Guard,
            F64Bounds.boundedByHalfBits, hc₁]
      · rw [if_neg (by simp [guardResultModel, hc₂])]
        wp_run
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        simp [Project.F64Horner2CheckedBits.func1Def,
          horner2ResultBitsModel, horner2StatusModel, horner2Guard,
          F64Bounds.boundedByHalfBits, hc₂]
    · rw [if_neg (by simp [guardResultModel, hx])]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      wp_run
      simp [Project.F64Horner2CheckedBits.func1Def,
        horner2ResultBitsModel, horner2StatusModel, horner2Guard,
        F64Bounds.boundedByHalfBits, hx]

/-- The decoded compiler-generated WAT has exactly the source contract on all
inputs, independently of interpreter fuel. -/
theorem horner2CheckedBits_wat_real_error :
    RealErrorSpecFor Project.F64Horner2CheckedBits.«module» := by
  intro env initial x c₂ c₁ c₀
  refine TerminatesWith.mono
    (horner2CheckedBits_exact env initial x c₂ c₁ c₀) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl,
    horner2CheckedBits_source_real_error x c₂ c₁ c₀⟩

#print axioms func0_exact
#print axioms horner2CheckedBits_exact
#print axioms horner2CheckedBits_wat_real_error

end Project.F64Horner2CheckedBits.Spec
