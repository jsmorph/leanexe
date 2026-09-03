import Project.F64MulBits.Program
import CodeLib.IEEE64.Operations
import Interpreter.Wasm.Wp.Tactic

/-!
# Quantitative specification for `mulBits`

The Lean entry point is a restricted compiler intrinsic over raw `UInt64`
binary64 encodings.  Its proof contract is the pure Talos multiplication model;
Lean's native `Float` evaluator remains only an executable regression oracle.
The generated WAT keeps the public integer ABI and performs two
reinterpretations, one `f64.mul`, and a final reinterpretation back to `i64`.
-/

namespace Project.F64MulBits.Spec

open Wasm

/-- Pure proof-visible meaning of the LeanExe `mulBits` intrinsic. -/
def mulBitsModel (left right : UInt64) : UInt64 :=
  Wasm.IEEE64.mul left right

/-- The quantitative binary64 contract shared by the source specification and
the generated WAT theorem. -/
noncomputable def RealErrorResult
    (left right result : UInt64) : Prop :=
  CodeLib.IEEE64.Finite result ∧
    |CodeLib.IEEE64.value result -
        CodeLib.IEEE64.value left * CodeLib.IEEE64.value right| ≤
      CodeLib.IEEE64.multiplicationEpsilon

/-- Source-level contract associated with
`LeanExe.Examples.Float64Bits.mulBits`.  The association is specification
metadata; the trusted meaning is `mulBitsModel`, not native floating-point
evaluation. -/
@[spec_of "lean" "LeanExe.Examples.Float64Bits.mulBits"]
noncomputable def MulBitsSourceSpec : Prop :=
  ∀ (left right : UInt64),
    CodeLib.IEEE64.Finite left →
    CodeLib.IEEE64.Finite right →
    |CodeLib.IEEE64.value left| ≤ 1 →
    |CodeLib.IEEE64.value right| ≤ 1 →
    RealErrorResult left right (mulBitsModel left right)

/-- The compiler-recognized LeanExe intrinsic satisfies the finite-result and
absolute real-error contract supplied by Talos's pure binary64 model. -/
@[proves Project.F64MulBits.Spec.MulBitsSourceSpec]
theorem mulBits_source_real_error : MulBitsSourceSpec := by
  intro left right hleft hright hleftBound hrightBound
  exact CodeLib.IEEE64.mul_real_error left right hleft hright
    hleftBound hrightBound

/-- Fuel-independent exact execution property for the generated entry in an
arbitrary module. -/
def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (left right : UInt64),
    TerminatesWith env m 0 initial [.i64 right, .i64 left]
      (fun final values =>
        final = initial ∧
          values = [.i64 (mulBitsModel left right)])

/-- The generated entry returns the modeled product, preserves the store, and
satisfies exactly the same numerical result contract as the source spec. -/
noncomputable def RealErrorSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (left right : UInt64),
    CodeLib.IEEE64.Finite left →
    CodeLib.IEEE64.Finite right →
    |CodeLib.IEEE64.value left| ≤ 1 →
    |CodeLib.IEEE64.value right| ≤ 1 →
    TerminatesWith env m 0 initial [.i64 right, .i64 left]
      (fun final values =>
        final = initial ∧
          values = [.i64 (mulBitsModel left right)] ∧
          RealErrorResult left right (mulBitsModel left right))

/-- The generated WAT entry executes to the pure modeled multiplication for
all input bit patterns and leaves the WebAssembly store unchanged. -/
theorem mulBits_exact : ExactSpecFor Project.F64MulBits.«module» := by
  intro env initial left right
  apply TerminatesWith.of_wp_entry_for (f := Project.F64MulBits.func0Def)
  · simp [Project.F64MulBits.«module»]
  · change wp Project.F64MulBits.«module» Project.F64MulBits.func0 _ initial
      { params := [.i64 left, .i64 right],
        locals := [.i64 0], values := [] } env
    unfold Project.F64MulBits.func0
    wp_run
    simp [mulBitsModel, Wasm.f64Mul, Project.F64MulBits.func0Def]

/-- The exact generated WAT execution satisfies the source numerical contract:
the result is finite and differs from the real product by at most `2^-52`. -/
theorem mulBits_wat_real_error :
    RealErrorSpecFor Project.F64MulBits.«module» := by
  intro env initial left right hleft hright hleftBound hrightBound
  refine TerminatesWith.mono (mulBits_exact env initial left right) ?_
  rintro final values ⟨rfl, rfl⟩
  exact ⟨rfl, rfl,
    mulBits_source_real_error left right hleft hright hleftBound hrightBound⟩

/-! ## Explicit relational trace

This second execution proof exposes every instruction transition.  It is
independent of interpreter fuel and makes the integer/floating reinterpretation
boundary visible in the theorem source.
-/

def mulBitsConfig (initial : Store Unit) (left right : UInt64) :
    SmallStep.Config Unit :=
  { expr := .running
      { locals :=
          { params := [.i64 left, .i64 right], locals := [.i64 0] }
        code := Project.F64MulBits.func0
        resultArity := 1
        callerRemainder := [] }
    store :=
      { runtime :=
          { instances :=
              #[{ module := Project.F64MulBits.«module», host := {} }]
            entry := ⟨0⟩ }
        wasm := initial } }

theorem mulBits_steps (initial : Store Unit) (left right : UInt64) :
    SmallStep.Steps (mulBitsConfig initial left right)
      [(.instruction (.localGet 0)),
       (.instruction .f64ReinterpretI64),
       (.instruction (.localGet 1)),
       (.instruction .f64ReinterpretI64),
       (.instruction .f64Mul),
       (.instruction .i64ReinterpretF64),
       (.instruction (.localSet 2)),
       (.instruction (.localGet 2)),
       (.administrative .finish)]
      ⟨.done [.i64 (mulBitsModel left right)],
        (mulBitsConfig initial left right).store⟩ := by
  apply SmallStep.Steps.cons (.localGet rfl)
  apply SmallStep.Steps.cons (.scalarFloat1 rfl rfl)
  apply SmallStep.Steps.cons (.localGet rfl)
  apply SmallStep.Steps.cons (.scalarFloat1 rfl rfl)
  apply SmallStep.Steps.cons (.scalarFloat2 rfl rfl rfl)
  apply SmallStep.Steps.cons (.scalarFloat1 rfl rfl)
  apply SmallStep.Steps.cons (.localSet rfl)
  apply SmallStep.Steps.cons (.localGet rfl)
  apply SmallStep.Steps.cons .finish
  simpa [mulBitsConfig, Project.F64MulBits.func0, mulBitsModel,
    Wasm.f64Mul] using
    (SmallStep.Steps.refl
      (⟨.done [.i64 (mulBitsModel left right)],
        (mulBitsConfig initial left right).store⟩ : SmallStep.Config Unit))

theorem mulBits_smallStep_exact
    (initial : Store Unit) (left right : UInt64) :
    SmallStep.TerminatesWith (mulBitsConfig initial left right)
      (fun values final =>
        values = [.i64 (mulBitsModel left right)] ∧
          final = (mulBitsConfig initial left right).store) :=
  SmallStep.TerminatesWith.of_steps (mulBits_steps initial left right)
    ⟨rfl, rfl⟩

theorem mulBits_smallStep_real_error
    (initial : Store Unit) (left right : UInt64)
    (hleft : CodeLib.IEEE64.Finite left)
    (hright : CodeLib.IEEE64.Finite right)
    (hleftBound : |CodeLib.IEEE64.value left| ≤ 1)
    (hrightBound : |CodeLib.IEEE64.value right| ≤ 1) :
    SmallStep.TerminatesWith (mulBitsConfig initial left right)
      (fun values final =>
        values = [.i64 (mulBitsModel left right)] ∧
          final = (mulBitsConfig initial left right).store ∧
          RealErrorResult left right (mulBitsModel left right)) := by
  refine (mulBits_smallStep_exact initial left right).mono ?_
  rintro values final ⟨rfl, rfl⟩
  exact ⟨rfl, rfl,
    mulBits_source_real_error left right hleft hright hleftBound hrightBound⟩

#print axioms mulBits_source_real_error
#print axioms mulBits_exact
#print axioms mulBits_wat_real_error
#print axioms mulBits_steps
#print axioms mulBits_smallStep_exact
#print axioms mulBits_smallStep_real_error

end Project.F64MulBits.Spec
