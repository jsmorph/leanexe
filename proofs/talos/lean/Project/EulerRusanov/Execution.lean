import Project.EulerRusanov.Program
import Project.EulerRusanov.Model
import Project.TalosCompat
import Interpreter.Wasm.Wp.Call

/-!
# Fuel-independent execution of the guarded Euler--Rusanov flux

The generated entry performs ten unsigned raw-word checks before reaching any
floating-point instruction.  The proof below follows those checks in their
exact short-circuit order.  Every first-failure path reaches the common reject
branch and returns status one with three positive-zero payload words.  If all
checks pass, symbolic execution of the straight-line binary64 body agrees
definitionally with `Model.checkedFluxBitsModel`.

The entry neither reads nor writes memory or globals.  Consequently every path
preserves the caller's complete WebAssembly store, for an arbitrary host
environment, and the result is independent of interpreter fuel.
-/

namespace Project.EulerRusanov.Spec

open Wasm

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-! ## Accepted-path staging

Running `wp_run` across the complete accepted branch constructs one enormous
weakest-precondition term containing every update of the 42 generated locals.
Instead, the following private layer splits that straight-line code at its
semantic boundaries.  Each lemma sees an opaque `rest`, so its simplifier can
consume only one small prefix: constants, left state, right state, and the
three flux components. -/

/-- Named contents of generated locals 6 through 47 on the accepted path. -/
private structure AcceptedWork where
  half : UInt64
  quarter : UInt64
  eighth : UInt64
  signMask : UInt64
  left : Model.SideBits
  right : Model.SideBits
  massJump : UInt64
  massMean : UInt64
  massDissipation : UInt64
  massResult : UInt64
  momentumJump : UInt64
  momentumMean : UInt64
  momentumDissipation : UInt64
  momentumResult : UInt64
  energyJump : UInt64
  energyMean : UInt64
  energyDissipation : UInt64
  energyResult : UInt64
  status : UInt64
  outputMass : UInt64
  outputMomentum : UInt64
  outputEnergy : UInt64

private def zeroSide : Model.SideBits :=
  { mass := 0
    velocitySquaredMass := 0
    halfKinetic := 0
    halfPressure := 0
    twoPressure := 0
    energyPressure := 0
    energy := 0
    enthalpyPressure := 0
    enthalpy := 0
    momentumFlux := 0
    energyFlux := 0 }

/-- All 42 compiler locals are initially binary integer zero. -/
private def initialWork : AcceptedWork :=
  { half := 0, quarter := 0, eighth := 0, signMask := 0
    left := zeroSide, right := zeroSide
    massJump := 0, massMean := 0, massDissipation := 0, massResult := 0
    momentumJump := 0, momentumMean := 0
    momentumDissipation := 0, momentumResult := 0
    energyJump := 0, energyMean := 0
    energyDissipation := 0, energyResult := 0
    status := 0, outputMass := 0, outputMomentum := 0, outputEnergy := 0 }

/-- Concrete interpreter frame corresponding to `AcceptedWork`. -/
private def acceptedFrame
    (rhoL uL pL rhoR uR pR : UInt64) (work : AcceptedWork) : Locals :=
  { params := [.i64 rhoL, .i64 uL, .i64 pL,
      .i64 rhoR, .i64 uR, .i64 pR]
    locals :=
      [.i64 work.half, .i64 work.quarter, .i64 work.eighth,
       .i64 work.signMask,
       .i64 work.left.mass, .i64 work.left.velocitySquaredMass,
       .i64 work.left.halfKinetic, .i64 work.left.halfPressure,
       .i64 work.left.twoPressure, .i64 work.left.energyPressure,
       .i64 work.left.energy, .i64 work.left.enthalpyPressure,
       .i64 work.left.enthalpy, .i64 work.left.momentumFlux,
       .i64 work.left.energyFlux,
       .i64 work.right.mass, .i64 work.right.velocitySquaredMass,
       .i64 work.right.halfKinetic, .i64 work.right.halfPressure,
       .i64 work.right.twoPressure, .i64 work.right.energyPressure,
       .i64 work.right.energy, .i64 work.right.enthalpyPressure,
       .i64 work.right.enthalpy, .i64 work.right.momentumFlux,
       .i64 work.right.energyFlux,
       .i64 work.massJump, .i64 work.massMean,
       .i64 work.massDissipation, .i64 work.massResult,
       .i64 work.momentumJump, .i64 work.momentumMean,
       .i64 work.momentumDissipation, .i64 work.momentumResult,
       .i64 work.energyJump, .i64 work.energyMean,
       .i64 work.energyDissipation, .i64 work.energyResult,
       .i64 work.status, .i64 work.outputMass,
       .i64 work.outputMomentum, .i64 work.outputEnergy]
    values := [] }

private def setupStep (work : AcceptedWork) : AcceptedWork :=
  { work with
    half := Model.halfBits
    quarter := Model.quarterBits
    eighth := Model.eighthBits
    signMask := Model.signMask }

/-- Per-side operation graph parameterized by the value actually held in
generated local 6.  After `setupStep` that value is `Model.halfBits`, making
this definition reduce to `Model.sideBits`. -/
private def sideWork (half rho u p : UInt64) : Model.SideBits :=
  let mass := IEEE64.mul rho u
  let velocitySquaredMass := IEEE64.mul mass u
  let halfKinetic := IEEE64.mul half velocitySquaredMass
  let halfPressure := IEEE64.mul half p
  let twoPressure := IEEE64.add p p
  let energyPressure := IEEE64.add twoPressure halfPressure
  let energy := IEEE64.add energyPressure halfKinetic
  let enthalpyPressure := IEEE64.add energyPressure p
  let enthalpy := IEEE64.add enthalpyPressure halfKinetic
  let momentumFlux := IEEE64.add velocitySquaredMass p
  let energyFlux := IEEE64.mul enthalpy u
  { mass, velocitySquaredMass, halfKinetic, halfPressure, twoPressure,
    energyPressure, energy, enthalpyPressure, enthalpy, momentumFlux,
    energyFlux }

private def leftStep (work : AcceptedWork)
    (rho u p : UInt64) : AcceptedWork :=
  { work with left := sideWork work.half rho u p }

private def rightStep (work : AcceptedWork)
    (rho u p : UInt64) : AcceptedWork :=
  { work with right := sideWork work.half rho u p }

/-- Four locals calculated for one Rusanov component.  Constants are read
from `work`, exactly as the generated code reads locals 6 through 9. -/
private structure ComponentWork where
  jump : UInt64
  mean : UInt64
  dissipation : UInt64
  result : UInt64

private def componentWork (work : AcceptedWork)
    (fluxL fluxR stateL stateR : UInt64) : ComponentWork :=
  let jump := IEEE64.add stateL (stateR ^^^ work.signMask)
  let mean := IEEE64.mul work.half (IEEE64.add fluxL fluxR)
  let dissipation := IEEE64.add
    (IEEE64.add (IEEE64.mul work.half jump)
      (IEEE64.mul work.quarter jump))
    (IEEE64.mul work.eighth jump)
  let result := IEEE64.add mean dissipation
  { jump, mean, dissipation, result }

private def massStep (work : AcceptedWork)
    (rhoL rhoR : UInt64) : AcceptedWork :=
  let component := componentWork work
    work.left.mass work.right.mass rhoL rhoR
  { work with
    massJump := component.jump
    massMean := component.mean
    massDissipation := component.dissipation
    massResult := component.result }

private def momentumStep (work : AcceptedWork) : AcceptedWork :=
  let component := componentWork work
    work.left.momentumFlux work.right.momentumFlux
    work.left.mass work.right.mass
  { work with
    momentumJump := component.jump
    momentumMean := component.mean
    momentumDissipation := component.dissipation
    momentumResult := component.result }

private def energyStep (work : AcceptedWork) : AcceptedWork :=
  let component := componentWork work
    work.left.energyFlux work.right.energyFlux
    work.left.energy work.right.energy
  { work with
    energyJump := component.jump
    energyMean := component.mean
    energyDissipation := component.dissipation
    energyResult := component.result }

private def finishStep (work : AcceptedWork) : AcceptedWork :=
  { work with
    status := 0
    outputMass := work.massResult
    outputMomentum := work.momentumResult
    outputEnergy := work.energyResult }

private def setupProgram : Program :=
  [.constI64 4602678819172646912, .localSet 6,
   .constI64 4598175219545276416, .localSet 7,
   .constI64 4593671619917905920, .localSet 8,
   .constI64 9223372036854775808, .localSet 9]

/-- Generated per-side operation graph.  `first` is local 10 for the left
state and local 21 for the right state. -/
private def sideProgram
    (rhoLocal uLocal pLocal first : Nat) : Program :=
  [.localGet rhoLocal, .f64ReinterpretI64,
   .localGet uLocal, .f64ReinterpretI64, .f64Mul,
   .i64ReinterpretF64, .localSet first,
   .localGet first, .f64ReinterpretI64,
   .localGet uLocal, .f64ReinterpretI64, .f64Mul,
   .i64ReinterpretF64, .localSet (first + 1),
   .localGet 6, .f64ReinterpretI64,
   .localGet (first + 1), .f64ReinterpretI64, .f64Mul,
   .i64ReinterpretF64, .localSet (first + 2),
   .localGet 6, .f64ReinterpretI64,
   .localGet pLocal, .f64ReinterpretI64, .f64Mul,
   .i64ReinterpretF64, .localSet (first + 3),
   .localGet pLocal, .f64ReinterpretI64,
   .localGet pLocal, .f64ReinterpretI64, .f64Add,
   .i64ReinterpretF64, .localSet (first + 4),
   .localGet (first + 4), .f64ReinterpretI64,
   .localGet (first + 3), .f64ReinterpretI64, .f64Add,
   .i64ReinterpretF64, .localSet (first + 5),
   .localGet (first + 5), .f64ReinterpretI64,
   .localGet (first + 2), .f64ReinterpretI64, .f64Add,
   .i64ReinterpretF64, .localSet (first + 6),
   .localGet (first + 5), .f64ReinterpretI64,
   .localGet pLocal, .f64ReinterpretI64, .f64Add,
   .i64ReinterpretF64, .localSet (first + 7),
   .localGet (first + 7), .f64ReinterpretI64,
   .localGet (first + 2), .f64ReinterpretI64, .f64Add,
   .i64ReinterpretF64, .localSet (first + 8),
   .localGet (first + 1), .f64ReinterpretI64,
   .localGet pLocal, .f64ReinterpretI64, .f64Add,
   .i64ReinterpretF64, .localSet (first + 9),
   .localGet (first + 8), .f64ReinterpretI64,
   .localGet uLocal, .f64ReinterpretI64, .f64Mul,
   .i64ReinterpretF64, .localSet (first + 10)]

private def leftSideProgram : Program := sideProgram 0 1 2 10
private def rightSideProgram : Program := sideProgram 3 4 5 21

/-- Generated jump, mean, dyadic dissipation, and final addition for one
component.  `first` is 32, 36, or 40. -/
private def componentProgram
    (fluxL fluxR stateL stateR first : Nat) : Program :=
  [.localGet stateL, .f64ReinterpretI64,
   .localGet stateR, .localGet 9, .xorI64, .f64ReinterpretI64,
   .f64Add, .i64ReinterpretF64, .localSet first,
   .localGet 6, .f64ReinterpretI64,
   .localGet fluxL, .f64ReinterpretI64,
   .localGet fluxR, .f64ReinterpretI64,
   .f64Add, .i64ReinterpretF64, .f64ReinterpretI64,
   .f64Mul, .i64ReinterpretF64, .localSet (first + 1),
   .localGet 6, .f64ReinterpretI64,
   .localGet first, .f64ReinterpretI64,
   .f64Mul, .i64ReinterpretF64, .f64ReinterpretI64,
   .localGet 7, .f64ReinterpretI64,
   .localGet first, .f64ReinterpretI64,
   .f64Mul, .i64ReinterpretF64, .f64ReinterpretI64,
   .f64Add, .i64ReinterpretF64, .f64ReinterpretI64,
   .localGet 8, .f64ReinterpretI64,
   .localGet first, .f64ReinterpretI64,
   .f64Mul, .i64ReinterpretF64, .f64ReinterpretI64,
   .f64Add, .i64ReinterpretF64, .localSet (first + 2),
   .localGet (first + 1), .f64ReinterpretI64,
   .localGet (first + 2), .f64ReinterpretI64,
   .f64Add, .i64ReinterpretF64, .localSet (first + 3)]

private def massProgram : Program := componentProgram 10 21 0 3 32
private def momentumProgram : Program := componentProgram 19 30 10 21 36
private def energyProgram : Program := componentProgram 20 31 16 27 40

private def finishProgram : Program :=
  [.constI64 0, .localSet 44,
   .localGet 35, .localSet 45,
   .localGet 39, .localSet 46,
   .localGet 43, .localSet 47]

/-- Exact decomposition of the generated accepted branch. -/
private def acceptedProgram : Program :=
  setupProgram ++ leftSideProgram ++ rightSideProgram ++ massProgram ++
    momentumProgram ++ energyProgram ++ finishProgram

private theorem wp_setupProgram
    (rhoL uL pL rhoR uR pR : UInt64) (work : AcceptedWork)
    {m : Module} {env : HostEnv Unit} {store : Store Unit}
    {rest : Program} {Q : Assertion Unit}
    (hrest : wp m rest Q store
      (acceptedFrame rhoL uL pL rhoR uR pR (setupStep work)) env) :
    wp m (setupProgram ++ rest) Q store
      (acceptedFrame rhoL uL pL rhoR uR pR work) env := by
  simpa only [setupProgram, List.cons_append, List.nil_append, wp_simp,
    acceptedFrame, setupStep, Model.halfBits, Model.quarterBits,
    Model.eighthBits, Model.signMask, Locals.get, Locals.set?,
    Function.toLocals, Function.numParams, List.take, List.drop,
    List.replicate, List.length, List.map, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    reduceIte, ite_true, ite_false,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
    ValueType.zero] using hrest

private theorem wp_leftSideProgram
    (rhoL uL pL rhoR uR pR : UInt64) (work : AcceptedWork)
    {m : Module} {env : HostEnv Unit} {store : Store Unit}
    {rest : Program} {Q : Assertion Unit}
    (hrest : wp m rest Q store
      (acceptedFrame rhoL uL pL rhoR uR pR
        (leftStep work rhoL uL pL)) env) :
    wp m (leftSideProgram ++ rest) Q store
      (acceptedFrame rhoL uL pL rhoR uR pR work) env := by
  simpa only [leftSideProgram, sideProgram, List.cons_append,
    List.nil_append, wp_simp, acceptedFrame, leftStep, sideWork,
    Wasm.f64Mul, Wasm.f64Add, Locals.get, Locals.set?,
    Function.toLocals, Function.numParams, List.take, List.drop,
    List.replicate, List.length, List.map, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    reduceIte, ite_true, ite_false,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
    ValueType.zero] using hrest

private theorem wp_rightSideProgram
    (rhoL uL pL rhoR uR pR : UInt64) (work : AcceptedWork)
    {m : Module} {env : HostEnv Unit} {store : Store Unit}
    {rest : Program} {Q : Assertion Unit}
    (hrest : wp m rest Q store
      (acceptedFrame rhoL uL pL rhoR uR pR
        (rightStep work rhoR uR pR)) env) :
    wp m (rightSideProgram ++ rest) Q store
      (acceptedFrame rhoL uL pL rhoR uR pR work) env := by
  simpa only [rightSideProgram, sideProgram, List.cons_append,
    List.nil_append, wp_simp, acceptedFrame, rightStep, sideWork,
    Wasm.f64Mul, Wasm.f64Add, Locals.get, Locals.set?,
    Function.toLocals, Function.numParams, List.take, List.drop,
    List.replicate, List.length, List.map, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    reduceIte, ite_true, ite_false,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
    ValueType.zero] using hrest

private theorem wp_massProgram
    (rhoL uL pL rhoR uR pR : UInt64) (work : AcceptedWork)
    {m : Module} {env : HostEnv Unit} {store : Store Unit}
    {rest : Program} {Q : Assertion Unit}
    (hrest : wp m rest Q store
      (acceptedFrame rhoL uL pL rhoR uR pR
        (massStep work rhoL rhoR)) env) :
    wp m (massProgram ++ rest) Q store
      (acceptedFrame rhoL uL pL rhoR uR pR work) env := by
  simpa only [massProgram, componentProgram, List.cons_append,
    List.nil_append, wp_simp, acceptedFrame, massStep, componentWork,
    Wasm.f64Mul, Wasm.f64Add, Locals.get, Locals.set?,
    Function.toLocals, Function.numParams, List.take, List.drop,
    List.replicate, List.length, List.map, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    reduceIte, ite_true, ite_false,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
    ValueType.zero] using hrest

private theorem wp_momentumProgram
    (rhoL uL pL rhoR uR pR : UInt64) (work : AcceptedWork)
    {m : Module} {env : HostEnv Unit} {store : Store Unit}
    {rest : Program} {Q : Assertion Unit}
    (hrest : wp m rest Q store
      (acceptedFrame rhoL uL pL rhoR uR pR
        (momentumStep work)) env) :
    wp m (momentumProgram ++ rest) Q store
      (acceptedFrame rhoL uL pL rhoR uR pR work) env := by
  simpa only [momentumProgram, componentProgram, List.cons_append,
    List.nil_append, wp_simp, acceptedFrame, momentumStep, componentWork,
    Wasm.f64Mul, Wasm.f64Add, Locals.get, Locals.set?,
    Function.toLocals, Function.numParams, List.take, List.drop,
    List.replicate, List.length, List.map, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    reduceIte, ite_true, ite_false,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
    ValueType.zero] using hrest

private theorem wp_energyProgram
    (rhoL uL pL rhoR uR pR : UInt64) (work : AcceptedWork)
    {m : Module} {env : HostEnv Unit} {store : Store Unit}
    {rest : Program} {Q : Assertion Unit}
    (hrest : wp m rest Q store
      (acceptedFrame rhoL uL pL rhoR uR pR
        (energyStep work)) env) :
    wp m (energyProgram ++ rest) Q store
      (acceptedFrame rhoL uL pL rhoR uR pR work) env := by
  simpa only [energyProgram, componentProgram, List.cons_append,
    List.nil_append, wp_simp, acceptedFrame, energyStep, componentWork,
    Wasm.f64Mul, Wasm.f64Add, Locals.get, Locals.set?,
    Function.toLocals, Function.numParams, List.take, List.drop,
    List.replicate, List.length, List.map, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    reduceIte, ite_true, ite_false,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
    ValueType.zero] using hrest

private theorem wp_finishProgram
    (rhoL uL pL rhoR uR pR : UInt64) (work : AcceptedWork)
    {m : Module} {env : HostEnv Unit} {store : Store Unit}
    {rest : Program} {Q : Assertion Unit}
    (hrest : wp m rest Q store
      (acceptedFrame rhoL uL pL rhoR uR pR (finishStep work)) env) :
    wp m (finishProgram ++ rest) Q store
      (acceptedFrame rhoL uL pL rhoR uR pR work) env := by
  simpa only [finishProgram, List.cons_append, List.nil_append, wp_simp,
    acceptedFrame, finishStep, Locals.get, Locals.set?,
    Function.toLocals, Function.numParams, List.take, List.drop,
    List.replicate, List.length, List.map, List.set,
    List.getElem?_cons_zero, List.getElem?_cons_succ, List.getElem?_nil,
    reduceIte, ite_true, ite_false,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
    ValueType.zero] using hrest

/-- Pure normalization of the seven staged updates.  This is intentionally
separate from WP reduction: no interpreter frame or program occurs here. -/
private theorem completedWork_resultValues
    (rhoL uL pL rhoR uR pR : UInt64)
    (hGuard : Model.eulerGuard rhoL uL pL rhoR uR pR = true) :
    let completed := finishStep <| energyStep <| momentumStep <|
      massStep
        (rightStep
          (leftStep (setupStep initialWork) rhoL uL pL)
          rhoR uR pR)
        rhoL rhoR
    [.i64 completed.outputEnergy, .i64 completed.outputMomentum,
      .i64 completed.outputMass, .i64 completed.status] =
      Model.resultValues rhoL uL pL rhoR uR pR := by
  simp [finishStep, energyStep, momentumStep, massStep, componentWork,
    rightStep, leftStep, sideWork, setupStep, initialWork, zeroSide,
    Model.resultValues, Model.checkedFluxBitsModel, Model.rusanovBits,
    Model.sideBits,
    Model.rusanovComponentBits, Model.jumpBits, Model.negateBits,
    Model.meanBits, Model.dissipationBits, hGuard]

/-- Fuel-independent exact behavior of the compiler-generated exported entry.
Wasm's operand stack is top-first, so the six source arguments are supplied in
reverse order.  The four source result fields are likewise observed in reverse
order, as recorded by `Model.resultValues`. -/
def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit)
    (rhoL uL pL rhoR uR pR : UInt64),
    TerminatesWith env m 0 initial
      [.i64 pR, .i64 uR, .i64 rhoR, .i64 pL, .i64 uL, .i64 rhoL]
      (fun final values =>
        final = initial ∧
          values = Model.resultValues rhoL uL pL rhoR uR pR)

/-- Every input takes one of eleven semantic paths in any module whose function
zero is the generated guarded flux entry: the first failing raw-word guard
rejects without floating-point evaluation, or all ten guards pass and the
explicitly rounded Euler--Rusanov operation graph executes.  All paths preserve
the complete WebAssembly store. -/
theorem rusanovFluxCheckedBits_exact_in_module {m : Wasm.Module}
    (hFunc : m.funcs[0 - m.imports.length]? =
      some Project.EulerRusanov.func0Def)
    (hNoImport : m.imports[0]? = none) :
    ExactSpecFor m := by
  intro env initial rhoL uL pL rhoR uR pR
  refine TerminatesWith.of_wp_entry_for
    (f := Project.EulerRusanov.func0Def) hFunc ?_ hNoImport
  · change wp m
      Project.EulerRusanov.func0 _ initial
      { params := [.i64 rhoL, .i64 uL, .i64 pL,
          .i64 rhoR, .i64 uR, .i64 pR],
        locals :=
          [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
           .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
           .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
           .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
           .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
           .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
           .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold Project.EulerRusanov.func0
    wp_run
    refine wp_iff_cons rfl ?_
    by_cases hRhoLMin : Model.rhoMinBits ≤ rhoL
    · rw [ite_eq_left (by simpa [Model.rhoMinBits] using hRhoLMin)]
      wp_run
      refine wp_iff_cons rfl ?_
      by_cases hRhoLMax : rhoL ≤ Model.rhoMaxBits
      · rw [ite_eq_left (by simpa [Model.rhoMaxBits] using hRhoLMax)]
        wp_run
        refine wp_iff_cons rfl ?_
        by_cases hPLMin : Model.pressureMinBits ≤ pL
        · rw [ite_eq_left (by simpa [Model.pressureMinBits] using hPLMin)]
          wp_run
          refine wp_iff_cons rfl ?_
          by_cases hPLRho : pL ≤ rhoL
          · rw [ite_eq_left (by simpa using hPLRho)]
            wp_run
            refine wp_iff_cons rfl ?_
            by_cases hUL :
                Model.magnitudeBits uL ≤ Model.velocityMaxBits
            · rw [ite_eq_left (by simpa [Model.magnitudeBits,
                  Model.magnitudeMask, Model.velocityMaxBits] using hUL)]
              wp_run
              refine wp_iff_cons rfl ?_
              by_cases hRhoRMin : Model.rhoMinBits ≤ rhoR
              · rw [ite_eq_left (by
                    simpa [Model.rhoMinBits] using hRhoRMin)]
                wp_run
                refine wp_iff_cons rfl ?_
                by_cases hRhoRMax : rhoR ≤ Model.rhoMaxBits
                · rw [ite_eq_left (by
                      simpa [Model.rhoMaxBits] using hRhoRMax)]
                  wp_run
                  refine wp_iff_cons rfl ?_
                  by_cases hPRMin : Model.pressureMinBits ≤ pR
                  · rw [ite_eq_left (by
                        simpa [Model.pressureMinBits] using hPRMin)]
                    wp_run
                    refine wp_iff_cons rfl ?_
                    by_cases hPRRho : pR ≤ rhoR
                    · rw [ite_eq_left (by simpa using hPRRho)]
                      wp_run
                      refine wp_iff_cons rfl ?_
                      by_cases hUR :
                          Model.magnitudeBits uR ≤ Model.velocityMaxBits
                      · rw [ite_eq_left (by simpa [Model.magnitudeBits,
                            Model.magnitudeMask, Model.velocityMaxBits]
                            using hUR)]
                        wp_run
                        refine wp_iff_cons rfl ?_
                        rw [ite_eq_left (by simp)]
                        wp_run
                        refine wp_iff_cons rfl ?_
                        rw [ite_eq_left (by simp)]
                        have hGuard :
                            Model.eulerGuard rhoL uL pL rhoR uR pR = true := by
                          simp [Model.eulerGuard, hRhoLMin, hRhoLMax,
                            hPLMin, hPLRho, hUL, hRhoRMin, hRhoRMax,
                            hPRMin, hPRRho, hUR]
                        let work0 := initialWork
                        let work1 := setupStep work0
                        let work2 := leftStep work1 rhoL uL pL
                        let work3 := rightStep work2 rhoR uR pR
                        let work4 := massStep work3 rhoL rhoR
                        let work5 := momentumStep work4
                        let work6 := energyStep work5
                        let work7 := finishStep work6
                        have hValues :
                            [.i64 work7.outputEnergy,
                              .i64 work7.outputMomentum,
                              .i64 work7.outputMass,
                              .i64 work7.status] =
                                Model.resultValues rhoL uL pL rhoR uR pR := by
                          dsimp only [work7, work6, work5, work4, work3,
                            work2, work1, work0]
                          exact completedWork_resultValues
                            rhoL uL pL rhoR uR pR hGuard
                        change wp m
                          acceptedProgram _ initial
                          (acceptedFrame rhoL uL pL rhoR uR pR work0) env
                        unfold acceptedProgram
                        refine wp_setupProgram
                          rhoL uL pL rhoR uR pR work0 ?_
                        refine wp_leftSideProgram
                          rhoL uL pL rhoR uR pR work1 ?_
                        refine wp_rightSideProgram
                          rhoL uL pL rhoR uR pR work2 ?_
                        refine wp_massProgram
                          rhoL uL pL rhoR uR pR work3 ?_
                        refine wp_momentumProgram
                          rhoL uL pL rhoR uR pR work4 ?_
                        refine wp_energyProgram
                          rhoL uL pL rhoR uR pR work5 ?_
                        refine wp_finishProgram
                          rhoL uL pL rhoR uR pR work6 ?_
                        change wp m [] _ initial
                          (acceptedFrame rhoL uL pL rhoR uR pR work7) env
                        wp_run [acceptedFrame]
                        simp [Project.EulerRusanov.func0Def, hValues,
                          Model.resultValues, Model.checkedFluxBitsModel,
                          hGuard]
                      · rw [ite_eq_right (by simpa [Model.magnitudeBits,
                            Model.magnitudeMask, Model.velocityMaxBits]
                            using hUR)]
                        wp_run
                        repeat
                          first
                          | refine wp_iff_cons rfl ?_
                            rw [ite_eq_right (by simp)]
                            wp_run
                        have hGuard :
                            Model.eulerGuard rhoL uL pL rhoR uR pR = false := by
                          simp [Model.eulerGuard, hUR]
                        simp [Project.EulerRusanov.func0Def,
                          Model.resultValues, Model.checkedFluxBitsModel, hGuard]
                    · rw [ite_eq_right (by simpa using hPRRho)]
                      wp_run
                      repeat
                        first
                        | refine wp_iff_cons rfl ?_
                          rw [ite_eq_right (by simp)]
                          wp_run
                      have hGuard :
                          Model.eulerGuard rhoL uL pL rhoR uR pR = false := by
                        simp [Model.eulerGuard, hPRRho]
                      simp [Project.EulerRusanov.func0Def,
                        Model.resultValues, Model.checkedFluxBitsModel, hGuard]
                  · rw [ite_eq_right (by
                        simpa [Model.pressureMinBits] using hPRMin)]
                    wp_run
                    repeat
                      first
                      | refine wp_iff_cons rfl ?_
                        rw [ite_eq_right (by simp)]
                        wp_run
                    have hGuard :
                        Model.eulerGuard rhoL uL pL rhoR uR pR = false := by
                      simp [Model.eulerGuard, hPRMin]
                    simp [Project.EulerRusanov.func0Def,
                      Model.resultValues, Model.checkedFluxBitsModel, hGuard]
                · rw [ite_eq_right (by
                      simpa [Model.rhoMaxBits] using hRhoRMax)]
                  wp_run
                  repeat
                    first
                    | refine wp_iff_cons rfl ?_
                      rw [ite_eq_right (by simp)]
                      wp_run
                  have hGuard :
                      Model.eulerGuard rhoL uL pL rhoR uR pR = false := by
                    simp [Model.eulerGuard, hRhoRMax]
                  simp [Project.EulerRusanov.func0Def,
                    Model.resultValues, Model.checkedFluxBitsModel, hGuard]
              · rw [ite_eq_right (by
                    simpa [Model.rhoMinBits] using hRhoRMin)]
                wp_run
                repeat
                  first
                  | refine wp_iff_cons rfl ?_
                    rw [ite_eq_right (by simp)]
                    wp_run
                have hGuard :
                    Model.eulerGuard rhoL uL pL rhoR uR pR = false := by
                  simp [Model.eulerGuard, hRhoRMin]
                simp [Project.EulerRusanov.func0Def,
                  Model.resultValues, Model.checkedFluxBitsModel, hGuard]
            · rw [ite_eq_right (by simpa [Model.magnitudeBits,
                  Model.magnitudeMask, Model.velocityMaxBits] using hUL)]
              wp_run
              repeat
                first
                | refine wp_iff_cons rfl ?_
                  rw [ite_eq_right (by simp)]
                  wp_run
              have hGuard :
                  Model.eulerGuard rhoL uL pL rhoR uR pR = false := by
                simp [Model.eulerGuard, hUL]
              simp [Project.EulerRusanov.func0Def,
                Model.resultValues, Model.checkedFluxBitsModel, hGuard]
          · rw [ite_eq_right (by simpa using hPLRho)]
            wp_run
            repeat
              first
              | refine wp_iff_cons rfl ?_
                rw [ite_eq_right (by simp)]
                wp_run
            have hGuard :
                Model.eulerGuard rhoL uL pL rhoR uR pR = false := by
              simp [Model.eulerGuard, hPLRho]
            simp [Project.EulerRusanov.func0Def,
              Model.resultValues, Model.checkedFluxBitsModel, hGuard]
        · rw [ite_eq_right (by
              simpa [Model.pressureMinBits] using hPLMin)]
          wp_run
          repeat
            first
            | refine wp_iff_cons rfl ?_
              rw [ite_eq_right (by simp)]
              wp_run
          have hGuard :
              Model.eulerGuard rhoL uL pL rhoR uR pR = false := by
            simp [Model.eulerGuard, hPLMin]
          simp [Project.EulerRusanov.func0Def,
            Model.resultValues, Model.checkedFluxBitsModel, hGuard]
      · rw [ite_eq_right (by simpa [Model.rhoMaxBits] using hRhoLMax)]
        wp_run
        repeat
          first
          | refine wp_iff_cons rfl ?_
            rw [ite_eq_right (by simp)]
            wp_run
        have hGuard :
            Model.eulerGuard rhoL uL pL rhoR uR pR = false := by
          simp [Model.eulerGuard, hRhoLMax]
        simp [Project.EulerRusanov.func0Def,
          Model.resultValues, Model.checkedFluxBitsModel, hGuard]
    · rw [ite_eq_right (by simpa [Model.rhoMinBits] using hRhoLMin)]
      wp_run
      repeat
        first
        | refine wp_iff_cons rfl ?_
          rw [ite_eq_right (by simp)]
          wp_run
      have hGuard :
          Model.eulerGuard rhoL uL pL rhoR uR pR = false := by
        simp [Model.eulerGuard, hRhoLMin]
      simp [Project.EulerRusanov.func0Def,
        Model.resultValues, Model.checkedFluxBitsModel, hGuard]

/-- Exact behavior of the standalone compiler artifact, retained as the public
specialization of the module-polymorphic execution theorem. -/
theorem rusanovFluxCheckedBits_exact :
    ExactSpecFor Project.EulerRusanov.«module» :=
  rusanovFluxCheckedBits_exact_in_module
    (m := Project.EulerRusanov.«module») (by rfl) (by rfl)

#print axioms rusanovFluxCheckedBits_exact_in_module
#print axioms rusanovFluxCheckedBits_exact

end Project.EulerRusanov.Spec
