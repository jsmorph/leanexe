import Examples.Euler.Outward

/-! The compiled flux and face-update kernels of the reconstructed Euler solver compute their
Lean definitions. -/

namespace Examples.Euler

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit Examples.Euler

def outwardSideTuple : Float × Float × Float × Float → Side :=
  fun (rho, momentum, transverse, energy) => outwardSide rho momentum transverse energy

set_option maxHeartbeats 4000000 in
theorem outwardSide_implements {a : Bool} : ImplementsPureA a euler.module 34 outwardSideTuple :=
  Func.implementsPureA euler.funcs 32 euler.outwardSide.ir "outwardSide" rfl outwardSideTuple
    (fun _ => rfl) fun ⟨rho, momentum, transverse, energy⟩ initial => by
      refine Stmt.seq_callPure speedUpper_implements rfl rfl rfl
        (x := (rho, momentum, transverse, energy)) ?_
      eval_ir [euler.outwardSide.ir, speedUpperTuple]
      iterate 12 (refine Stmt.seq_run ?_; eval_ir [])
      refine Stmt.run_triple ?_
      eval_ir [outwardSideTuple, outwardSide, positive, finite, absBits, rejectedSide, word_and,
        word_eq_one, F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul,
        F64Bits.toBits_div, half_toBits, twoFifths_toBits, zero_toBits]
      simp only [and_assoc]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · rw [ite_eq_left h]
        eval_ir [F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_div,
          half_toBits, twoFifths_toBits]
      · rw [ite_eq_right h]
        eval_ir [zero_toBits]

def outwardFluxTuple : Float × Float × Float × Float × Float × Float × Float × Float → Flux :=
  fun (rhoL, momentumL, transverseL, energyL, rhoR, momentumR, transverseR, energyR) =>
    outwardFlux rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR

set_option maxHeartbeats 4000000 in
theorem outwardFlux_implements {a : Bool} : ImplementsPureA a euler.module 35 outwardFluxTuple :=
  Func.implementsPureA euler.funcs 33 euler.outwardFlux.ir "outwardFlux" rfl outwardFluxTuple
    (fun _ => rfl)
    fun ⟨rhoL, momentumL, transverseL, energyL, rhoR, momentumR, transverseR, energyR⟩
      initial => by
      have hS := outwardSide_implements (a := a)
      have hC := component_implements (a := a)
      let left := outwardSide rhoL momentumL transverseL energyL
      let right := outwardSide rhoR momentumR transverseR energyR
      let alpha := if left.speed.toBits ≤ right.speed.toBits then right.speed else left.speed
      refine Stmt.seq_callPure hS rfl rfl rfl (x := (rhoL, momentumL, transverseL, energyL)) ?_
      eval_ir [euler.outwardFlux.ir, outwardSideTuple]
      refine Stmt.seq_callPure hS rfl rfl rfl (x := (rhoR, momentumR, transverseR, energyR)) ?_
      eval_ir [outwardSideTuple]
      refine Stmt.seq_run ?_
      eval_ir []
      refine Stmt.seq_callPure hC rfl rfl rfl
        (x := (alpha, left.massFlux, right.massFlux, rhoL, rhoR)) ?_
      eval_ir [componentTuple, alpha, left, right, toBits_ite]
      refine Stmt.seq_callPure hC rfl rfl rfl
        (x := (alpha, left.momentumFlux, right.momentumFlux, momentumL, momentumR)) ?_
      eval_ir [componentTuple, alpha, left, right, toBits_ite]
      refine Stmt.seq_callPure hC rfl rfl rfl
        (x := (alpha, left.transverseFlux, right.transverseFlux, transverseL, transverseR)) ?_
      eval_ir [componentTuple, alpha, left, right, toBits_ite]
      refine Stmt.seq_callPure hC rfl rfl rfl
        (x := (alpha, left.energyFlux, right.energyFlux, energyL, energyR)) ?_
      eval_ir [componentTuple, alpha, left, right, toBits_ite]
      refine Stmt.run_triple ?_
      eval_ir [outwardFluxTuple, outwardFlux, rejectedFlux, word_and, word_eq_one, zero_toBits,
        toBits_ite, componentTuple, alpha, left, right]
      simp only [and_assoc]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · rw [ite_eq_left h]
        eval_ir [toBits_ite]
      · rw [ite_eq_right h]
        eval_ir [zero_toBits]

def faceStepTuple : Float × Float × Float × Float × Float × Float × Float × Float × Float ×
    Float × Float × Float × Float × Float × Float × Float × Float × Float × Float × Float ×
    Float → Updated :=
  fun (ratio, rho, momentum, transverse, energy, a1, a2, a3, a4, b1, b2, b3, b4, c1, c2, c3, c4,
      d1, d2, d3, d4) =>
    faceStep ratio rho momentum transverse energy a1 a2 a3 a4 b1 b2 b3 b4 c1 c2 c3 c4 d1 d2 d3 d4

set_option maxHeartbeats 8000000 in
theorem faceStep_implements {a : Bool} : ImplementsPureA a euler.module 36 faceStepTuple :=
  Func.implementsPureA euler.funcs 34 euler.faceStep.ir "faceStep" rfl faceStepTuple
    (fun _ => rfl)
    fun ⟨ratio, rho, momentum, transverse, energy, a1, a2, a3, a4, b1, b2, b3, b4, c1, c2, c3, c4,
      d1, d2, d3, d4⟩ initial => by
      have hF := outwardFlux_implements (a := a)
      have hU := update_implements (a := a)
      have hS := outwardSide_implements (a := a)
      let left := outwardFlux a1 a2 a3 a4 b1 b2 b3 b4
      let right := outwardFlux c1 c2 c3 c4 d1 d2 d3 d4
      let alpha := if left.alpha.toBits ≤ right.alpha.toBits then right.alpha else left.alpha
      let courant := outMul true ratio alpha
      let nextDensity := update ratio rho left.mass right.mass
      let nextMomentum := update ratio momentum left.momentum right.momentum
      let nextTransverse := update ratio transverse left.transverse right.transverse
      let nextEnergy := update ratio energy left.energy right.energy
      refine Stmt.seq_callPure hF rfl rfl rfl (x := (a1, a2, a3, a4, b1, b2, b3, b4)) ?_
      eval_ir [euler.faceStep.ir, outwardFluxTuple]
      refine Stmt.seq_callPure hF rfl rfl rfl (x := (c1, c2, c3, c4, d1, d2, d3, d4)) ?_
      eval_ir [outwardFluxTuple]
      refine Stmt.seq_run ?_
      eval_ir []
      refine Stmt.seq_callPure outMul_implements rfl rfl rfl (x := (true, ratio, alpha)) ?_
      eval_ir [outMulTuple, alpha, left, right, toBits_ite]
      refine Stmt.seq_callPure hU rfl rfl rfl (x := (ratio, rho, left.mass, right.mass)) ?_
      eval_ir [updateTuple, left, right]
      refine Stmt.seq_callPure hU rfl rfl rfl
        (x := (ratio, momentum, left.momentum, right.momentum)) ?_
      eval_ir [updateTuple, left, right]
      refine Stmt.seq_callPure hU rfl rfl rfl
        (x := (ratio, transverse, left.transverse, right.transverse)) ?_
      eval_ir [updateTuple, left, right]
      refine Stmt.seq_callPure hU rfl rfl rfl (x := (ratio, energy, left.energy, right.energy)) ?_
      eval_ir [updateTuple, left, right]
      refine Stmt.seq_callPure hS rfl rfl rfl (x := (nextDensity.value, nextMomentum.value,
        nextTransverse.value, nextEnergy.value)) ?_
      eval_ir [outwardSideTuple, nextDensity, nextMomentum, nextTransverse, nextEnergy, left, right]
      refine Stmt.run_triple ?_
      eval_ir [faceStepTuple, faceStep, rejectedCell, positive, word_and, word_eq_one,
        zero_toBits, toBits_ite, outMulTuple, alpha, courant, left, right, nextDensity,
        nextMomentum, nextTransverse, nextEnergy]
      simp only [and_assoc]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · rw [ite_eq_left h]
        eval_ir [toBits_ite]
      · rw [ite_eq_right h]
        eval_ir [zero_toBits]

end Examples.Euler
