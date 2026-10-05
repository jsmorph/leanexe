import Project.Euler.Module
import Project.IR.Correct
import Project.IR.Run
import Project.ProofKit.F64Bits

/-! The compiled scalar functions of the first-order Euler solver compute their Lean
definitions.  A record is represented as the tuple of its fields, and a `Bool` word is 1 exactly
when the Lean value is `true`. -/

namespace Project.Euler

open Wasm Project.Pipeline Project.IR Project.ProofKit LeanExe.Examples.Euler

instance : Flat Conserved (Float × Float × Float × Float) :=
  ⟨fun q => (q.density, q.mx, q.my, q.energy)⟩
instance : Flat Cell (Conserved × Float × UInt64) := ⟨fun c => (c.state, c.pressure, c.status)⟩
instance : Flat Side (UInt64 × Float × Float × Float × Float × Float × Float × Float) :=
  ⟨fun s => (s.status, s.velocity, s.pressure, s.speed, s.massFlux, s.momentumFlux,
    s.transverseFlux, s.energyFlux)⟩
instance : Flat Component (UInt64 × Float) := ⟨fun c => (c.status, c.value)⟩
instance : Flat Flux (UInt64 × Float × Float × Float × Float × Float) :=
  ⟨fun f => (f.status, f.mass, f.momentum, f.transverse, f.energy, f.alpha)⟩
instance : Flat Updated (UInt64 × Float × Float × Float × Float × Float × Float × Float) :=
  ⟨fun u => (u.status, u.density, u.momentum, u.transverse, u.energy, u.pressure, u.alpha,
    u.courant)⟩

/-! Words of Bool tests: the compiler computes `a && b` as the bitwise and of two words that
are 0 or 1, and tests the result against 1. -/

theorem word_and (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : UInt64) &&& if q then 1 else 0) = if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem word_or (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : UInt64) ||| if q then 1 else 0) = if p ∨ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem word_eq_one (p : Prop) [Decidable p] : ((if p then 1 else 0 : UInt64) = 1) ↔ p := by
  by_cases hp : p <;> simp [hp]

/-- A run that ends in one of two states by a test: each state, under its outcome. -/
theorem exists_ite_some {c : Prop} [Decidable c] {a b : State} {P : State → Prop}
    (ha : c → P a) (hb : ¬c → P b) :
    ∃ final, (if c then some a else some b) = some final ∧ P final := by
  by_cases h : c
  · exact ⟨a, by simp [h], ha h⟩
  · exact ⟨b, by simp [h], hb h⟩

theorem toBits_ite (c : Prop) [Decidable c] (a b : Float) :
    (if c then a else b).toBits = if c then a.toBits else b.toBits := by
  split <;> rfl

/-- The IR's division and remainder test the divisor for 0, where Lean's give 0 and the
dividend. -/
theorem divU_eq (a b : UInt64) : (if b = 0 then 0 else a / b) = a / b := by
  split <;> simp_all

theorem remU_eq (a b : UInt64) : (if b = 0 then a else a % b) = a % b := by
  split <;> simp_all

theorem min_word (a b : UInt64) : min a b = if a ≤ b then a else b := rfl

theorem zero_toBits : (0 : Float).toBits = 0 := by decide +kernel
theorem half_toBits : (0.5 : Float).toBits = 0x3FE0000000000000 := by decide +kernel
theorem twoFifths_toBits : (0.4 : Float).toBits = 0x3FD999999999999A := by decide +kernel
theorem sevenFifths_toBits : (1.4 : Float).toBits = 0x3FF6666666666666 := by decide +kernel
theorem one_toBits : (1 : Float).toBits = 0x3FF0000000000000 := by decide +kernel
theorem endTime_toBits : (0.8 : Float).toBits = 0x3FE999999999999A := by decide +kernel
theorem fifth_toBits : (0.2 : Float).toBits = 4596373779694328218 := by decide +kernel
theorem threeFifths_toBits : (0.6 : Float).toBits = 4603579539098121011 := by decide +kernel
theorem p029_toBits : (0.029 : Float).toBits = 4584015902316823577 := by decide +kernel
theorem p138_toBits : (0.138 : Float).toBits = 4594139994279152452 := by decide +kernel
theorem p1206_toBits : (1.206 : Float).toBits = 4608110160323255730 := by decide +kernel
theorem p3_toBits : (0.3 : Float).toBits = 4599075939470750515 := by decide +kernel
theorem p5323_toBits : (0.5323 : Float).toBits = 4602969751708575046 := by decide +kernel
theorem p15_toBits : (1.5 : Float).toBits = 4609434218613702656 := by decide +kernel

/-- Evaluates a compiled body of assignments and conditionals and its results, with the given
lemmas, then splits on the tests, which both sides now state as the same propositions on bits,
and closes each case with the bit lemmas of the float operations. -/
macro "evaluate_pure" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (refine Stmt.run_triple ?_
             simp [Stmt.run, Expr.eval, Func.state, Func.locals, Func.scratch, Func.width,
               Stmt.scratchWidth, Expr.scratchWidth, State.set?_eq_update, State.get,
               State.update, U64Op.apply, F64Op.apply, Scalar.values, ScalarType.valueType,
               Expr.evalResults, ScalarType.value, Flat.flat, word_and, word_or, word_eq_one,
               F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_div,
               F64Bits.toBits_sqrt, F64Bits.toBits_abs, zero_toBits, half_toBits,
               twoFifths_toBits, sevenFifths_toBits, one_toBits, endTime_toBits, $args,*]
             simp only [and_assoc]
             split_ifs <;> simp [F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul,
               F64Bits.toBits_div, F64Bits.toBits_sqrt, F64Bits.toBits_abs, zero_toBits,
               half_toBits, twoFifths_toBits, sevenFifths_toBits, one_toBits, endTime_toBits]))

def updateTuple : Float × Float × Float × Float → Component :=
  fun (ratio, state, fluxL, fluxR) => update ratio state fluxL fluxR

theorem update_implements : ImplementsPure euler.module 7 updateTuple :=
  Func.implementsPure euler.funcs 5 euler.update.ir "update" rfl updateTuple
    (fun _ => rfl) fun ⟨ratio, state, fluxL, fluxR⟩ initial => by
      evaluate_pure [euler.update.ir, updateTuple, update, positive, finite, absBits,
        rejectedComponent]

def componentTuple : Float × Float × Float × Float × Float → Component :=
  fun (alpha, fluxL, fluxR, stateL, stateR) => component alpha fluxL fluxR stateL stateR

set_option maxHeartbeats 2000000 in
theorem component_implements : ImplementsPure euler.module 5 componentTuple :=
  Func.implementsPure euler.funcs 3 euler.component.ir "component" rfl componentTuple
    (fun _ => rfl) fun ⟨alpha, fluxL, fluxR, stateL, stateR⟩ initial => by
      evaluate_pure [euler.component.ir, componentTuple, component, positive, finite, absBits,
        rejectedComponent]

/-- A word whose exponent field is not all ones is not a NaN pattern. -/
theorem not_nan_of_exponent {w : UInt64} (h : ¬(w >>> 52) &&& 0x7FF = 0x7FF) :
    Wasm.IEEE64.isNaN w = false := by
  have hExp : Wasm.IEEE64.exponent w ≠ 0x7FF := by
    intro he
    apply h
    apply UInt64.toNat_inj.mp
    have hAnd : ((w >>> 52) &&& 0x7FF).toNat = w.toNat / 2 ^ 52 % 2 ^ 11 := by
      rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
      exact Nat.and_two_pow_sub_one_eq_mod _ 11
    rw [hAnd]
    simpa [Wasm.IEEE64.exponent] using he
  simp [Wasm.IEEE64.isNaN, hExp]

def normalizedTuple : Float × UInt64 → Float := fun (x, top) => normalized x top

set_option maxHeartbeats 2000000 in
theorem normalized_implements : ImplementsPure euler.module 2 normalizedTuple :=
  Func.implementsPure euler.funcs 0 euler.normalized.ir "normalized" rfl normalizedTuple
    (fun _ => rfl) fun ⟨x, top⟩ initial => by
      refine Stmt.run_triple ?_
      simp [Stmt.run, Expr.eval, Func.state, Func.locals, Func.scratch, Func.width,
        Stmt.scratchWidth, Expr.scratchWidth, State.set?_eq_update, State.get,
        State.update, U64Op.apply, F64Op.apply, Scalar.values, ScalarType.valueType,
        Expr.evalResults, ScalarType.value, euler.normalized.ir, normalizedTuple, normalized,
        absBits, exponentBits, zero_toBits, word_or, word_eq_one, or_iff_not_imp_left]
      split_ifs with h
      · simp [zero_toBits]
      · rw [F64Bits.toBits_ofBits, not_nan_of_exponent fun hb => h fun _ => hb]
        rfl

def energyGuardTuple : Float × Float × Float × Float → Bool :=
  fun (rho, mx, my, energy) => energyGuard rho mx my energy

/-- The lemmas that evaluate expressions and statements of a compiled body. -/
macro "eval_ir" "[" args:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [Stmt.run, Expr.eval, Func.state, Func.locals, Func.scratch, Func.width,
    Stmt.scratchWidth, Expr.scratchWidth, State.set?_eq_update, State.get, State.update,
    State.setAll, U64Op.apply, F64Op.apply, F64UnOp.apply, Scalar.values, ScalarType.valueType,
    Expr.evalResults, ScalarType.value, Flat.flat, divU_eq, remU_eq, -mul_ite, -ite_mul, -add_ite, -ite_add,
    -sub_ite, -ite_sub, -div_ite, -ite_div, $args,*])

set_option maxHeartbeats 4000000 in
theorem energyGuard_implements : ImplementsPure euler.module 3 energyGuardTuple :=
  Func.implementsPure euler.funcs 1 euler.energyGuard.ir "energyGuard" rfl energyGuardTuple
    (fun _ => rfl) fun ⟨rho, mx, my, energy⟩ initial => by
      have hN := normalized_implements
      refine Stmt.seq_run ?_
      eval_ir [euler.energyGuard.ir]
      refine Stmt.seq_callPure hN rfl rfl rfl (x := (rho, topExponent rho mx my energy)) ?_
      eval_ir [normalizedTuple]
      refine Stmt.seq_callPure hN rfl rfl rfl (x := (energy, topExponent rho mx my energy)) ?_
      eval_ir [normalizedTuple]
      refine Stmt.seq_callPure hN rfl rfl rfl (x := (mx, topExponent rho mx my energy)) ?_
      eval_ir [normalizedTuple]
      refine Stmt.seq_callPure hN rfl rfl rfl (x := (mx, topExponent rho mx my energy)) ?_
      eval_ir [normalizedTuple]
      refine Stmt.seq_callPure hN rfl rfl rfl (x := (my, topExponent rho mx my energy)) ?_
      eval_ir [normalizedTuple]
      refine Stmt.seq_callPure hN rfl rfl rfl (x := (my, topExponent rho mx my energy)) ?_
      eval_ir [normalizedTuple]
      refine Stmt.run_triple ?_
      eval_ir [energyGuardTuple, energyGuard, positive, finite, absBits, normalizable,
        exponentBits, topExponent, maxWord, energyResidual, word_and, word_or, word_eq_one,
        F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul, half_toBits, cond_eq_ite,
        or_iff_not_imp_left]

def sideTuple : Float × Float × Float × Float → Side :=
  fun (rho, momentum, transverse, energy) => side rho momentum transverse energy

set_option maxHeartbeats 8000000 in
theorem side_implements : ImplementsPure euler.module 4 sideTuple :=
  Func.implementsPure euler.funcs 2 euler.side.ir "side" rfl sideTuple
    (fun _ => rfl) fun ⟨rho, momentum, transverse, energy⟩ initial => by
      have hG := energyGuard_implements
      refine Stmt.seq_run ?_
      eval_ir [euler.side.ir]
      iterate 15 (refine Stmt.seq_run ?_; eval_ir [])
      refine Stmt.seq_callPure hG rfl rfl rfl (x := (rho, momentum, transverse, energy)) ?_
      eval_ir [energyGuardTuple]
      refine Stmt.run_triple ?_
      eval_ir [sideTuple, side, stateGuard, narrowGuard, positive, finite, absBits, rejectedSide,
        word_and, word_or, word_eq_one, F64Bits.toBits_add, F64Bits.toBits_sub,
        F64Bits.toBits_mul, F64Bits.toBits_div, F64Bits.toBits_sqrt, F64Bits.toBits_abs,
        half_toBits, twoFifths_toBits, sevenFifths_toBits, zero_toBits, cond_eq_ite]
      simp only [and_assoc]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · rw [if_pos h]
        eval_ir [F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_div,
          F64Bits.toBits_sqrt, F64Bits.toBits_abs, half_toBits, twoFifths_toBits,
          sevenFifths_toBits]
      · rw [if_neg h]
        eval_ir [zero_toBits]

def fluxTuple : Float × Float × Float × Float × Float × Float × Float × Float → Flux :=
  fun (rhoL, momentumL, transverseL, energyL, rhoR, momentumR, transverseR, energyR) =>
    flux rhoL momentumL transverseL energyL rhoR momentumR transverseR energyR

set_option maxHeartbeats 8000000 in
theorem flux_implements : ImplementsPure euler.module 6 fluxTuple :=
  Func.implementsPure euler.funcs 4 euler.flux.ir "flux" rfl fluxTuple (fun _ => rfl)
    fun ⟨rhoL, momentumL, transverseL, energyL, rhoR, momentumR, transverseR, energyR⟩
      initial => by
      have hS := side_implements
      have hC := component_implements
      let left := side rhoL momentumL transverseL energyL
      let right := side rhoR momentumR transverseR energyR
      let alpha := if left.speed.toBits ≤ right.speed.toBits then right.speed else left.speed
      refine Stmt.seq_callPure hS rfl rfl rfl (x := (rhoL, momentumL, transverseL, energyL)) ?_
      eval_ir [euler.flux.ir, sideTuple]
      refine Stmt.seq_callPure hS rfl rfl rfl (x := (rhoR, momentumR, transverseR, energyR)) ?_
      eval_ir [sideTuple]
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
      eval_ir [fluxTuple, flux, rejectedFlux, word_and, word_eq_one, zero_toBits, toBits_ite,
        componentTuple, alpha, left, right]
      simp only [and_assoc]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · rw [if_pos h]
        eval_ir [toBits_ite]
      · rw [if_neg h]
        eval_ir [zero_toBits]

def advanceCellTuple : Float × Float × Float × Float × Float × Float × Float × Float × Float ×
    Float × Float × Float × Float → Updated :=
  fun (ratio, rhoL, momentumL, transverseL, energyL, rho, momentum, transverse, energy, rhoR,
      momentumR, transverseR, energyR) =>
    advanceCell ratio rhoL momentumL transverseL energyL rho momentum transverse energy rhoR
      momentumR transverseR energyR

set_option maxHeartbeats 8000000 in
theorem advanceCell_implements : ImplementsPure euler.module 8 advanceCellTuple :=
  Func.implementsPure euler.funcs 6 euler.advanceCell.ir "advanceCell" rfl advanceCellTuple
    (fun _ => rfl)
    fun ⟨ratio, rhoL, momentumL, transverseL, energyL, rho, momentum, transverse, energy, rhoR,
      momentumR, transverseR, energyR⟩ initial => by
      have hF := flux_implements
      have hU := update_implements
      have hS := side_implements
      let left := flux rhoL momentumL transverseL energyL rho momentum transverse energy
      let right := flux rho momentum transverse energy rhoR momentumR transverseR energyR
      let alpha := if left.alpha.toBits ≤ right.alpha.toBits then right.alpha else left.alpha
      let nextDensity := update ratio rho left.mass right.mass
      let nextMomentum := update ratio momentum left.momentum right.momentum
      let nextTransverse := update ratio transverse left.transverse right.transverse
      let nextEnergy := update ratio energy left.energy right.energy
      refine Stmt.seq_callPure hF rfl rfl rfl
        (x := (rhoL, momentumL, transverseL, energyL, rho, momentum, transverse, energy)) ?_
      eval_ir [euler.advanceCell.ir, fluxTuple]
      refine Stmt.seq_callPure hF rfl rfl rfl
        (x := (rho, momentum, transverse, energy, rhoR, momentumR, transverseR, energyR)) ?_
      eval_ir [fluxTuple]
      refine Stmt.seq_run ?_
      eval_ir []
      refine Stmt.seq_run ?_
      eval_ir []
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
      eval_ir [sideTuple, nextDensity, nextMomentum, nextTransverse, nextEnergy, left, right]
      refine Stmt.run_triple ?_
      eval_ir [advanceCellTuple, advanceCell, rejectedCell, positive, word_and, word_eq_one,
        zero_toBits, toBits_ite, F64Bits.toBits_mul, alpha, left, right, nextDensity,
        nextMomentum, nextTransverse, nextEnergy]
      simp only [and_assoc]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · rw [if_pos h]
        eval_ir [toBits_ite, F64Bits.toBits_mul]
      · rw [if_neg h]
        eval_ir [zero_toBits]

def initialCellTuple : UInt64 × UInt64 → Cell := fun (n, index) => initialCell n index

set_option maxHeartbeats 8000000 in
theorem initialCell_implements : ImplementsPure euler.module 9 initialCellTuple :=
  Func.implementsPure euler.funcs 7 euler.initialCell.ir "initialCell" rfl initialCellTuple
    (fun _ => rfl) fun ⟨n, index⟩ initial => by
      have hS := side_implements
      let x := fifths (lowerFifths n (index % n))
      let y := fifths (lowerFifths n (index / n))
      let q : Conserved :=
        ⟨weightedComponent x y bottomLeft.density bottomRight.density topLeft.density
            topRight.density,
          weightedComponent x y bottomLeft.mx bottomRight.mx topLeft.mx topRight.mx,
          weightedComponent x y bottomLeft.my bottomRight.my topLeft.my topRight.my,
          weightedComponent x y bottomLeft.energy bottomRight.energy topLeft.energy
            topRight.energy⟩
      refine Stmt.seq_run ?_
      eval_ir [euler.initialCell.ir]
      iterate 15 (refine Stmt.seq_run ?_; eval_ir [])
      refine Stmt.callPure_last hS rfl rfl rfl (x := (q.density, q.mx, q.my, q.energy)) ?_
      eval_ir [sideTuple, q, x, y, initialCellTuple, initialCell, weightedComponent, fifths,
        lowerFifths, bottomLeft, bottomRight, topLeft, topRight, conservative, toBits_ite,
        F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_div,
        zero_toBits, half_toBits, twoFifths_toBits, one_toBits, endTime_toBits, fifth_toBits,
        threeFifths_toBits, p029_toBits, p138_toBits, p1206_toBits, p3_toBits, p5323_toBits,
        p15_toBits, min_word]

end Project.Euler
