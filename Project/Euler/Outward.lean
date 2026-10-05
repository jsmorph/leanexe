import Project.Euler.Kernels

/-! The compiled outward-rounding kernels of the reconstructed Euler solver compute their Lean
definitions. -/

namespace Project.Euler

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit LeanExe.Examples.Euler

instance : Flat Checked (UInt64 × Float) := ⟨fun c => (c.status, c.value)⟩

/-- The magnitude bits of a Lean float are the bits of a Lean float: a NaN's are the canonical
NaN's. -/
theorem toBits_ofBits_abs (x : Float) :
    (Float.ofBits (x.toBits &&& 0x7FFFFFFFFFFFFFFF)).toBits = x.toBits &&& 0x7FFFFFFFFFFFFFFF := by
  rw [F64Bits.toBits_ofBits]
  split
  · rename_i hN
    have hA : (x.toBits &&& 0x7FFFFFFFFFFFFFFF).toNat = x.toBits.toNat % 2 ^ 63 := by
      rw [UInt64.toNat_and]
      exact Nat.and_two_pow_sub_one_eq_mod _ 63
    have hw : Wasm.IEEE64.isNaN x.toBits = true := by
      simp only [Wasm.IEEE64.isNaN, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, hA, Bool.and_eq_true,
        beq_iff_eq, bne_iff_ne, ne_eq] at hN ⊢
      omega
    have h := F64Bits.toBits_canonical x
    rw [hw, ite_eq_left rfl] at h
    rw [← h]
    decide
  · rfl

def endpointTuple : Bool × Float → Checked := fun (up, rounded) => endpoint up rounded

set_option maxHeartbeats 2000000 in
theorem endpoint_implements : ImplementsPure euler.module 24 endpointTuple :=
  Func.implementsPure euler.funcs 22 euler.endpoint.ir "endpoint" rfl endpointTuple
    (fun _ => rfl) fun ⟨up, rounded⟩ initial => by
      refine Stmt.run_triple ?_
      eval_ir [euler.endpoint.ir, endpointTuple, endpoint, word_and, word_eq_one, finite, absBits,
        nextUpBits, nextDownBits, rejectedChecked]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · eval_ir [h.1, h.2, toBits_ofBits_of_finite h.2]
      · eval_ir [h, zero_toBits, and_assoc]

def outAddTuple : Bool × Float × Float → Checked := fun (up, a, b) => outAdd up a b

set_option maxHeartbeats 2000000 in
theorem outAdd_implements : ImplementsPure euler.module 25 outAddTuple :=
  Func.implementsPure euler.funcs 23 euler.outAdd.ir "outAdd" rfl outAddTuple
    (fun _ => rfl) fun ⟨up, a, b⟩ initial => by
      refine Stmt.seq_callPure endpoint_implements rfl rfl rfl (x := (up, a + b)) ?_
      eval_ir [euler.outAdd.ir, endpointTuple, F64Bits.toBits_add]
      refine Stmt.run_triple ?_
      eval_ir [outAddTuple, outAdd, word_and, word_eq_one, finite, absBits, rejectedChecked]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · eval_ir [h]
      · eval_ir [h, zero_toBits, and_assoc]

def outSubTuple : Bool × Float × Float → Checked := fun (up, a, b) => outSub up a b

set_option maxHeartbeats 2000000 in
theorem outSub_implements : ImplementsPure euler.module 26 outSubTuple :=
  Func.implementsPure euler.funcs 24 euler.outSub.ir "outSub" rfl outSubTuple
    (fun _ => rfl) fun ⟨up, a, b⟩ initial => by
      refine Stmt.seq_callPure endpoint_implements rfl rfl rfl (x := (up, a - b)) ?_
      eval_ir [euler.outSub.ir, endpointTuple, F64Bits.toBits_sub]
      refine Stmt.run_triple ?_
      eval_ir [outSubTuple, outSub, word_and, word_eq_one, finite, absBits, rejectedChecked]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · eval_ir [h]
      · eval_ir [h, zero_toBits, and_assoc]

def outMulTuple : Bool × Float × Float → Checked := fun (up, a, b) => outMul up a b

set_option maxHeartbeats 2000000 in
theorem outMul_implements : ImplementsPure euler.module 27 outMulTuple :=
  Func.implementsPure euler.funcs 25 euler.outMul.ir "outMul" rfl outMulTuple
    (fun _ => rfl) fun ⟨up, a, b⟩ initial => by
      refine Stmt.seq_callPure endpoint_implements rfl rfl rfl (x := (up, a * b)) ?_
      eval_ir [euler.outMul.ir, endpointTuple, F64Bits.toBits_mul]
      refine Stmt.run_triple ?_
      eval_ir [outMulTuple, outMul, word_and, word_eq_one, finite, absBits, rejectedChecked]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · eval_ir [h]
      · eval_ir [h, zero_toBits, and_assoc]

def outDivTuple : Bool × Float × Float → Checked := fun (up, a, b) => outDiv up a b

set_option maxHeartbeats 2000000 in
theorem outDiv_implements : ImplementsPure euler.module 28 outDivTuple :=
  Func.implementsPure euler.funcs 26 euler.outDiv.ir "outDiv" rfl outDivTuple
    (fun _ => rfl) fun ⟨up, a, b⟩ initial => by
      refine Stmt.seq_callPure endpoint_implements rfl rfl rfl (x := (up, a / b)) ?_
      eval_ir [euler.outDiv.ir, endpointTuple, F64Bits.toBits_div]
      refine Stmt.run_triple ?_
      eval_ir [outDivTuple, outDiv, word_and, word_eq_one, finite, absBits, rejectedChecked]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · eval_ir [h]
      · eval_ir [h, zero_toBits, and_assoc]

def outSqrtTuple : Bool × Float → Checked := fun (up, a) => outSqrt up a

set_option maxHeartbeats 2000000 in
theorem outSqrt_implements : ImplementsPure euler.module 29 outSqrtTuple :=
  Func.implementsPure euler.funcs 27 euler.outSqrt.ir "outSqrt" rfl outSqrtTuple
    (fun _ => rfl) fun ⟨up, a⟩ initial => by
      refine Stmt.seq_callPure endpoint_implements rfl rfl rfl (x := (up, a.sqrt)) ?_
      eval_ir [euler.outSqrt.ir, endpointTuple, F64Bits.toBits_sqrt]
      refine Stmt.run_triple ?_
      eval_ir [outSqrtTuple, outSqrt, word_and, word_eq_one, finite, absBits, rejectedChecked]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · eval_ir [h]
      · eval_ir [h, zero_toBits, and_assoc]

theorem gammaUp_toBits : (1.4000000000000001 : Float).toBits = 0x3FF6666666666667 := by
  decide +kernel

def kineticLowerTuple : Float × Float × Float → Checked :=
  fun (rho, mx, my) => kineticLower rho mx my

set_option maxHeartbeats 4000000 in
theorem kineticLower_implements : ImplementsPure euler.module 30 kineticLowerTuple :=
  Func.implementsPure euler.funcs 28 euler.kineticLower.ir "kineticLower" rfl kineticLowerTuple
    (fun _ => rfl) fun ⟨rho, mx, my⟩ initial => by
      let xx := outMul false mx mx
      let yy := outMul false my my
      let sum := outAdd false xx.value yy.value
      let half := outMul false 0.5 sum.value
      refine Stmt.seq_callPure outMul_implements rfl rfl rfl (x := (false, mx, mx)) ?_
      eval_ir [euler.kineticLower.ir, outMulTuple]
      refine Stmt.seq_callPure outMul_implements rfl rfl rfl (x := (false, my, my)) ?_
      eval_ir [outMulTuple]
      refine Stmt.seq_callPure outAdd_implements rfl rfl rfl (x := (false, xx.value, yy.value)) ?_
      eval_ir [outAddTuple, xx, yy]
      refine Stmt.seq_callPure outMul_implements rfl rfl rfl (x := (false, 0.5, sum.value)) ?_
      eval_ir [outMulTuple, sum, xx, yy, half_toBits]
      refine Stmt.seq_callPure outDiv_implements rfl rfl rfl (x := (false, half.value, rho)) ?_
      eval_ir [outDivTuple, half, sum, xx, yy]
      refine Stmt.run_triple ?_
      eval_ir [kineticLowerTuple, kineticLower, word_and, word_eq_one, rejectedChecked]
      simp only [and_assoc]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · eval_ir [h]
      · eval_ir [h, zero_toBits, and_assoc]

def pressureUpperTuple : Float × Float × Float × Float → Checked :=
  fun (rho, mx, my, energy) => pressureUpper rho mx my energy

set_option maxHeartbeats 4000000 in
theorem pressureUpper_implements : ImplementsPure euler.module 31 pressureUpperTuple :=
  Func.implementsPure euler.funcs 29 euler.pressureUpper.ir "pressureUpper" rfl
    pressureUpperTuple (fun _ => rfl) fun ⟨rho, mx, my, energy⟩ initial => by
      let kinetic := kineticLower rho mx my
      let internal := outSub true energy kinetic.value
      refine Stmt.seq_callPure kineticLower_implements rfl rfl rfl (x := (rho, mx, my)) ?_
      eval_ir [euler.pressureUpper.ir, kineticLowerTuple]
      refine Stmt.seq_callPure outSub_implements rfl rfl rfl
        (x := (true, energy, kinetic.value)) ?_
      eval_ir [outSubTuple, kinetic]
      refine Stmt.seq_callPure outMul_implements rfl rfl rfl (x := (true, 0.4, internal.value)) ?_
      eval_ir [outMulTuple, internal, kinetic, twoFifths_toBits]
      refine Stmt.run_triple ?_
      eval_ir [pressureUpperTuple, pressureUpper, word_and, word_eq_one, rejectedChecked]
      simp only [and_assoc]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · eval_ir [h]
      · eval_ir [h, zero_toBits, and_assoc]

def soundUpperTuple : Float × Float × Float × Float → Checked :=
  fun (rho, mx, my, energy) => soundUpper rho mx my energy

set_option maxHeartbeats 4000000 in
theorem soundUpper_implements : ImplementsPure euler.module 32 soundUpperTuple :=
  Func.implementsPure euler.funcs 30 euler.soundUpper.ir "soundUpper" rfl soundUpperTuple
    (fun _ => rfl) fun ⟨rho, mx, my, energy⟩ initial => by
      let pressure := pressureUpper rho mx my energy
      let ratio := outDiv true pressure.value rho
      let radicand := outMul true 1.4000000000000001 ratio.value
      refine Stmt.seq_callPure pressureUpper_implements rfl rfl rfl (x := (rho, mx, my, energy)) ?_
      eval_ir [euler.soundUpper.ir, pressureUpperTuple]
      refine Stmt.seq_callPure outDiv_implements rfl rfl rfl (x := (true, pressure.value, rho)) ?_
      eval_ir [outDivTuple, pressure]
      refine Stmt.seq_callPure outMul_implements rfl rfl rfl
        (x := (true, 1.4000000000000001, ratio.value)) ?_
      eval_ir [outMulTuple, ratio, pressure, gammaUp_toBits]
      refine Stmt.seq_callPure outSqrt_implements rfl rfl rfl (x := (true, radicand.value)) ?_
      eval_ir [outSqrtTuple, radicand, ratio, pressure]
      refine Stmt.run_triple ?_
      eval_ir [soundUpperTuple, soundUpper, word_and, word_eq_one, rejectedChecked]
      simp only [and_assoc]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · eval_ir [h]
      · eval_ir [h, zero_toBits, and_assoc]

def speedUpperTuple : Float × Float × Float × Float → Checked :=
  fun (rho, mx, my, energy) => speedUpper rho mx my energy

set_option maxHeartbeats 4000000 in
theorem speedUpper_implements : ImplementsPure euler.module 33 speedUpperTuple :=
  Func.implementsPure euler.funcs 31 euler.speedUpper.ir "speedUpper" rfl speedUpperTuple
    (fun _ => rfl) fun ⟨rho, mx, my, energy⟩ initial => by
      let velocity := outDiv true (Float.ofBits (absBits mx.toBits)) rho
      let sound := soundUpper rho mx my energy
      refine Stmt.seq_callPure outDiv_implements rfl rfl rfl
        (x := (true, Float.ofBits (absBits mx.toBits), rho)) ?_
      eval_ir [euler.speedUpper.ir, outDivTuple, toBits_ofBits_abs]
      refine Stmt.seq_callPure soundUpper_implements rfl rfl rfl (x := (rho, mx, my, energy)) ?_
      eval_ir [soundUpperTuple]
      refine Stmt.seq_callPure outAdd_implements rfl rfl rfl
        (x := (true, velocity.value, sound.value)) ?_
      eval_ir [outAddTuple, velocity, sound]
      refine Stmt.seq_callPure energyGuard_implements rfl rfl rfl (x := (rho, mx, my, energy)) ?_
      eval_ir [energyGuardTuple]
      refine Stmt.run_triple ?_
      eval_ir [speedUpperTuple, speedUpper, stateGuard, narrowGuard, positive, finite, absBits,
        rejectedChecked, word_and, word_or, word_eq_one, cond_eq_ite]
      simp only [and_assoc]
      refine exists_ite_some (fun h => ?_) (fun h => ?_)
      · eval_ir [h]
      · eval_ir [h, zero_toBits, and_assoc]

end Project.Euler
