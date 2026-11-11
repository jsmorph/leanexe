import Library.Random.Xorshift.Verified
import Verified.Master

namespace Library.Random.Xorshift

open Function

/-- Marsaglia's xorshift step with the shifts 13, 7, and 17 on a 64-bit word, `x ^= x << 13;
x ^= x >> 7; x ^= x << 17`, the generator `xor64` of G. Marsaglia, "Xorshift RNGs", *Journal of
Statistical Software* 8(14), 2003. -/
def xor64 (v : BitVec 64) : BitVec 64 :=
  let v := v ^^^ (v <<< 13)
  let v := v ^^^ (v >>> 7)
  v ^^^ (v <<< 17)

theorem step_export :
    ({ name := "step", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem advance_export :
    ({ name := "advance", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem jump_export :
    ({ name := "jump", funcIdx := 7 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem toBitVec_iterate (n : Nat) (x : UInt64) :
    (step^[n] x).toBitVec = xor64^[n] x.toBitVec :=
  Semiconj.iterate_right (f := UInt64.toBitVec) (gb := xor64) toBitVec_step n x

/-- The export `step`, called on a state `x`, returns the state `xor64 x` of Marsaglia's
generator. -/
theorem step_master :
    Verified.Master compiled.module compiled.tables "step" compiled.step.bound (fun _ => True)
      (fun (x : UInt64) (y : UInt64) => y.toBitVec = xor64 x.toBitVec) :=
  .of_trapFree (.ofA compiled.step.trapFree) nofun step_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => toBitVec_step x

#print axioms step_master

/-- The export `advance`, called on a count `n` and a state `x`, returns the state after `n` steps
of `xor64` from `x`. -/
theorem advance_master :
    Verified.Master compiled.module compiled.tables "advance" compiled.advance.bound
      (fun _ => True)
      (fun (x : UInt64 × UInt64) (y : UInt64) =>
        y.toBitVec = xor64^[x.1.toNat] x.2.toBitVec) :=
  .of_trapFree (.ofA compiled.advance.trapFree) nofun advance_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => by
      rw [advance_eq_iterate]
      exact toBitVec_iterate _ _

#print axioms advance_master

/-- The export `jump`, called on a count `n` and a state `x`, returns the state after `n` steps of
`xor64` from `x`. -/
theorem jump_master :
    Verified.Master compiled.module compiled.tables "jump" compiled.jump.bound (fun _ => True)
      (fun (x : UInt64 × UInt64) (y : UInt64) =>
        y.toBitVec = xor64^[x.1.toNat] x.2.toBitVec) :=
  .of_trapFree (.ofA compiled.jump.trapFree) nofun jump_export (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => by
      rw [jump_eq, advance_eq_iterate]
      exact toBitVec_iterate _ _

#print axioms jump_master

end Library.Random.Xorshift
