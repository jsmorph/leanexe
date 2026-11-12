import Library.Random.Lcg.Verified
import Verified.Master

namespace Library.Random.Lcg

open Function

theorem step_export :
    ({ name := "step", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem advance_export :
    ({ name := "advance", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem jump_export :
    ({ name := "jump", funcIdx := 6 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- One step of the generator on the natural number of the state. -/
theorem toNat_step (x : UInt64) :
    (step x).toNat = (6364136223846793005 * x.toNat + 1442695040888963407) % 2 ^ 64 := by
  simp only [step, affine, multiplier, increment, UInt64.toNat_add, UInt64.toNat_mul,
    UInt64.reduceToNat, Nat.mod_add_mod]

/-- `n` steps of the generator on the natural number of the state. -/
theorem toNat_iterate (n : Nat) (x : UInt64) :
    (step^[n] x).toNat =
      (fun s => (6364136223846793005 * s + 1442695040888963407) % 2 ^ 64)^[n] x.toNat :=
  Semiconj.iterate_right (f := UInt64.toNat)
    (gb := fun s => (6364136223846793005 * s + 1442695040888963407) % 2 ^ 64) toNat_step n x

/-- The export `step`, called on a state `x`, returns the state
`(6364136223846793005 x + 1442695040888963407) mod 2^64`. -/
theorem step_master :
    Verified.Master compiled.module compiled.tables "step" compiled.step.bound (fun _ => True)
      (fun (x : UInt64) (y : UInt64) =>
        y.toNat = (6364136223846793005 * x.toNat + 1442695040888963407) % 2 ^ 64) :=
  .of_trapFree (.ofA compiled.step.trapFree) nofun step_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => toNat_step x

#print axioms step_master

/-- The export `advance`, called on a count `n` and a state `x`, returns the state after `n` steps
`s ↦ (6364136223846793005 s + 1442695040888963407) mod 2^64` from `x`. -/
theorem advance_master :
    Verified.Master compiled.module compiled.tables "advance" compiled.advance.bound
      (fun _ => True)
      (fun (x : UInt64 × UInt64) (y : UInt64) => y.toNat =
        (fun s => (6364136223846793005 * s + 1442695040888963407) % 2 ^ 64)^[x.1.toNat]
          x.2.toNat) :=
  .of_trapFree (.ofA compiled.advance.trapFree) nofun advance_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => by
      rw [advance_eq_iterate]
      exact toNat_iterate _ _

#print axioms advance_master

/-- The export `jump`, called on a count `n` and a state `x`, returns the state after `n` steps
`s ↦ (6364136223846793005 s + 1442695040888963407) mod 2^64` from `x`. -/
theorem jump_master :
    Verified.Master compiled.module compiled.tables "jump" compiled.jump.bound (fun _ => True)
      (fun (x : UInt64 × UInt64) (y : UInt64) => y.toNat =
        (fun s => (6364136223846793005 * s + 1442695040888963407) % 2 ^ 64)^[x.1.toNat]
          x.2.toNat) :=
  .of_trapFree (.ofA compiled.jump.trapFree) nofun jump_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => by
      rw [jump_eq, advance_eq_iterate]
      exact toNat_iterate _ _

#print axioms jump_master

end Library.Random.Lcg
