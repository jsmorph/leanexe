import Library.Random.ParkMiller.Verified
import Verified.Master

namespace Library.Random.ParkMiller

theorem step_export :
    ({ name := "step", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem advance_export :
    ({ name := "advance", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem seed_export :
    ({ name := "seed", funcIdx := 4 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The export `step`, called on a state `x < 2^31 - 1`, returns the state
`16807 x mod (2^31 - 1)`. -/
theorem step_master :
    Verified.Master compiled.module compiled.tables "step" compiled.step.bound
      (fun x : UInt64 => x.toNat < 2147483647)
      (fun x (y : UInt64) => y.toNat = 16807 * x.toNat % 2147483647) :=
  .of_trapFree (.ofA compiled.step.trapFree) nofun step_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ _ _ hx => toNat_step hx

#print axioms step_master

/-- The export `advance`, called on a count `n` and a state `x < 2^31 - 1`, returns the state
`16807^n x mod (2^31 - 1)` after `n` steps. -/
theorem advance_master :
    Verified.Master compiled.module compiled.tables "advance" compiled.advance.bound
      (fun x : UInt64 × UInt64 => x.2.toNat < 2147483647)
      (fun x (y : UInt64) => y.toNat = 16807 ^ x.1.toNat * x.2.toNat % 2147483647) :=
  .of_trapFree (.ofA compiled.advance.trapFree) nofun advance_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ x _ hx => by
      rw [advance_eq_iterate]
      exact toNat_iterate hx _

#print axioms advance_master

/-- The export `seed`, called on a seed `s`, returns the state `s mod (2^31 - 1)`, or 1 when that
is 0, the state that the C++ standard's `linear_congruential_engine` with increment 0 sets for the
seed `s` ([rand.eng.lcong]). -/
theorem seed_master :
    Verified.Master compiled.module compiled.tables "seed" compiled.seed.bound (fun _ => True)
      (fun (s : UInt64) (y : UInt64) =>
        y.toNat = if s.toNat % 2147483647 = 0 then 1 else s.toNat % 2147483647) :=
  .of_trapFree (.ofA compiled.seed.trapFree) nofun seed_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ s _ _ => by
      have hr : (s % 2147483647).toNat = s.toNat % 2147483647 := UInt64.toNat_mod _ _
      show (if s % 2147483647 = 0 then (1 : UInt64) else s % 2147483647).toNat = _
      by_cases h : s % 2147483647 = 0
      · have h' : s.toNat % 2147483647 = 0 := by
          rw [← hr, h]
          rfl
        rw [ite_eq_left h, ite_eq_left h']
        rfl
      · have h' : s.toNat % 2147483647 ≠ 0 := by
          rw [← hr]
          exact fun h' => h (UInt64.toNat_inj.mp (h'.trans rfl))
        rw [ite_eq_right h, ite_eq_right h', hr]

#print axioms seed_master

end Library.Random.ParkMiller
