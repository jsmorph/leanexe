import Verified.TailCode

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem Env.Rep.keepDying {Γ : List Ty} {modes : List Mode} {heap : Heap}
    {store : Store Unit} {ws : List Value} {env : Env Γ} {s : Locals} {base : Nat}
    {live : Nat → Bool} (hRep : Env.Rep (paramMode Γ modes) heap store ws env)
    (hold : LocalsHold s base (Γ.flatMap Ty.types) ws) {r : Nat × Nat}
    (hApart : Apart store (Env.moves store (paramMode Γ modes) ws env) r) :
    Holds.KeepDying env (paramSlots Γ modes base) live (fun _ => false) store s r := by
  intro t x _ _ hxMode wx hxHold hxLength b hb
  rw [paramSlots_getD x] at hxMode hxHold
  obtain rfl := LocalsHold.unique hxHold (hold.var x)
    (hxLength.trans (hRep.var x).length.symm)
  rw [Ty.blocks_pointers] at hb
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
  exact hApart q (Env.moves_var x hRep hxMode q hq)

theorem TailAfter.chain {Γ params : List Ty} {result : Ty} {env : Env Γ}
    {sourceModes targetModes : List Mode} {base stateBase resultBase : Nat}
    {heap0 heap heap' : Heap} {store0 store store' : Store Unit} {s s' : Locals}
    {ws : List Value} {value : Sum (Env params) result.denote} {keep : Nat × Nat → Prop}
    (before : Step heap0 store0 keep heap store
      ((Env.moves store (paramMode Γ sourceModes) ws env).map (block store)))
    (rep : Env.Rep (paramMode Γ sourceModes) heap store ws env)
    (hold : LocalsHold s base (Γ.flatMap Ty.types) ws)
    (after : TailAfter env (paramSlots Γ sourceModes base) (fun _ => true) targetModes
      stateBase resultBase heap store s value heap' store' s') :
    Step heap0 store0 keep heap' store' (tailFresh targetModes store' after.words value) := by
  refine before.trans after.step fun r hr => ⟨hr, fun hf => ?_⟩
  exact rep.keepDying hold fun q hq => hf (block store q) (List.mem_map.mpr ⟨q, hq, rfl⟩)

#print axioms Env.Rep.keepDying
#print axioms TailAfter.chain

end Verified
