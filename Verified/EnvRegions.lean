import Verified.After

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem Env.Rep.regions_var {heap : Heap} {store : Store Unit} {Γ : List Ty} {t : Ty}
    {env : Env Γ} {modes : Nat → Mode} {ws : List Value}
    (hRep : Env.Rep modes heap store ws env) (x : Var Γ t) :
    ∀ r ∈ t.regions (modes x.index) store ((ws.drop x.offset).take t.width) (env.get x),
      r ∈ (Env.moves store modes ws env).map (block store) ++ Env.reads store modes ws env := by
  intro r hr
  cases hm : modes x.index
  · rw [hm] at hr
    change r ∈ t.reads store ((ws.drop x.offset).take t.width) (env.get x) at hr
    exact List.mem_append_right _ (Env.reads_var x hRep hm r hr)
  · rw [hm] at hr
    change r ∈ t.blocks store ((ws.drop x.offset).take t.width) (env.get x) at hr
    rw [Ty.blocks_pointers] at hr
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    exact List.mem_append_left _ (List.mem_map.mpr ⟨p, Env.moves_var x hRep hm p hp, rfl⟩)

end Verified
