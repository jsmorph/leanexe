import Verified.State

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

def Env.blocks (store : Store Unit) : {Γ : List Ty} → List Value → Env Γ → List (Nat × Nat)
  | _, _, .nil => []
  | _, ws, .cons (t := t) value env =>
    t.blocks store (ws.take t.width) value ++ env.blocks store (ws.drop t.width)

theorem Env.blocks_cons {store : Store Unit} {t : Ty} {Γ : List Ty} {value : t.denote}
    {env : Env Γ} {first rest : List Value} (h : first.length = t.width) :
    (Env.cons value env).blocks store (first ++ rest) =
      t.blocks store first value ++ env.blocks store rest := by
  simp only [Env.blocks, List.take_left' h, List.drop_left' h]

theorem Env.Rep.stepOwned {heap heap' : Heap} {store store' : Store Unit}
    {keep : Nat × Nat → Prop} {fresh : List (Nat × Nat)}
    (hStep : Step heap store keep heap' store' fresh) :
    {Γ : List Ty} → {ws : List Value} → {env : Env Γ} →
      Env.Rep (fun _ => .owned) heap store ws env →
      (∀ r ∈ env.blocks store ws, keep r) →
      Env.Rep (fun _ => .owned) heap' store' ws env ∧
        env.blocks store' ws = env.blocks store ws ∧
        ∀ r ∈ env.blocks store ws, ∀ b ∈ fresh, regionsDisjoint r b
  | _, _, .nil, hRep, _ => ⟨hRep, rfl, nofun⟩
  | _, _, .cons value env, hRep, hKeep => by
    obtain ⟨first, rest, rfl, hFirst, hRest⟩ := hRep
    rw [Env.blocks_cons hFirst.length] at hKeep
    obtain ⟨hFirst', hSame1, hApart1⟩ := hFirst.step hStep
      (fun r hr => hKeep r (List.mem_append_left _ hr))
    obtain ⟨hRest', hSame2, hApart2⟩ := Env.Rep.stepOwned hStep hRest
      (fun r hr => hKeep r (List.mem_append_right _ hr))
    refine ⟨⟨first, rest, rfl, hFirst', hRest'⟩, ?_, ?_⟩
    · rw [Env.blocks_cons hFirst.length, Env.blocks_cons hFirst.length]
      exact congrArg₂ List.append hSame1 hSame2
    · rw [Env.blocks_cons hFirst.length]
      intro r hr b hb
      rcases List.mem_append.mp hr with hr | hr
      · exact hApart1 r hr b hb
      · exact hApart2 r hr b hb

end Verified
