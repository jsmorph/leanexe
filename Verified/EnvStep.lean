import Verified.Potential

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem Env.Rep.step {heap heap' : Heap} {store store' : Store Unit}
    {keep : Nat × Nat → Prop} {fresh : List (Nat × Nat)}
    (step : Step heap store keep heap' store' fresh)
    {Γ : List Ty} (env : Env Γ) (modes : Nat → Mode) (ws : List Value)
    (rep : Env.Rep modes heap store ws env)
    (owned : ∀ q ∈ Env.moves store modes ws env, keep (block store q))
    (borrowed : ∀ r ∈ Env.reads store modes ws env, keep r) :
    Env.Rep modes heap' store' ws env ∧
      (∀ q ∈ Env.moves store modes ws env, block store' q = block store q) ∧
      Env.moves store' modes ws env = Env.moves store modes ws env ∧
      Env.reads store' modes ws env = Env.reads store modes ws env := by
  induction env generalizing modes ws with
  | nil => exact ⟨rep, nofun, rfl, rfl⟩
  | @cons Γ t value env ih =>
    obtain ⟨first, rest, rfl, head, tail⟩ := rep
    have keepHead : ∀ r ∈ t.regions (modes 0) store first value, keep r := by
      intro r hr
      cases hm : modes 0 with
      | borrowed =>
        have hr' : r ∈ t.reads store first value := by simpa [Ty.regions, hm] using hr
        exact borrowed r (by rw [Env.reads_cons head.length, hm]; exact List.mem_append_left _ hr')
      | owned =>
        have hr' : r ∈ (t.pointers store first value).map (block store) := by
          simpa [Ty.regions, hm, Ty.blocks_pointers] using hr
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr'
        exact owned q (by rw [Env.moves_cons head.length, hm]; exact List.mem_append_left _ hq)
    obtain ⟨head', same, -⟩ := head.step step keepHead
    obtain ⟨tail', sameTail, movesTail, readsTail⟩ := ih (fun i => modes (i + 1)) rest tail
      (fun q hq => owned q (by rw [Env.moves_cons head.length]; exact List.mem_append_right _ hq))
      (fun r hr => borrowed r (by rw [Env.reads_cons head.length]; exact List.mem_append_right _ hr))
    have pointers (hm : modes 0 = .owned) :
        t.pointers store' first value = t.pointers store first value := by
      have hOwned : t.Rep .owned heap store first value := by rw [← hm]; exact head
      exact hOwned.pointers_step step (by simpa only [Ty.regions, hm] using keepHead)
    refine ⟨⟨first, rest, rfl, head', tail'⟩, ?_, ?_, ?_⟩
    · intro q hq
      rw [Env.moves_cons head.length] at hq
      rcases List.mem_append.mp hq with hq | hq
      · cases hm : modes 0 with
        | borrowed => rw [hm] at hq; exact nomatch hq
        | owned =>
          rw [hm] at hq
          have eq : (t.pointers store first value).map (block store') =
              (t.pointers store first value).map (block store) := by
            simpa only [Ty.regions, hm, Ty.blocks_pointers, pointers hm] using same
          exact List.map_inj_left.mp eq q hq
      · exact sameTail q hq
    · rw [Env.moves_cons head.length, Env.moves_cons head.length, movesTail]
      congr 1
      cases hm : modes 0
      · rfl
      · exact pointers hm
    · rw [Env.reads_cons head.length, Env.reads_cons head.length, readsTail]
      congr 1
      cases hm : modes 0
      · simpa only [Ty.regions, hm] using same
      · rfl

theorem Separate.of_block_eq {store store' : Store Unit} {owned : List UInt64}
    {borrowed : List (Nat × Nat)} (separate : Separate store owned borrowed)
    (same : ∀ q ∈ owned, block store' q = block store q) : Separate store' owned borrowed := by
  have mapped : owned.map (block store') = owned.map (block store) :=
    List.map_congr_left same
  refine ⟨?_, fun r hr q hq => ?_⟩
  · change (owned.map (block store')).Pairwise regionsDisjoint
    rw [mapped]
    exact separate.1
  · rw [same q hq]
    exact separate.2 r hr q hq

theorem Ty.pot_of_pointerBlocks {store store' : Store Unit} :
    (t : Ty) → (ws : List Value) → (value : t.denote) →
      (∀ q ∈ t.pointers store ws value, block store' q = block store q) →
      t.pot store' ws value = t.pot store ws value
  | .elem _, _, _, _ | .tree _, _, _, _ | .treeHeader _ _, _, _, _ => rfl
  | .pair a b, ws, value, same => by
    simp only [Ty.pot]
    congr 1
    · exact a.pot_of_pointerBlocks _ _ fun q hq => same q (List.mem_append_left _ hq)
    · exact b.pot_of_pointerBlocks _ _ fun q hq => same q (List.mem_append_right _ hq)
  | .array _, ws, _, same => by
    simp only [Ty.pointers] at same
    simp only [Ty.pot]
    split
    · rename_i ptr
      have hc := same ptr (List.mem_singleton_self _)
      simp only [block, Prod.mk.injEq] at hc
      simp only [arrayPot]
      omega
    · rfl

theorem Env.argPot_of_blocks {heap : Heap} {store store' : Store Unit}
    {Γ : List Ty} (env : Env Γ) (modes : Nat → Mode) (ws : List Value)
    (rep : Env.Rep modes heap store ws env)
    (same : ∀ q ∈ Env.moves store modes ws env, block store' q = block store q)
    (sel : Nat → Bool) (owned : ∀ i, sel i = true → modes i = .owned) :
    Env.argPot store' sel ws env = Env.argPot store sel ws env := by
  induction env generalizing modes ws sel with
  | nil => rfl
  | @cons Γ t value env ih =>
    obtain ⟨first, rest, rfl, head, tail⟩ := rep
    have sameTail : ∀ q ∈ Env.moves store (fun i => modes (i + 1)) rest env,
        block store' q = block store q :=
      fun q hq => same q (by rw [Env.moves_cons head.length]; exact List.mem_append_right _ hq)
    have tailEq := ih (fun i => modes (i + 1)) rest tail sameTail (fun i => sel (i + 1))
      (fun i hi => owned (i + 1) hi)
    simp only [Env.argPot, List.take_left' head.length, List.drop_left' head.length, tailEq]
    congr 1
    split
    · next hs =>
      apply Ty.pot_of_pointerBlocks t first value
      exact fun q hq =>
        same q (by rw [Env.moves_cons head.length, owned 0 hs]; exact List.mem_append_left _ hq)
    · rfl

#print axioms Env.Rep.step
#print axioms Separate.of_block_eq
#print axioms Env.argPot_of_blocks

end Verified
