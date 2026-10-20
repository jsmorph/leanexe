import Verified.VarCorrect
import Verified.TreeAllocate

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

def treeParentCode {Γ : List Ty} (shape : TreeShape)
    (reuse : Option (Var Γ (.treeHeader shape))) (slots : List Slot) (base : Nat)
    (live : Nat → Bool) : Program :=
  match reuse with
  | none => treeCopyAllocate shape base
  | some x =>
    if (slots.getD x.index default).mode = .owned ∧ live x.index = false then
      [.localGet (slots.getD x.index default).loc, .localSet base]
    else treeCopyAllocate shape base

def treeParentCost {Γ : List Ty} (shape : TreeShape)
    (reuse : Option (Var Γ (.treeHeader shape))) (slots : List Slot) (live : Nat → Bool) : Nat :=
  match reuse with
  | none => allocCost (8 * shape.fields.length)
  | some x =>
    if (slots.getD x.index default).mode = .owned ∧ live x.index = false then 0
    else allocCost (8 * shape.fields.length)

theorem wp_treeParent {Γ : List Ty} {env : Env Γ} {slots : List Slot} {shape : TreeShape}
    (reuse : Option (Var Γ (.treeHeader shape))) {live : Nat → Bool} {base : Nat}
    {heap : Heap} {store : Store Unit} {s : Locals} {m : Module} {host : HostEnv Unit}
    {rest : Program} {Q : Assertion Unit} (hm : Runtime m)
    (hVars : Holds env slots (fun i => live i || optionVarUses reuse i) base heap store s)
    (hAt : heap.At store) (hCap : store.memoryCap m 0 ≤ 65535)
    (hLow : s.params.length ≤ base) (hHigh : base < s.positions)
    (hTrap : TrapOK (!decide (heap.Within store m (treeParentCost shape reuse slots live))) Q)
    (hNext : ∀ heap' store' s' p,
      Step heap store (Holds.KeepDying env slots (fun i => live i || optionVarUses reuse i)
        live store s) heap' store' [block store' p] →
      Frame base s s' → Holds env slots live base heap' store' s' →
      RecordStorage shape heap' store' p → store'.mem.read64 (p - 40).toUInt32 = 1 →
      s'.get base = some (.i64 p) → s'.values = s.values →
      (∀ j, j ≠ base → s'.get j = s.get j) →
      Holds.Apart env slots live store' s' (.treeHeader shape) .owned [.i64 p] .unit →
      heap'.top.toNat ≤ heap.top.toNat + treeParentCost shape reuse slots live →
      wp m rest Q store' s' host) :
    wp m (treeParentCode shape reuse slots base live ++ rest) Q store s host := by
  have hLive : ∀ i, live i = true → (live i || optionVarUses reuse i) = true := by
    intro i hi
    simp only [hi, Bool.true_or]
  have hAllocate (hc : treeParentCost shape reuse slots live =
      allocCost (8 * shape.fields.length)) :
      wp m (treeCopyAllocate shape base ++ rest) Q store s host := by
    refine wp_treeCopyAllocate hm hAt hCap (by simpa only [hc] using hTrap)
      hLow (Locals.lt_total hHigh) fun heap' store' p hStep hRaw hCount hTop => ?_
    have hFrame := Frame.set (v := Value.i64 p) hLow (le_refl base) hHigh
    have hLiveVars := hVars.live_mono hLive
    refine hNext heap' store' (setLocal s base (.i64 p)) p
      (hStep.mono (fun _ _ => trivial) (fun _ hb => hb)) hFrame
      ((hLiveVars.step hStep (fun _ _ _ _ _ _ _ _ => trivial)).agree hFrame)
      hRaw hCount (Locals.get_setLocal_same hLow (Locals.lt_total hHigh)) rfl
      (fun _ hj => Locals.get_setLocal_ne hLow hj) ?_ (by rw [hc]; exact hTop)
    intro t x hx _ wx hold length b hb c hc
    have hb' : b = block store' p := by
      simpa only [Ty.regions, Ty.blocks, List.mem_singleton] using hb
    subst b
    have hold0 := (hLiveVars.hold_agree hFrame hx length).mp hold
    obtain ⟨hRegions, hFresh⟩ := hLiveVars.regions_after hStep hx hold0 length (fun _ _ => trivial)
    rw [hRegions] at hc
    exact regionsDisjoint_symm (hFresh c hc (block store' p) (by simp))
  cases reuse with
  | none => exact hAllocate rfl
  | some x =>
    by_cases hReuse : (slots.getD x.index default).mode = .owned ∧ live x.index = false
    · obtain ⟨hOwned, hDead⟩ := hReuse
      have hx : (live x.index || optionVarUses (some x) x.index) = true := by
        simp [optionVarUses]
      obtain ⟨_, ws, hold, hRep⟩ := hVars.get x hx
      rw [hOwned] at hRep
      obtain ⟨p, rfl, hHeader⟩ := hRep
      obtain ⟨payload, hLength, hHead, _⟩ := hHeader
      have hRaw := RecordStorage.ofHeader hHead (by simpa only [List.length_map] using hLength)
      have hPtr := hold.word
      have hFrame := Frame.set (v := Value.i64 p) hLow (le_refl base) hHigh
      have hStep : Step heap store
          (Holds.KeepDying env slots (fun i => live i || optionVarUses (some x) i) live store s)
          heap store [block store p] := by
        refine ⟨hAt, rfl, fun r hr _ hk => ⟨fun _ _ _ => rfl, hr, ?_⟩⟩
        intro b hb
        simp only [List.mem_singleton] at hb
        subst b
        exact hk (.treeHeader shape) x hx hDead hOwned [.i64 p] hold rfl (block store p)
          (by simp [Ty.blocks])
      have hApart : Holds.Apart env slots live store (setLocal s base (.i64 p))
          (.treeHeader shape) .owned [.i64 p] .unit := by
        intro t y hy _ wy hwy length b hb c hc
        have hb' : b = block store p := by
          simpa only [Ty.regions, Ty.blocks, List.mem_singleton] using hb
        subst b
        have hwy0 := ((hVars.live_mono hLive).hold_agree hFrame hy length).mp hwy
        have hNe : x.index ≠ y.index := fun he => by rw [he, hy] at hDead; exact nomatch hDead
        exact hVars.2 (.treeHeader shape) t x y hx (hLive _ hy) hNe hOwned [.i64 p] wy hold rfl
          hwy0 length (block store p) (by simp [Ty.blocks]) c hc
      simp only [treeParentCode, hOwned, hDead, and_self, ↓reduceIte, List.cons_append,
        List.nil_append, wp_localGet_cons, hPtr]
      refine wp_localSet_local hLow (Locals.lt_total hHigh) ?_
      exact hNext heap store (setLocal s base (.i64 p)) p hStep hFrame
        ((hVars.live_mono hLive).agree hFrame) hRaw hHead.count
        (Locals.get_setLocal_same hLow (Locals.lt_total hHigh)) rfl
        (fun _ hj => Locals.get_setLocal_ne hLow hj) hApart
        (by simp [treeParentCost, hOwned, hDead])
    · simpa only [treeParentCode, hReuse, ↓reduceIte] using
        hAllocate (by simp only [treeParentCost, hReuse, ↓reduceIte])

end Verified
