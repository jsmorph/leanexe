import Verified.After
import Verified.OwnedValues

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

structure FieldsAfter {Γ ps : List Ty} (env : Env Γ) (slots : List Slot)
    (liveIn live : Nat → Bool) (base : Nat) (heap : Heap) (store : Store Unit) (s : Locals)
    (values : Env ps) (heap' : Heap) (store' : Store Unit) (s' : Locals)
    (words : List Value) : Prop where
  step : Step heap store (Holds.KeepDying env slots liveIn live store s) heap' store'
    (values.blocks store' words)
  frame : Frame base s s'
  holds : Holds env slots live base heap' store' s'
  rep : Env.Rep (fun _ => .owned) heap' store' words values
  pairwise : (values.blocks store' words).Pairwise regionsDisjoint
  apart : ∀ (t : Ty) (x : Var Γ t), live x.index = true → ∀ ws,
    LocalsHold s' (slots.getD x.index default).loc t.types ws → ws.length = t.width →
    ∀ b ∈ values.blocks store' words,
    ∀ c ∈ t.regions (slots.getD x.index default).mode store' ws (env.get x), regionsDisjoint b c

theorem FieldsAfter.nil {Γ : List Ty} {env : Env Γ} {slots : List Slot} {live : Nat → Bool}
    {base : Nat} {heap : Heap} {store : Store Unit} {s : Locals}
    (hAt : heap.At store) (hVars : Holds env slots live base heap store s) :
    FieldsAfter env slots live live base heap store s Env.nil heap store s [] :=
  ⟨Step.refl hAt _, Frame.refl base s, hVars, rfl, List.Pairwise.nil,
    fun _ _ _ _ _ _ _ h => nomatch h⟩

theorem FieldsAfter.reframe {Γ ps : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 live : Nat → Bool} {base : Nat} {heap heap' : Heap} {store store' : Store Unit}
    {s s' s'' : Locals} {values : Env ps} {words : List Value}
    (a : FieldsAfter env slots L0 live base heap store s values heap' store' s' words)
    (hFrame : Frame base s' s'') :
    FieldsAfter env slots L0 live base heap store s values heap' store' s'' words :=
  ⟨a.step, a.frame.trans hFrame, a.holds.agree hFrame, a.rep, a.pairwise,
    fun t x hx ws hold length b hb c hc =>
      a.apart t x hx ws ((a.holds.hold_agree hFrame hx length).mp hold) length b hb c hc⟩

theorem FieldsAfter.prepend {Γ ps : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 live : Nat → Bool} {base : Nat} {heap heap1 heap2 : Heap}
    {store store1 store2 : Store Unit} {s s1 s2 : Locals} {t : Ty} {value : t.denote}
    {values : Env ps} {first words vs : List Value}
    (h0 : Holds env slots L0 base heap store s)
    (a1 : After env slots L0 L1 base heap store s t .owned value heap1 store1 s1 first)
    (a2 : FieldsAfter env slots L1 live base heap1 store1 { s1 with values := vs }
      values heap2 store2 s2 words)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hLive : ∀ i, live i = true → L1 i = true) :
    FieldsAfter env slots L0 live base heap store s (Env.cons value values)
      heap2 store2 s2 (first ++ words) := by
  have hKeep1 : ∀ c ∈ t.blocks store1 first value,
      Holds.KeepDying env slots L1 live store1 { s1 with values := vs } c := by
    intro c hc u x hx _ hm wx hwx hlx b hb
    have hb' : b ∈ u.regions (slots.getD x.index default).mode store1 wx (env.get x) := by
      rw [hm]; exact hb
    exact a1.apart u x hx (Or.inl rfl) wx hwx hlx c hc b hb'
  obtain ⟨hRep1, hSame1, hFresh1⟩ := a1.rep.step a2.step hKeep1
  have hSame : t.blocks store2 first value = t.blocks store1 first value := hSame1
  have hStep := a1.step.transBoth (keep := Holds.KeepDying env slots L0 live store s) a2.step
    fun c hc =>
    ⟨hc.mono fun i h1 h2 => ⟨h1, by
        cases hl : live i with
        | false => rfl
        | true => rw [hLive i hl] at h2; exact nomatch h2⟩,
      fun _ => Holds.KeepDying.transfer h0 a1.step a1.frame hL1
        (fun i h1 _ => h1) (hc.mono fun i h1 h2 => ⟨hL1 _ h1, h2⟩)⟩
  have hApart1 := (a1.apart.live_mono hLive).transfer (a1.holds.live_mono hLive) a2.step
    a2.frame.values
    (fun u y hy wy hwy hly c hc => a1.holds.keepDying hLive hy hwy hly c hc) hSame1
  refine ⟨?_, a1.frame.trans a2.frame.values, a2.holds,
    ⟨first, words, rfl, hRep1, a2.rep⟩, ?_, ?_⟩
  · rw [Env.blocks_cons a1.rep.length, hSame]
    exact hStep
  · rw [Env.blocks_cons a1.rep.length]
    exact List.pairwise_append.mpr ⟨hRep1.pairwise, a2.pairwise, fun b hb c hc => by
      rw [hSame] at hb
      exact hFresh1 b hb c hc⟩
  · intro u x hx wx hwx hlx b hb c hc
    rw [Env.blocks_cons a1.rep.length] at hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hApart1 u x hx (Or.inl rfl) wx hwx hlx b hb c hc
    · exact a2.apart u x hx wx hwx hlx b hb c hc

end Verified
