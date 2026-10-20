import Verified.FieldsAfter

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem FieldsAfter.advance {Γ ps : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 live : Nat → Bool} {base : Nat} {heap heap1 heap2 : Heap}
    {store store1 store2 : Store Unit} {s s1 s2 : Locals} {values : Env ps}
    {words : List Value} {fresh : List (Nat × Nat)}
    (h0 : Holds env slots L0 base heap store s)
    (a : FieldsAfter env slots L0 L1 base heap store s values heap1 store1 s1 words)
    (hStep : Step heap1 store1 (Holds.KeepDying env slots L1 live store1 s1)
      heap2 store2 fresh)
    (hFrame : Frame base s1 s2) (hHolds : Holds env slots live base heap2 store2 s2)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hLive : ∀ i, live i = true → L1 i = true) :
    FieldsAfter env slots L0 live base heap store s values heap2 store2 s2 words ∧
      Step heap store (Holds.KeepDying env slots L0 live store s) heap2 store2
        (values.blocks store2 words ++ fresh) ∧
      values.blocks store2 words = values.blocks store1 words ∧
      ∀ b ∈ values.blocks store1 words, ∀ c ∈ fresh, regionsDisjoint b c := by
  have hKeep : ∀ b ∈ values.blocks store1 words,
      Holds.KeepDying env slots L1 live store1 s1 b := by
    intro b hb t x hx _ hm ws hold length c hc
    exact a.apart t x hx ws hold length b hb c (by rw [hm]; exact hc)
  obtain ⟨hRep, hSame, hFresh⟩ := a.rep.stepOwned hStep hKeep
  have hBoth := a.step.transBoth (keep := Holds.KeepDying env slots L0 live store s) hStep
    fun c hc =>
    ⟨hc.mono fun i h1 h2 => ⟨h1, by
        cases hl : live i with
        | false => rfl
        | true => rw [hLive i hl] at h2; exact nomatch h2⟩,
      fun _ => Holds.KeepDying.transfer h0 a.step a.frame hL1
        (fun i h1 _ => h1) (hc.mono fun i h1 h2 => ⟨hL1 _ h1, h2⟩)⟩
  rw [← hSame] at hBoth
  refine ⟨⟨hBoth.mono (fun _ hr => hr) (fun _ hb => List.mem_append_left _ hb),
    a.frame.trans hFrame, hHolds, hRep, by rw [hSame]; exact a.pairwise, ?_⟩,
    hBoth, hSame, hFresh⟩
  intro t x hx ws hold length b hb c hc
  have hold1 := (a.holds.hold_agree hFrame (hLive _ hx) length).mp hold
  obtain ⟨hRegions, _⟩ := a.holds.regions_after hStep (hLive _ hx) hold1 length
    (fun r hr => a.holds.keepDying hLive hx hold1 length r hr)
  rw [hRegions] at hc
  rw [hSame] at hb
  exact a.apart t x (hLive _ hx) ws hold1 length b hb c hc

end Verified
