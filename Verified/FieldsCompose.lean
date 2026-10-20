import Verified.FieldsAfter

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

def Env.append {qs : List Ty} : {ps : List Ty} → Env ps → Env qs → Env (ps ++ qs)
  | _, .nil, tail => tail
  | _, .cons value values, tail => .cons value (values.append tail)

theorem Env.Rep.appendOwned {heap : Heap} {store : Store Unit} {ps qs : List Ty}
    {values : Env ps} {tail : Env qs} {first rest : List Value}
    (h : Env.Rep (fun _ => .owned) heap store first values)
    (hTail : Env.Rep (fun _ => .owned) heap store rest tail) :
    Env.Rep (fun _ => .owned) heap store (first ++ rest) (values.append tail) := by
  induction values generalizing first with
  | nil =>
    have he : first = [] := h
    subst he
    exact hTail
  | cons value values ih =>
    obtain ⟨ws, vs, rfl, hFirst, hRest⟩ := h
    exact ⟨ws, vs ++ rest, by simp only [List.append_assoc], hFirst, ih hRest⟩

theorem Env.blocks_append {heap : Heap} {store : Store Unit} {ps qs : List Ty}
    {values : Env ps} {tail : Env qs} {first rest : List Value}
    (h : Env.Rep (fun _ => .owned) heap store first values) :
    (values.append tail).blocks store (first ++ rest) =
      values.blocks store first ++ tail.blocks store rest := by
  induction values generalizing first with
  | nil =>
    have he : first = [] := h
    subst he
    rfl
  | cons value values ih =>
    obtain ⟨ws, vs, rfl, hFirst, hRest⟩ := h
    change (Env.cons value (values.append tail)).blocks store ((ws ++ vs) ++ rest) = _
    rw [List.append_assoc, Env.blocks_cons hFirst.length, Env.blocks_cons hFirst.length,
      ih hRest, List.append_assoc]

theorem FieldsAfter.append {Γ ps qs : List Ty} {env : Env Γ} {slots : List Slot}
    {L0 L1 live : Nat → Bool} {base : Nat} {heap heap1 heap2 : Heap}
    {store store1 store2 : Store Unit} {s s1 s2 : Locals}
    {values : Env ps} {tail : Env qs} {first rest vs : List Value}
    (h0 : Holds env slots L0 base heap store s)
    (a1 : FieldsAfter env slots L0 L1 base heap store s values heap1 store1 s1 first)
    (a2 : FieldsAfter env slots L1 live base heap1 store1 { s1 with values := vs }
      tail heap2 store2 s2 rest)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hLive : ∀ i, live i = true → L1 i = true) :
    FieldsAfter env slots L0 live base heap store s (values.append tail)
      heap2 store2 s2 (first ++ rest) := by
  have hKeep : ∀ b ∈ values.blocks store1 first,
      Holds.KeepDying env slots L1 live store1 { s1 with values := vs } b := by
    intro b hb t x hx _ hm ws hold length c hc
    exact a1.apart t x hx ws hold length b hb c (by rw [hm]; exact hc)
  obtain ⟨hRep, hSame, hFresh⟩ := a1.rep.stepOwned a2.step hKeep
  have hStep := a1.step.transBoth (keep := Holds.KeepDying env slots L0 live store s) a2.step
    fun c hc =>
    ⟨hc.mono fun i h1 h2 => ⟨h1, by
        cases hl : live i with
        | false => rfl
        | true => rw [hLive i hl] at h2; exact nomatch h2⟩,
      fun _ => Holds.KeepDying.transfer h0 a1.step a1.frame hL1
        (fun i h1 _ => h1) (hc.mono fun i h1 h2 => ⟨hL1 _ h1, h2⟩)⟩
  refine ⟨?_, a1.frame.trans a2.frame.values, a2.holds, hRep.appendOwned a2.rep, ?_, ?_⟩
  · rw [Env.blocks_append hRep, hSame]
    exact hStep
  · rw [Env.blocks_append hRep]
    exact List.pairwise_append.mpr ⟨by rw [hSame]; exact a1.pairwise, a2.pairwise,
      fun b hb c hc => hFresh b (by rwa [hSame] at hb) c hc⟩
  · intro t x hx ws hold length b hb c hc
    rw [Env.blocks_append hRep] at hb
    rcases List.mem_append.mp hb with hb | hb
    · have hold1 := (a1.holds.hold_agree a2.frame.values (hLive _ hx) length).mp hold
      obtain ⟨hRegions, _⟩ := a1.holds.regions_after a2.step (hLive _ hx) hold1 length
        (fun r hr => a1.holds.keepDying hLive hx hold1 length r hr)
      rw [hRegions] at hc
      rw [hSame] at hb
      exact a1.apart t x (hLive _ hx) ws hold1 length b hb c hc
    · exact a2.apart t x hx ws hold length b hb c hc

end Verified
