import Verified.ContextAppend

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem After.bindPrefixStep {Γ ps : List Ty} {env : Env Γ} {values : Env ps}
    {slots first : List Slot} {L0 L1 LB live : Nat → Bool} {base base' : Nat}
    {heap heap1 heap' : Heap} {store store1 store' : Store Unit}
    {s s1 s2 s' : Locals} {u : Ty} {mode : Mode} {v : u.denote}
    {ws : List Value} {fresh : List (Nat × Nat)}
    (h0 : Holds env slots L0 base heap store s)
    (hStep : Step heap store (Holds.KeepDying env slots L0 L1 store s) heap1 store1 fresh)
    (hFrame : Frame base s s1) (hVars1 : Holds env slots L1 base heap1 store1 s1)
    (f2 : Frame base s1 s2) (hLength : first.length = ps.length)
    (aB : After (values.append env) (first ++ slots) LB (shift ps.length live) base'
      heap1 store1 s2 u mode v heap' store' s' ws) (hBase : base ≤ base')
    (hNew : ∀ r, (∀ b ∈ fresh, regionsDisjoint r b) →
      ∀ (t : Ty) (x : Var ps t), (first.getD x.index default).mode = .owned →
      ∀ w, LocalsHold s2 (first.getD x.index default).loc t.types w → w.length = t.width →
      ∀ b ∈ t.blocks store1 w (values.get x), regionsDisjoint r b)
    (hLB : ∀ i, LB (ps.length + i) = true → L1 i = true)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hLive : ∀ i, live i = true → L1 i = true) :
    After env slots L0 live base heap store s u mode v heap' store' s' ws := by
  refine ⟨hStep.trans aB.step fun r hr => ⟨hr.mono fun i h1 h2 => ⟨h1, ?_⟩, fun hFresh => ?_⟩,
    hFrame.trans (f2.trans (aB.frame.mono hBase)), ?_, aB.rep, ?_⟩
  · cases hl : live i with
    | false => rfl
    | true => rw [hLive i hl] at h2; exact nomatch h2
  · have hr1 : Holds.KeepDying env slots L1 live store1 s1 r :=
      Holds.KeepDying.transfer h0 hStep hFrame hL1
        (fun i h1 _ => h1) (hr.mono fun i h1 h2 => ⟨hL1 _ h1, h2⟩)
    intro t x hx hxo hm wx hwx hlx b hb
    rcases x.append_cases with ⟨x, rfl⟩ | ⟨x, rfl⟩
    · simp only [Var.prefix_index, slots_append_prefix x first slots hLength,
        Env.get_append_prefix] at hm hwx hb
      exact hNew r hFresh t x hm wx hwx hlx b hb
    · simp only [slots_append_suffix x first slots hLength,
        Env.get_append_suffix] at hm hwx hb
      have hx1 : L1 x.index = true := hLB x.index (by simpa using hx)
      have hxo' : live x.index = false := by simpa [shift] using hxo
      exact hr1 t x hx1 hxo' hm wx
        ((hVars1.hold_agree f2 hx1 hlx).mp hwx) hlx b hb
  · exact ((aB.holds.popPrefix hLength).live_mono fun i h => by
      simpa [shift] using h).lower h0 fun i h => hL1 _ (hLive _ h)
  · exact (aB.apart.popPrefix hLength).live_mono fun i h => by simpa [shift] using h

theorem After.bindPrefix {Γ ps : List Ty} {env : Env Γ} {values : Env ps}
    {slots first : List Slot} {L0 L1 LB live : Nat → Bool} {base base' : Nat}
    {heap heap1 heap' : Heap} {store store1 store' : Store Unit}
    {s s1 s2 s' : Locals} {tv u : Ty} {mv mode : Mode} {vv : tv.denote} {v : u.denote}
    {wsv ws : List Value}
    (h0 : Holds env slots L0 base heap store s)
    (a1 : After env slots L0 L1 base heap store s tv mv vv heap1 store1 s1 wsv)
    (f2 : Frame base s1 s2) (hLength : first.length = ps.length)
    (aB : After (values.append env) (first ++ slots) LB (shift ps.length live) base'
      heap1 store1 s2 u mode v heap' store' s' ws) (hBase : base ≤ base')
    (hNew : ∀ r, (∀ b ∈ mv.fresh store1 tv wsv vv, regionsDisjoint r b) →
      ∀ (t : Ty) (x : Var ps t), (first.getD x.index default).mode = .owned →
      ∀ w, LocalsHold s2 (first.getD x.index default).loc t.types w → w.length = t.width →
      ∀ b ∈ t.blocks store1 w (values.get x), regionsDisjoint r b)
    (hLB : ∀ i, LB (ps.length + i) = true → L1 i = true)
    (hL1 : ∀ i, L1 i = true → L0 i = true) (hLive : ∀ i, live i = true → L1 i = true) :
    After env slots L0 live base heap store s u mode v heap' store' s' ws :=
  After.bindPrefixStep h0 a1.step a1.frame a1.holds f2 hLength aB hBase hNew hLB hL1 hLive

end Verified
