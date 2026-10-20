import Verified.TailCorrect
import Verified.ContextAppend
import Verified.ContextHEq

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

def TailAfter.bindPrefixStep {Γ ps params : List Ty} {result : Ty}
    {env : Env Γ} {values : Env ps} {slots first : List Slot} {L0 L1 LB : Nat → Bool}
    {base stateBase resultBase : Nat} {modes : List Mode}
    {heap heap1 heap' : Heap} {store store1 store' : Store Unit}
    {s s1 s2 s' : Locals} {value : Sum (Env params) result.denote}
    {fresh : List (Nat × Nat)}
    (h0 : Holds env slots L0 base heap store s)
    (hStep : Step heap store (Holds.KeepDying env slots L0 L1 store s) heap1 store1 fresh)
    (hFrame : Frame base s s1) (hVars1 : Holds env slots L1 base heap1 store1 s1)
    (f2 : Frame base s1 s2) (hLength : first.length = ps.length)
    (aB : TailAfter (values.append env) (first ++ slots) LB modes stateBase resultBase
      heap1 store1 s2 value heap' store' s') (hState : stateBase ≤ base)
    (hNew : ∀ r, (∀ b ∈ fresh, regionsDisjoint r b) →
      ∀ (t : Ty) (x : Var ps t), (first.getD x.index default).mode = .owned →
      ∀ w, LocalsHold s2 (first.getD x.index default).loc t.types w → w.length = t.width →
      ∀ b ∈ t.blocks store1 w (values.get x), regionsDisjoint r b)
    (hLB : ∀ i, LB (ps.length + i) = true → L1 i = true)
    (hL1 : ∀ i, L1 i = true → L0 i = true) :
    TailAfter env slots L0 modes stateBase resultBase heap store s value heap' store' s' := by
  refine ⟨aB.words, hStep.trans aB.step fun r hr =>
    ⟨hr.mono fun _ hi _ => ⟨hi, rfl⟩, fun hFresh => ?_⟩,
    (hFrame.mono hState).trans ((f2.mono hState).trans aB.frame), aB.rep⟩
  have hr1 : Holds.KeepDying env slots L1 (fun _ => false) store1 s1 r :=
    Holds.KeepDying.transfer h0 hStep hFrame hL1 (fun _ hi _ => hi)
      (hr.mono fun i hi _ => ⟨hL1 i hi, rfl⟩)
  intro t x hx _ hm wx hwx hlx b hb
  rcases x.append_cases with ⟨x, rfl⟩ | ⟨x, rfl⟩
  · simp only [Var.prefix_index, slots_append_prefix x first slots hLength,
      Env.get_append_prefix] at hm hwx hb
    exact hNew r hFresh t x hm wx hwx hlx b hb
  · simp only [slots_append_suffix x first slots hLength,
      Env.get_append_suffix] at hm hwx hb
    have hx1 : L1 x.index = true := hLB x.index (by simpa using hx)
    exact hr1 t x hx1 rfl hm wx ((hVars1.hold_agree f2 hx1 hlx).mp hwx) hlx b hb

def TailAfter.ofHEq {Γ Δ params : List Ty} {result : Ty} {first : Env Γ} {second : Env Δ}
    (hΓ : Γ = Δ) (h : HEq first second) {slots : List Slot} {live : Nat → Bool}
    {modes : List Mode} {stateBase resultBase : Nat} {heap heap' : Heap}
    {store store' : Store Unit} {s s' : Locals} {value : Sum (Env params) result.denote}
    (after : TailAfter first slots live modes stateBase resultBase heap store s
      value heap' store' s') :
    TailAfter second slots live modes stateBase resultBase heap store s value heap' store' s' := by
  cases hΓ
  cases h
  exact after

#print axioms TailAfter.bindPrefixStep
#print axioms TailAfter.ofHEq

end Verified
